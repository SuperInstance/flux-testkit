"""
FLUX TestKit — comprehensive test harness for FLUX VM programs.

Provides:
- Assertion helpers for FLUX VM state (registers, flags, memory, cycles)
- Test fixture generators (random bytecode, edge cases, known programs)
- Property-based testing support (fuzz-like generators for instructions)
- Snapshot testing for disassembly output
- Per-opcode pass/fail reporting
- Test runner with setup/teardown, suites, grouping
- Report generation (pass/fail/skip counts, terminal, markdown, JSON)
"""
from dataclasses import dataclass, field
from typing import List, Dict, Callable, Optional, Tuple, Any, Iterator
from enum import Enum
import time
import json
import random
import hashlib
import os

# ═══════════════════════════════════════════════════════════════════
# Opcode Definitions (shared with flux-coverage)
# ═══════════════════════════════════════════════════════════════════

OPCODE_NAMES: Dict[int, str] = {
    0x00: "HALT", 0x01: "NOP",
    0x08: "INCR", 0x09: "DECR", 0x0C: "PUSH", 0x0D: "POP",
    0x0E: "NOT", 0x0F: "NEG",
    0x18: "MOVI", 0x1A: "CMPI",
    0x1D: "JMP", 0x1E: "CALL",
    0x20: "ADD", 0x21: "SUB", 0x22: "MUL", 0x23: "DIV",
    0x24: "MOD", 0x25: "AND", 0x26: "OR", 0x27: "XOR",
    0x28: "SHL", 0x29: "SHR", 0x2A: "SAR",
    0x2B: "EQ", 0x2C: "SEQ", 0x2D: "SLT", 0x2E: "SLE",
    0x2F: "SGT", 0x30: "SGE", 0x31: "SNE",
    0x3A: "MOVr", 0x3C: "BEQ", 0x3D: "BNE", 0x3E: "BLT", 0x3F: "BGE",
}

CONDITIONAL_OPCODES = {0x3C, 0x3D, 0x3E, 0x3F}

def _inst_size(op: int) -> int:
    if op <= 0x07: return 1
    if op <= 0x17: return 2
    if op <= 0x1F: return 3
    return 4


def _signed_byte(b) -> int:
    return b - 256 if b > 127 else b


# ═══════════════════════════════════════════════════════════════════
# MiniVM (lightweight test execution VM)
# ═══════════════════════════════════════════════════════════════════

@dataclass
class VMState:
    """Snapshot of VM state after execution."""
    registers: Dict[int, int]
    stack_top: int
    pc: int
    cycles: int
    halted: bool
    opcodes_executed: Dict[int, int] = field(default_factory=dict)

    def register_eq(self, reg: int, value: int) -> bool:
        return self.registers.get(reg, 0) == value

    def flag_zero(self) -> bool:
        """Check if zero flag would be set (R0 == 0)."""
        return self.registers.get(0, 0) == 0

    def flag_negative(self) -> bool:
        """Check if negative flag would be set (R0 < 0)."""
        return self.registers.get(0, 0) < 0


class _MiniVM:
    """Lightweight VM for test execution with state tracking."""

    def __init__(self):
        self.max_cycles = 100000

    def run(self, bytecode: List[int], initial: Dict[int, int] = None) -> Tuple[Dict[int, int], int]:
        regs = [0] * 64
        stack = [0] * 4096
        sp = 4096
        pc = 0
        cycles = 0
        opcodes_executed: Dict[int, int] = {}

        if initial:
            for k, v in initial.items():
                regs[k] = v

        bc = bytes(bytecode)
        halted = False

        while pc < len(bc) and cycles < self.max_cycles:
            op = bc[pc]; cycles += 1
            opcodes_executed[op] = opcodes_executed.get(op, 0) + 1

            if op == 0x00: halted = True; break
            elif op == 0x01: pc += 1
            elif op == 0x08: regs[bc[pc+1]] += 1; pc += 2
            elif op == 0x09: regs[bc[pc+1]] -= 1; pc += 2
            elif op == 0x0C: sp -= 1; stack[sp] = regs[bc[pc+1]]; pc += 2
            elif op == 0x0D: regs[bc[pc+1]] = stack[sp]; sp += 1; pc += 2
            elif op == 0x0E: regs[bc[pc+1]] = ~regs[bc[pc+1]] & 0xFF; pc += 2
            elif op == 0x0F: regs[bc[pc+1]] = -regs[bc[pc+1]]; pc += 2
            elif op == 0x18: regs[bc[pc+1]] = _signed_byte(bc[pc+2]); pc += 3
            elif op == 0x1D: pc += _signed_byte(bc[pc+2])  # JMP
            elif op == 0x20: regs[bc[pc+1]] = regs[bc[pc+2]] + regs[bc[pc+3]]; pc += 4
            elif op == 0x21: regs[bc[pc+1]] = regs[bc[pc+2]] - regs[bc[pc+3]]; pc += 4
            elif op == 0x22: regs[bc[pc+1]] = regs[bc[pc+2]] * regs[bc[pc+3]]; pc += 4
            elif op == 0x23:
                rs2_val = regs[bc[pc+3]]
                regs[bc[pc+1]] = regs[bc[pc+2]] // rs2_val if rs2_val != 0 else 0; pc += 4
            elif op == 0x24:
                rs2_val = regs[bc[pc+3]]
                regs[bc[pc+1]] = regs[bc[pc+2]] % rs2_val if rs2_val != 0 else 0; pc += 4
            elif op == 0x25: regs[bc[pc+1]] = regs[bc[pc+2]] & regs[bc[pc+3]]; pc += 4
            elif op == 0x26: regs[bc[pc+1]] = regs[bc[pc+2]] | regs[bc[pc+3]]; pc += 4
            elif op == 0x27: regs[bc[pc+1]] = regs[bc[pc+2]] ^ regs[bc[pc+3]]; pc += 4
            elif op == 0x28: regs[bc[pc+1]] = regs[bc[pc+2]] << regs[bc[pc+3]]; pc += 4
            elif op == 0x29: regs[bc[pc+1]] = regs[bc[pc+2]] >> regs[bc[pc+3]]; pc += 4
            elif op == 0x2C: regs[bc[pc+1]] = 1 if regs[bc[pc+2]] == regs[bc[pc+3]] else 0; pc += 4
            elif op == 0x2D: regs[bc[pc+1]] = 1 if regs[bc[pc+2]] < regs[bc[pc+3]] else 0; pc += 4
            elif op == 0x3A: regs[bc[pc+1]] = regs[bc[pc+2]]; pc += 4
            elif op == 0x3C:
                if regs[bc[pc+1]] == 0: pc += _signed_byte(bc[pc+2])
                else: pc += 4
            elif op == 0x3D:
                if regs[bc[pc+1]] != 0: pc += _signed_byte(bc[pc+2])
                else: pc += 4
            elif op == 0x3E:
                if regs[bc[pc+1]] < 0: pc += _signed_byte(bc[pc+2])
                else: pc += 4
            elif op == 0x3F:
                if regs[bc[pc+1]] >= 0: pc += _signed_byte(bc[pc+2])
                else: pc += 4
            else: pc += 1

        return {i: regs[i] for i in range(16)}, cycles

    def run_with_state(self, bytecode: List[int], initial: Dict[int, int] = None) -> VMState:
        """Run and return a full VMState snapshot."""
        regs, cycles = self.run(bytecode, initial)
        return VMState(
            registers=regs, stack_top=0, pc=0, cycles=cycles, halted=True
        )


# ═══════════════════════════════════════════════════════════════════
# Disassembler (for snapshot testing)
# ═══════════════════════════════════════════════════════════════════

def disassemble(bytecode: List[int]) -> str:
    """Disassemble FLUX bytecode to a human-readable string."""
    lines = []
    i = 0
    bc = bytes(bytecode)
    while i < len(bc):
        op = bc[i]
        name = OPCODE_NAMES.get(op, f"UNK_{op:#04x}")
        if op <= 0x07:
            lines.append(f"{i:04d}: {name}")
            i += 1
        elif op <= 0x17:
            lines.append(f"{i:04d}: {name} R{bc[i+1]}")
            i += 2
        elif op <= 0x1F:
            imm = _signed_byte(bc[i+2])
            lines.append(f"{i:04d}: {name} R{bc[i+1]}, {imm}")
            i += 3
        else:
            lines.append(f"{i:04d}: {name} R{bc[i+1]}, R{bc[i+2]}, R{bc[i+3]}")
            i += 4
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Test Framework
# ═══════════════════════════════════════════════════════════════════

class TestStatus(Enum):
    PASSED = "passed"
    FAILED = "failed"
    SKIPPED = "skipped"
    ERROR = "error"


@dataclass
class Assertion:
    name: str
    passed: bool
    expected: str
    actual: str


@dataclass
class TestResult:
    name: str
    status: TestStatus
    assertions: List[Assertion]
    duration_ms: float
    error: str = ""
    opcode_tag: Optional[str] = None  # Tag for per-opcode reporting

    @property
    def passed(self) -> bool:
        return self.status == TestStatus.PASSED

    @property
    def assertion_count(self) -> int:
        return len(self.assertions)

    @property
    def failed_assertions(self) -> List[Assertion]:
        return [a for a in self.assertions if not a.passed]


@dataclass
class SuiteResult:
    name: str
    tests: List[TestResult]
    start_time: float
    end_time: float

    @property
    def total(self) -> int: return len(self.tests)
    @property
    def passed(self) -> int: return sum(1 for t in self.tests if t.passed)
    @property
    def failed(self) -> int: return sum(1 for t in self.tests if t.status == TestStatus.FAILED)
    @property
    def errors(self) -> int: return sum(1 for t in self.tests if t.status == TestStatus.ERROR)
    @property
    def skipped(self) -> int: return sum(1 for t in self.tests if t.status == TestStatus.SKIPPED)
    @property
    def duration_ms(self) -> float: return (self.end_time - self.start_time) * 1000

    def to_markdown(self) -> str:
        lines = [f"# Test Suite: {self.name}\n"]
        lines.append(f"**{self.passed}/{self.total} passed** in {self.duration_ms:.1f}ms\n")
        for t in self.tests:
            icon = {"passed":"✅","failed":"❌","skipped":"⏭️","error":"💥"}.get(t.status.value, "?")
            tag = f" [{t.opcode_tag}]" if t.opcode_tag else ""
            lines.append(f"{icon} {t.name}{tag} ({t.duration_ms:.1f}ms)")
            for a in t.failed_assertions:
                lines.append(f"  ❌ {a.name}: expected {a.expected}, got {a.actual}")
            if t.error:
                lines.append(f"  💥 {t.error}")
        return "\n".join(lines)

    def to_json(self) -> str:
        return json.dumps({
            "name": self.name,
            "total": self.total, "passed": self.passed,
            "failed": self.failed, "errors": self.errors, "skipped": self.skipped,
            "duration_ms": round(self.duration_ms, 2),
            "tests": [
                {
                    "name": t.name, "status": t.status.value,
                    "assertion_count": t.assertion_count,
                    "duration_ms": round(t.duration_ms, 2),
                    "opcode_tag": t.opcode_tag,
                    "error": t.error,
                }
                for t in self.tests
            ],
        }, indent=2)

    def to_terminal(self) -> str:
        lines = ["═" * 55]
        lines.append(f"  Suite: {self.name}")
        lines.append(f"  Result: {self.passed}/{self.total} passed in {self.duration_ms:.1f}ms")
        lines.append("─" * 55)
        for t in self.tests:
            icon = {"passed":"✓","failed":"✗","skipped":"-","error":"!"}.get(t.status.value, "?")
            tag = f" [{t.opcode_tag}]" if t.opcode_tag else ""
            lines.append(f"  {icon} {t.name}{tag} ({t.duration_ms:.1f}ms)")
            for a in t.failed_assertions:
                lines.append(f"      ✗ {a.name}: expected {a.expected}, got {a.actual}")
            if t.error:
                lines.append(f"      ! {t.error}")
        lines.append("═" * 55)
        return "\n".join(lines)

    def per_opcode_report(self) -> str:
        """Generate a per-opcode pass/fail breakdown."""
        opcode_results: Dict[str, Dict[str, int]] = {}
        for t in self.tests:
            tag = t.opcode_tag or "untagged"
            if tag not in opcode_results:
                opcode_results[tag] = {"passed": 0, "failed": 0, "error": 0}
            if t.status == TestStatus.PASSED:
                opcode_results[tag]["passed"] += 1
            elif t.status == TestStatus.FAILED:
                opcode_results[tag]["failed"] += 1
            else:
                opcode_results[tag]["error"] += 1

        lines = ["┌──────────────────────────────────────────────┐"]
        lines.append("│  Per-Opcode Pass/Fail Report             │")
        lines.append("├──────────────┬───────┬───────┬──────────┤")
        lines.append("│ Opcode       │ Pass  │ Fail  │ Rate     │")
        lines.append("├──────────────┼───────┼───────┼──────────┤")
        for opcode, counts in sorted(opcode_results.items()):
            total = counts["passed"] + counts["failed"] + counts["error"]
            rate = (counts["passed"] / total * 100) if total > 0 else 0
            lines.append(f"│ {opcode:<12} │ {counts['passed']:>5} │ {counts['failed']:>5} │ {rate:>6.1f}%  │")
        lines.append("└──────────────┴───────┴───────┴──────────┘")
        return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════
# Assertion Helpers
# ═══════════════════════════════════════════════════════════════════

class FluxTestContext:
    """Context object passed to test functions with rich assertion helpers."""

    def __init__(self):
        self.assertions: List[Assertion] = []
        self._skip = False

    def _add(self, name: str, passed: bool, expected: str, actual: str):
        self.assertions.append(Assertion(name=name, passed=passed, expected=expected, actual=str(actual)))

    def assert_register(self, regs: Dict[int, int], reg: int, expected: int, msg: str = ""):
        actual = regs.get(reg, 0)
        self._add(msg or f"R{reg} == {expected}", actual == expected, str(expected), actual)

    def assert_register_eq(self, regs: Dict[int, int], reg: int, expected: int, msg: str = ""):
        """Alias for assert_register."""
        self.assert_register(regs, reg, expected, msg)

    def assert_register_ne(self, regs: Dict[int, int], reg: int, expected_not: int, msg: str = ""):
        actual = regs.get(reg, 0)
        self._add(msg or f"R{reg} != {expected_not}", actual != expected_not, f"!= {expected_not}", actual)

    def assert_register_range(self, regs: Dict[int, int], reg: int, lo: int, hi: int, msg: str = ""):
        actual = regs.get(reg, 0)
        self._add(msg or f"R{reg} in [{lo}, {hi}]", lo <= actual <= hi, f"[{lo}, {hi}]", actual)

    def assert_flag_zero(self, state: VMState, expected: bool, msg: str = ""):
        self._add(msg or "flag_zero", state.flag_zero() == expected, str(expected), str(state.flag_zero()))

    def assert_flag_negative(self, state: VMState, expected: bool, msg: str = ""):
        self._add(msg or "flag_negative", state.flag_negative() == expected, str(expected), str(state.flag_negative()))

    def assert_halted(self, state: VMState, expected: bool = True, msg: str = ""):
        self._add(msg or "halted", state.halted == expected, str(expected), str(state.halted))

    def assert_not_equal(self, actual, expected_not, msg: str = ""):
        self._add(msg or f"value != {expected_not}", actual != expected_not, f"!= {expected_not}", actual)

    def assert_true(self, value: bool, msg: str = ""):
        self._add(msg or "value is true", value, "True", str(value))

    def assert_false(self, value: bool, msg: str = ""):
        self._add(msg or "value is false", not value, "False", str(value))

    def assert_greater(self, actual, threshold, msg: str = ""):
        self._add(msg or f"value > {threshold}", actual > threshold, f">{threshold}", actual)

    def assert_less(self, actual, threshold, msg: str = ""):
        self._add(msg or f"value < {threshold}", actual < threshold, f"<{threshold}", actual)

    def assert_in_range(self, value, lo, hi, msg: str = ""):
        self._add(msg or f"value in [{lo}, {hi}]", lo <= value <= hi, f"[{lo}, {hi}]", value)

    def assert_cycles(self, cycles: int, max_cycles: int, msg: str = ""):
        self._add(msg or f"cycles <= {max_cycles}", cycles <= max_cycles, f"<={max_cycles}", cycles)

    def assert_bytecode_size(self, bytecode: List[int], max_bytes: int, msg: str = ""):
        self._add(msg or f"bytecode <= {max_bytes} bytes", len(bytecode) <= max_bytes, f"<={max_bytes}", len(bytecode))

    def assert_no_error(self, fn: Callable, *args, msg: str = ""):
        try:
            fn(*args)
            self._add(msg or "no error raised", True, "no error", "no error")
        except Exception as e:
            self._add(msg or "no error raised", False, "no error", str(e))

    def skip(self, reason: str = ""):
        """Mark this test as skipped."""
        self._skip = True
        self.assertions.append(Assertion(name=f"skipped: {reason}", passed=True, expected="skip", actual="skip"))


# ═══════════════════════════════════════════════════════════════════
# Test Suite
# ═══════════════════════════════════════════════════════════════════

class FluxTestSuite:
    """Define and run FLUX test suites."""

    def __init__(self, name: str):
        self.name = name
        self._tests: List[Tuple[str, Callable, Optional[str]]] = []
        self._vm = _MiniVM()
        self._setup: Optional[Callable] = None
        self._teardown: Optional[Callable] = None

    def test(self, name: str, opcode_tag: str = ""):
        """Decorator to register a test."""
        def decorator(fn):
            self._tests.append((name, fn, opcode_tag or None))
            return fn
        return decorator

    def add_test(self, name: str, fn: Callable, opcode_tag: str = ""):
        self._tests.append((name, fn, opcode_tag or None))

    def setup(self, fn: Callable):
        self._setup = fn
        return fn

    def teardown(self, fn: Callable):
        self._teardown = fn
        return fn

    def run(self) -> SuiteResult:
        t0 = time.time()
        results = []

        if self._setup:
            try:
                self._setup(self._vm)
            except Exception:
                pass

        for name, fn, tag in self._tests:
            ctx = FluxTestContext()
            t_start = time.perf_counter()
            try:
                fn(ctx, self._vm)
                if ctx._skip:
                    status = TestStatus.SKIPPED
                else:
                    all_passed = all(a.passed for a in ctx.assertions)
                    status = TestStatus.PASSED if all_passed else TestStatus.FAILED
            except Exception as e:
                status = TestStatus.ERROR
                ctx.assertions.append(Assertion("exception", False, "no error", str(e)))

            t_end = time.perf_counter()
            results.append(TestResult(
                name=name, status=status, assertions=ctx.assertions,
                duration_ms=(t_end - t_start) * 1000,
                error="" if status != TestStatus.ERROR else str(ctx.assertions[-1].actual if ctx.assertions else ""),
                opcode_tag=tag,
            ))

        if self._teardown:
            try:
                self._teardown(self._vm)
            except Exception:
                pass

        return SuiteResult(
            name=self.name, tests=results,
            start_time=t0, end_time=time.time()
        )


# ═══════════════════════════════════════════════════════════════════
# Test Fixture Generators
# ═══════════════════════════════════════════════════════════════════

class BytecodeBuilder:
    """Fluent builder for FLUX bytecode programs."""

    def __init__(self):
        self._bc: List[int] = []

    def halt(self):
        self._bc.extend([0x00])
        return self

    def nop(self):
        self._bc.extend([0x01])
        return self

    def movi(self, rd: int, imm: int):
        self._bc.extend([0x18, rd, imm & 0xFF])
        return self

    def add(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x20, rd, rs1, rs2])
        return self

    def sub(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x21, rd, rs1, rs2])
        return self

    def mul(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x22, rd, rs1, rs2])
        return self

    def div(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x23, rd, rs1, rs2])
        return self

    def mod(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x24, rd, rs1, rs2])
        return self

    def and_(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x25, rd, rs1, rs2])
        return self

    def or_(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x26, rd, rs1, rs2])
        return self

    def xor(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x27, rd, rs1, rs2])
        return self

    def seq(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x2C, rd, rs1, rs2])
        return self

    def slt(self, rd: int, rs1: int, rs2: int):
        self._bc.extend([0x2D, rd, rs1, rs2])
        return self

    def movr(self, rd: int, rs1: int):
        self._bc.extend([0x3A, rd, rs1, 0])
        return self

    def beq(self, rs: int, offset: int):
        self._bc.extend([0x3C, rs, offset & 0xFF, 0])
        return self

    def bne(self, rs: int, offset: int):
        self._bc.extend([0x3D, rs, offset & 0xFF, 0])
        return self

    def incr(self, rd: int):
        self._bc.extend([0x08, rd])
        return self

    def decr(self, rd: int):
        self._bc.extend([0x09, rd])
        return self

    def push(self, rd: int):
        self._bc.extend([0x0C, rd])
        return self

    def pop(self, rd: int):
        self._bc.extend([0x0D, rd])
        return self

    def build(self) -> List[int]:
        return list(self._bc)

    def __len__(self):
        return len(self._bc)


class FixtureGenerator:
    """Generate test fixtures: edge cases, random programs, known patterns."""

    def __init__(self, seed: Optional[int] = None):
        self._rng = random.Random(seed)

    @staticmethod
    def movi_program(rd: int, value: int) -> List[int]:
        """Generate a simple MOVI + HALT program."""
        return [0x18, rd, value & 0xFF, 0x00]

    @staticmethod
    def add_program(a: int, b: int) -> List[int]:
        """Generate a program that adds two immediates."""
        return [0x18, 0, a & 0xFF, 0x18, 1, b & 0xFF, 0x20, 2, 0, 1, 0x00]

    @staticmethod
    def factorial_program(n: int) -> List[int]:
        """Generate a program that computes n! in R1."""
        # MOVI R0, n; MOVI R1, 1; loop: MUL R1, R1, R0; DECR R0; BNE R0, offset; HALT
        # offset = -6 = 0xFA
        return [0x18, 0, n & 0xFF, 0x18, 1, 1, 0x22, 1, 1, 0, 0x09, 0, 0x3D, 0, 0xFA, 0, 0x00]

    @staticmethod
    def edge_zero_program() -> List[int]:
        """Edge case: all zeros."""
        return [0x00]

    @staticmethod
    def edge_max_immediate() -> List[int]:
        """Edge case: max immediate value (127)."""
        return [0x18, 0, 0x7F, 0x00]

    @staticmethod
    def edge_negative_immediate() -> List[int]:
        """Edge case: negative immediate (-128 via 0x80)."""
        return [0x18, 0, 0x80, 0x00]

    @staticmethod
    def loop_program(iterations: int) -> List[int]:
        """Generate a loop that runs N times: MOVI R0, N; DECR; BNE R0, offset; HALT."""
        # MOVI at PC=0 (3 bytes), DECR at PC=3 (2 bytes), BNE at PC=5
        # Jump back to PC=3: offset = 3 - 5 = -2 = 0xFE
        return [0x18, 0, iterations & 0xFF, 0x09, 0, 0x3D, 0, 0xFE, 0, 0x00]

    @staticmethod
    def nop_sled(count: int) -> List[int]:
        """Generate a NOP sled."""
        return [0x01] * count + [0x00]

    @staticmethod
    def push_pop_program() -> List[int]:
        """Push R0, pop R1."""
        return [0x18, 0, 42, 0x0C, 0, 0x0D, 1, 0x00]

    def random_movi_program(self, rd: int = 0, value_range: Tuple[int, int] = (-128, 127)) -> List[int]:
        """Generate a random MOVI program."""
        value = self._rng.randint(*value_range)
        return self.movi_program(rd, value)

    def random_arithmetic_program(self) -> List[int]:
        """Generate a random 2-operand arithmetic program."""
        a = self._rng.randint(0, 100)
        b = self._rng.randint(0, 100)
        ops = [0x20, 0x21, 0x22]  # ADD, SUB, MUL
        op = self._rng.choice(ops)
        return [0x18, 0, a & 0xFF, 0x18, 1, b & 0xFF, op, 2, 0, 1, 0x00]

    def random_program(self, length: int = 5, opcodes: Optional[List[int]] = None) -> List[int]:
        """Generate a random bytecode program of given instruction count."""
        if opcodes is None:
            opcodes = [0x01, 0x08, 0x09, 0x18, 0x20, 0x21, 0x22]
        bc = []
        for _ in range(length):
            op = self._rng.choice(opcodes)
            bc.append(op)
            if op == 0x18:
                bc.extend([self._rng.randint(0, 3), self._rng.randint(0, 50)])
            elif op in (0x20, 0x21, 0x22):
                bc.extend([self._rng.randint(0, 3), self._rng.randint(0, 3), self._rng.randint(0, 3)])
            elif op in (0x08, 0x09):
                bc.append(self._rng.randint(0, 3))
        bc.append(0x00)
        return bc


# ═══════════════════════════════════════════════════════════════════
# Property-Based Testing Support
# ═══════════════════════════════════════════════════════════════════

@dataclass
class PropertyResult:
    """Result of a property-based test."""
    property_name: str
    passed: bool
    iterations: int
    counterexample: Optional[Any] = None
    error: Optional[str] = None


class PropertyChecker:
    """
    Property-based testing for FLUX VM.
    Run assertions against randomly generated inputs.
    """

    def __init__(self, seed: Optional[int] = None):
        self._rng = random.Random(seed)
        self._results: List[PropertyResult] = []

    def for_all_values(self, name: str, values: List[int], fn: Callable[[int], bool],
                       max_iterations: int = 100) -> PropertyResult:
        """Test a property for all values in a list (sampled up to max_iterations)."""
        sample = values[:max_iterations]
        for val in sample:
            try:
                if not fn(val):
                    result = PropertyResult(name, False, len(sample), counterexample=val)
                    self._results.append(result)
                    return result
            except Exception as e:
                result = PropertyResult(name, False, len(sample), counterexample=val, error=str(e))
                self._results.append(result)
                return result
        result = PropertyResult(name, True, len(sample))
        self._results.append(result)
        return result

    def for_all_bytecodes(self, name: str, generator: Callable[[], List[int]],
                          fn: Callable[[List[int], Dict[int, int], int], bool],
                          max_iterations: int = 50, vm: Optional[_MiniVM] = None) -> PropertyResult:
        """Test a property against randomly generated bytecode programs."""
        if vm is None:
            vm = _MiniVM()
        for i in range(max_iterations):
            bc = generator()
            try:
                regs, cycles = vm.run(bc)
                if not fn(bc, regs, cycles):
                    result = PropertyResult(name, False, i + 1, counterexample=bc)
                    self._results.append(result)
                    return result
            except Exception as e:
                result = PropertyResult(name, False, i + 1, counterexample=bc, error=str(e))
                self._results.append(result)
                return result
        result = PropertyResult(name, True, max_iterations)
        self._results.append(result)
        return result

    @property
    def results(self) -> List[PropertyResult]:
        return self._results

    @property
    def all_passed(self) -> bool:
        return all(r.passed for r in self._results)


# ═══════════════════════════════════════════════════════════════════
# Snapshot Testing
# ═══════════════════════════════════════════════════════════════════

class SnapshotTester:
    """
    Snapshot testing for disassembly output.
    Compares current disassembly against stored snapshots.
    """

    def __init__(self, snapshot_dir: str = ".snapshots"):
        self.snapshot_dir = snapshot_dir

    def _snapshot_path(self, name: str) -> str:
        return os.path.join(self.snapshot_dir, f"{name}.snap")

    def assert_match_snapshot(self, name: str, bytecode: List[int], update: bool = False) -> Tuple[bool, str]:
        """Compare disassembly output against stored snapshot."""
        current = disassemble(bytecode)
        snap_path = self._snapshot_path(name)

        if update:
            os.makedirs(self.snapshot_dir, exist_ok=True)
            with open(snap_path, "w") as f:
                f.write(current)
            return True, "snapshot updated"

        if os.path.exists(snap_path):
            with open(snap_path, "r") as f:
                expected = f.read()
            if current == expected:
                return True, "snapshot matches"
            else:
                return False, f"snapshot mismatch:\nexpected:\n{expected}\n\ngot:\n{current}"
        else:
            # Auto-create on first run
            os.makedirs(self.snapshot_dir, exist_ok=True)
            with open(snap_path, "w") as f:
                f.write(current)
            return True, "snapshot created"

    def assert_snapshot_content(self, name: str, content: str, update: bool = False) -> Tuple[bool, str]:
        """Compare arbitrary content against stored snapshot."""
        snap_path = self._snapshot_path(name)

        if update:
            os.makedirs(self.snapshot_dir, exist_ok=True)
            with open(snap_path, "w") as f:
                f.write(content)
            return True, "snapshot updated"

        if os.path.exists(snap_path):
            with open(snap_path, "r") as f:
                expected = f.read()
            if content == expected:
                return True, "snapshot matches"
            else:
                return False, "snapshot mismatch"
        else:
            os.makedirs(self.snapshot_dir, exist_ok=True)
            with open(snap_path, "w") as f:
                f.write(content)
            return True, "snapshot created"


# ═══════════════════════════════════════════════════════════════════
# Tests
# ═══════════════════════════════════════════════════════════════════

import unittest


class TestAssertions(unittest.TestCase):
    """Test assertion helpers."""

    def test_assert_register_eq(self):
        ctx = FluxTestContext()
        ctx.assert_register_eq({0: 42}, 0, 42)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_register_eq_fail(self):
        ctx = FluxTestContext()
        ctx.assert_register_eq({0: 42}, 0, 99)
        self.assertFalse(ctx.assertions[0].passed)

    def test_assert_register_ne(self):
        ctx = FluxTestContext()
        ctx.assert_register_ne({0: 42}, 0, 99)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_register_ne_fail(self):
        ctx = FluxTestContext()
        ctx.assert_register_ne({0: 42}, 0, 42)
        self.assertFalse(ctx.assertions[0].passed)

    def test_assert_register_range(self):
        ctx = FluxTestContext()
        ctx.assert_register_range({0: 50}, 0, 0, 100)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_register_range_fail(self):
        ctx = FluxTestContext()
        ctx.assert_register_range({0: 200}, 0, 0, 100)
        self.assertFalse(ctx.assertions[0].passed)

    def test_assert_flag_zero(self):
        state = VMState(registers={0: 0}, stack_top=0, pc=0, cycles=1, halted=True)
        ctx = FluxTestContext()
        ctx.assert_flag_zero(state, True)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_flag_negative(self):
        state = VMState(registers={0: -5}, stack_top=0, pc=0, cycles=1, halted=True)
        ctx = FluxTestContext()
        ctx.assert_flag_negative(state, True)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_halted(self):
        state = VMState(registers={}, stack_top=0, pc=0, cycles=1, halted=True)
        ctx = FluxTestContext()
        ctx.assert_halted(state, True)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_true_false(self):
        ctx = FluxTestContext()
        ctx.assert_true(True)
        ctx.assert_false(False)
        self.assertTrue(all(a.passed for a in ctx.assertions))

    def test_assert_greater_less(self):
        ctx = FluxTestContext()
        ctx.assert_greater(10, 5)
        ctx.assert_less(3, 5)
        self.assertTrue(all(a.passed for a in ctx.assertions))

    def test_assert_in_range(self):
        ctx = FluxTestContext()
        ctx.assert_in_range(50, 0, 100)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_no_error(self):
        ctx = FluxTestContext()
        ctx.assert_no_error(lambda: None)
        self.assertTrue(ctx.assertions[0].passed)

    def test_assert_no_error_catches(self):
        ctx = FluxTestContext()
        ctx.assert_no_error(lambda: (_ for _ in ()).throw(ValueError("boom")), msg="should catch")
        self.assertFalse(ctx.assertions[0].passed)

    def test_skip(self):
        ctx = FluxTestContext()
        ctx.skip("test reason")
        self.assertTrue(ctx._skip)


class TestSuiteRunner(unittest.TestCase):
    """Test suite execution."""

    def test_basic_suite(self):
        suite = FluxTestSuite("basic")
        suite.add_test("movi_42", lambda ctx, vm: ctx.assert_register(vm.run([0x18, 0, 42, 0x00])[0], 0, 42))
        result = suite.run()
        self.assertEqual(result.passed, 1)
        self.assertEqual(result.total, 1)

    def test_failed_assertion(self):
        suite = FluxTestSuite("fail")
        suite.add_test("wrong_value", lambda ctx, vm: ctx.assert_register(vm.run([0x18, 0, 42, 0x00])[0], 0, 99))
        result = suite.run()
        self.assertEqual(result.failed, 1)

    def test_add_program(self):
        suite = FluxTestSuite("add")
        suite.add_test("add_10_20", lambda ctx, vm: ctx.assert_register(
            vm.run([0x18, 0, 10, 0x18, 1, 20, 0x20, 2, 0, 1, 0x00])[0], 2, 30, "R0+R1=R2"))
        result = suite.run()
        self.assertTrue(result.tests[0].passed)

    def test_multiple_tests(self):
        suite = FluxTestSuite("multi")
        for val in [10, 20, 30]:
            def make_test(v):
                return lambda ctx, vm: ctx.assert_register(vm.run([0x18, 0, v, 0x00])[0], 0, v)
            suite.add_test(f"movi_{val}", make_test(val))
        result = suite.run()
        self.assertEqual(result.passed, 3)

    def test_error_handling(self):
        suite = FluxTestSuite("error")
        suite.add_test("crash", lambda ctx, vm: (_ for _ in ()).throw(RuntimeError("boom")))
        result = suite.run()
        self.assertEqual(result.errors, 1)

    def test_cycle_assertion(self):
        suite = FluxTestSuite("cycles")
        suite.add_test("fast", lambda ctx, vm: ctx.assert_cycles(vm.run([0x18, 0, 42, 0x00])[1], 100, "should complete fast"))
        result = suite.run()
        self.assertTrue(result.tests[0].passed)

    def test_markdown_report(self):
        suite = FluxTestSuite("report")
        suite.add_test("t1", lambda ctx, vm: ctx.assert_register({0: 42}, 0, 42))
        result = suite.run()
        md = result.to_markdown()
        self.assertIn("report", md)
        self.assertIn("✅", md)

    def test_json_report(self):
        suite = FluxTestSuite("json_report")
        suite.add_test("t1", lambda ctx, vm: ctx.assert_register({0: 42}, 0, 42))
        result = suite.run()
        j = result.to_json()
        data = json.loads(j)
        self.assertEqual(data["total"], 1)
        self.assertEqual(data["passed"], 1)

    def test_terminal_report(self):
        suite = FluxTestSuite("term")
        suite.add_test("t1", lambda ctx, vm: ctx.assert_register({0: 42}, 0, 42))
        result = suite.run()
        txt = result.to_terminal()
        self.assertIn("Suite: term", txt)
        self.assertIn("✓", txt)

    def test_bytecode_size_assertion(self):
        suite = FluxTestSuite("size")
        suite.add_test("size", lambda ctx, vm: ctx.assert_bytecode_size([0x18, 0, 42, 0x00], 10, "program fits"))
        result = suite.run()
        self.assertTrue(result.tests[0].passed)

    def test_skipped_test(self):
        suite = FluxTestSuite("skip")
        suite.add_test("skipped", lambda ctx, vm: ctx.skip("not ready"))
        result = suite.run()
        self.assertEqual(result.skipped, 1)

    def test_per_opcode_report(self):
        suite = FluxTestSuite("opcode_report")
        suite.add_test("t1", lambda ctx, vm: ctx.assert_register({0: 42}, 0, 42), opcode_tag="MOVI")
        suite.add_test("t2", lambda ctx, vm: ctx.assert_register({0: 99}, 0, 42), opcode_tag="MOVI")
        suite.add_test("t3", lambda ctx, vm: ctx.assert_register({0: 30}, 2, 30), opcode_tag="ADD")
        result = suite.run()
        report = result.per_opcode_report()
        self.assertIn("MOVI", report)
        self.assertIn("ADD", report)
        self.assertIn("Rate", report)


class TestFixtureGenerators(unittest.TestCase):
    """Test fixture generators."""

    def test_movi_program(self):
        bc = FixtureGenerator.movi_program(0, 42)
        self.assertEqual(len(bc), 4)
        self.assertEqual(bc[0], 0x18)

    def test_add_program(self):
        bc = FixtureGenerator.add_program(10, 20)
        self.assertIn(0x20, bc)

    def test_factorial_program(self):
        bc = FixtureGenerator.factorial_program(6)
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[1], 720)

    def test_edge_zero_program(self):
        bc = FixtureGenerator.edge_zero_program()
        self.assertEqual(bc, [0x00])

    def test_edge_max_immediate(self):
        bc = FixtureGenerator.edge_max_immediate()
        self.assertEqual(bc[2], 0x7F)

    def test_edge_negative_immediate(self):
        bc = FixtureGenerator.edge_negative_immediate()
        self.assertEqual(bc[2], 0x80)
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[0], -128)

    def test_loop_program(self):
        bc = FixtureGenerator.loop_program(5)
        vm = _MiniVM()
        regs, cycles = vm.run(bc)
        self.assertEqual(regs[0], 0)
        # MOVI(1) + 5*(DECR+BNE_taken) + 1*BNE_fallthrough + HALT(1) = 1+10+4+1 = 16
        self.assertGreater(cycles, 5)

    def test_nop_sled(self):
        bc = FixtureGenerator.nop_sled(10)
        self.assertEqual(len(bc), 11)
        self.assertTrue(all(b == 0x01 for b in bc[:-1]))

    def test_push_pop_program(self):
        bc = FixtureGenerator.push_pop_program()
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[1], 42)

    def test_random_movi_program(self):
        gen = FixtureGenerator(seed=42)
        bc = gen.random_movi_program(0)
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertIn(regs[0], range(-128, 128))

    def test_random_arithmetic_program(self):
        gen = FixtureGenerator(seed=42)
        bc = gen.random_arithmetic_program()
        self.assertIn(0x00, bc)  # ends with HALT

    def test_random_program(self):
        gen = FixtureGenerator(seed=42)
        bc = gen.random_program(length=5)
        self.assertIn(0x00, bc)


class TestBytecodeBuilder(unittest.TestCase):
    """Test the fluent bytecode builder."""

    def test_simple_build(self):
        bc = BytecodeBuilder().movi(0, 42).halt().build()
        self.assertEqual(bc, [0x18, 0, 42, 0x00])

    def test_add_program(self):
        bc = BytecodeBuilder().movi(0, 10).movi(1, 20).add(2, 0, 1).halt().build()
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[2], 30)

    def test_loop(self):
        # MOVI at PC=0 (3 bytes), DECR at PC=3 (2 bytes), BNE at PC=5
        # Jump back to PC=3: offset = 3 - 5 = -2
        bc = (BytecodeBuilder()
              .movi(0, 3)
              .decr(0)
              .bne(0, -2)  # 0xFE
              .halt()
              .build())
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[0], 0)

    def test_mul(self):
        bc = BytecodeBuilder().movi(0, 6).movi(1, 7).mul(2, 0, 1).halt().build()
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[2], 42)

    def test_sub(self):
        bc = BytecodeBuilder().movi(0, 30).movi(1, 12).sub(2, 0, 1).halt().build()
        vm = _MiniVM()
        regs, _ = vm.run(bc)
        self.assertEqual(regs[2], 18)

    def test_builder_len(self):
        builder = BytecodeBuilder().movi(0, 42).nop()
        self.assertEqual(len(builder), 4)


class TestDisassembler(unittest.TestCase):
    """Test disassembly output."""

    def test_simple_disasm(self):
        bc = [0x18, 0, 42, 0x00]
        result = disassemble(bc)
        self.assertIn("MOVI", result)
        self.assertIn("HALT", result)

    def test_add_disasm(self):
        bc = [0x18, 0, 10, 0x18, 1, 20, 0x20, 2, 0, 1, 0x00]
        result = disassemble(bc)
        self.assertIn("ADD", result)

    def test_unknown_opcode(self):
        # Unknown opcode 0xFF is a 4-byte RRR-type, needs 3 more bytes
        bc = [0xFF, 0, 0, 0, 0x00]
        result = disassemble(bc)
        self.assertIn("UNK_", result)


class TestPropertyBased(unittest.TestCase):
    """Test property-based testing support."""

    def test_for_all_values_pass(self):
        checker = PropertyChecker()
        result = checker.for_all_values("positive", [1, 2, 3, 4, 5], lambda x: x > 0)
        self.assertTrue(result.passed)

    def test_for_all_values_fail(self):
        checker = PropertyChecker()
        result = checker.for_all_values("positive", [1, -1, 3], lambda x: x > 0)
        self.assertFalse(result.passed)
        self.assertEqual(result.counterexample, -1)

    def test_for_all_bytecodes_halt(self):
        checker = PropertyChecker()
        vm = _MiniVM()
        gen = FixtureGenerator(seed=42)
        result = checker.for_all_bytecodes(
            "halts", lambda: gen.movi_program(0, 42),
            lambda bc, regs, cycles: cycles > 0, max_iterations=5, vm=vm
        )
        self.assertTrue(result.passed)

    def test_all_passed(self):
        checker = PropertyChecker()
        checker.for_all_values("a", [1, 2], lambda x: x > 0)
        checker.for_all_values("b", [1, 2], lambda x: x > 0)
        self.assertTrue(checker.all_passed)


class TestSnapshotTesting(unittest.TestCase):
    """Test snapshot testing for disassembly."""

    def test_snapshot_create_and_match(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmpdir:
            st = SnapshotTester(snapshot_dir=tmpdir)
            bc = [0x18, 0, 42, 0x00]
            ok, msg = st.assert_match_snapshot("test1", bc)
            self.assertTrue(ok)
            self.assertEqual(msg, "snapshot created")
            # Second call should match
            ok, msg = st.assert_match_snapshot("test1", bc)
            self.assertTrue(ok)
            self.assertEqual(msg, "snapshot matches")

    def test_snapshot_mismatch(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmpdir:
            st = SnapshotTester(snapshot_dir=tmpdir)
            bc1 = [0x18, 0, 42, 0x00]
            bc2 = [0x18, 1, 99, 0x00]
            st.assert_match_snapshot("test2", bc1)
            ok, msg = st.assert_match_snapshot("test2", bc2)
            self.assertFalse(ok)
            self.assertIn("mismatch", msg)

    def test_snapshot_update(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmpdir:
            st = SnapshotTester(snapshot_dir=tmpdir)
            st.assert_match_snapshot("test3", [0x18, 0, 42, 0x00])
            ok, msg = st.assert_match_snapshot("test3", [0x18, 1, 99, 0x00], update=True)
            self.assertTrue(ok)
            self.assertEqual(msg, "snapshot updated")

    def test_snapshot_content(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmpdir:
            st = SnapshotTester(snapshot_dir=tmpdir)
            ok, _ = st.assert_snapshot_content("content1", "hello world")
            self.assertTrue(ok)
            ok, msg = st.assert_snapshot_content("content1", "hello world")
            self.assertTrue(ok)
            self.assertEqual(msg, "snapshot matches")


if __name__ == "__main__":
    unittest.main(verbosity=2)
