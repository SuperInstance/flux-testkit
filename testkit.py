"""
FLUX TestKit — test harness for FLUX programs.

Provides:
- Test runner with setup/teardown
- Assertion helpers (register values, flags, cycles)
- Test suites and grouping
- Report generation (pass/fail/skip counts)
"""
from dataclasses import dataclass, field
from typing import List, Dict, Callable, Optional, Tuple
from enum import Enum
import time


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
    def duration_ms(self) -> float: return (self.end_time - self.start_time) * 1000
    
    def to_markdown(self) -> str:
        lines = [f"# Test Suite: {self.name}\n"]
        lines.append(f"**{self.passed}/{self.total} passed** in {self.duration_ms:.1f}ms\n")
        for t in self.tests:
            icon = {"passed":"✅","failed":"❌","skipped":"⏭️","error":"💥"}.get(t.status.value, "?")
            lines.append(f"{icon} {t.name} ({t.duration_ms:.1f}ms)")
            for a in t.failed_assertions:
                lines.append(f"  ❌ {a.name}: expected {a.expected}, got {a.actual}")
            if t.error:
                lines.append(f"  💥 {t.error}")
        return "\n".join(lines)


class FluxTestContext:
    """Context object passed to test functions with assertion helpers."""
    
    def __init__(self):
        self.assertions: List[Assertion] = []
    
    def assert_register(self, regs: Dict[int, int], reg: int, expected: int, msg: str = ""):
        actual = regs.get(reg, 0)
        passed = actual == expected
        self.assertions.append(Assertion(
            name=msg or f"R{reg} == {expected}", passed=passed,
            expected=str(expected), actual=str(actual)
        ))
    
    def assert_not_equal(self, actual, expected_not, msg: str = ""):
        passed = actual != expected_not
        self.assertions.append(Assertion(
            name=msg or f"value != {expected_not}", passed=passed,
            expected=f"!= {expected_not}", actual=str(actual)
        ))
    
    def assert_true(self, value: bool, msg: str = ""):
        self.assertions.append(Assertion(
            name=msg or "value is true", passed=value,
            expected="True", actual=str(value)
        ))
    
    def assert_cycles(self, cycles: int, max_cycles: int, msg: str = ""):
        passed = cycles <= max_cycles
        self.assertions.append(Assertion(
            name=msg or f"cycles <= {max_cycles}", passed=passed,
            expected=f"<={max_cycles}", actual=str(cycles)
        ))
    
    def assert_bytecode_size(self, bytecode: List[int], max_bytes: int, msg: str = ""):
        passed = len(bytecode) <= max_bytes
        self.assertions.append(Assertion(
            name=msg or f"bytecode <= {max_bytes} bytes", passed=passed,
            expected=f"<={max_bytes}", actual=str(len(bytecode))
        ))


class FluxTestSuite:
    """Define and run FLUX test suites."""
    
    def __init__(self, name: str):
        self.name = name
        self._tests: List[Tuple[str, Callable]] = []
        self._vm = _MiniVM()
    
    def test(self, name: str):
        """Decorator to register a test."""
        def decorator(fn):
            self._tests.append((name, fn))
            return fn
        return decorator
    
    def add_test(self, name: str, fn: Callable):
        self._tests.append((name, fn))
    
    def run(self) -> SuiteResult:
        t0 = time.time()
        results = []
        
        for name, fn in self._tests:
            ctx = FluxTestContext()
            t_start = time.perf_counter()
            try:
                fn(ctx, self._vm)
                all_passed = all(a.passed for a in ctx.assertions)
                status = TestStatus.PASSED if all_passed else TestStatus.FAILED
            except Exception as e:
                status = TestStatus.ERROR
                ctx.assertions.append(Assertion("exception", False, "no error", str(e)))
            
            t_end = time.perf_counter()
            results.append(TestResult(
                name=name, status=status, assertions=ctx.assertions,
                duration_ms=(t_end - t_start) * 1000,
                error="" if status != TestStatus.ERROR else str(ctx.assertions[-1].actual if ctx.assertions else "")
            ))
        
        return SuiteResult(
            name=self.name, tests=results,
            start_time=t0, end_time=time.time()
        )


class _MiniVM:
    """Lightweight VM for test execution."""
    
    def run(self, bytecode: List[int], initial: Dict[int, int] = None) -> Tuple[Dict[int, int], int]:
        regs = [0] * 64
        stack = [0] * 4096
        sp = 4096
        pc = 0
        cycles = 0
        
        if initial:
            for k, v in initial.items(): regs[k] = v
        
        def sb(b): return b - 256 if b > 127 else b
        bc = bytes(bytecode)
        
        while pc < len(bc) and cycles < 100000:
            op = bc[pc]; cycles += 1
            if op == 0x00: break
            elif op == 0x08: regs[bc[pc+1]] += 1; pc += 2
            elif op == 0x09: regs[bc[pc+1]] -= 1; pc += 2
            elif op == 0x0C: sp -= 1; stack[sp] = regs[bc[pc+1]]; pc += 2
            elif op == 0x0D: regs[bc[pc+1]] = stack[sp]; sp += 1; pc += 2
            elif op == 0x18: regs[bc[pc+1]] = sb(bc[pc+2]); pc += 3
            elif op == 0x20: regs[bc[pc+1]] = regs[bc[pc+2]] + regs[bc[pc+3]]; pc += 4
            elif op == 0x21: regs[bc[pc+1]] = regs[bc[pc+2]] - regs[bc[pc+3]]; pc += 4
            elif op == 0x22: regs[bc[pc+1]] = regs[bc[pc+2]] * regs[bc[pc+3]]; pc += 4
            elif op == 0x2C: regs[bc[pc+1]] = 1 if regs[bc[pc+2]] == regs[bc[pc+3]] else 0; pc += 4
            elif op == 0x2D: regs[bc[pc+1]] = 1 if regs[bc[pc+2]] < regs[bc[pc+3]] else 0; pc += 4
            elif op == 0x3A: regs[bc[pc+1]] = regs[bc[pc+2]]; pc += 4
            elif op == 0x3C:
                if regs[bc[pc+1]] == 0: pc += sb(bc[pc+2])
                else: pc += 4
            elif op == 0x3D:
                if regs[bc[pc+1]] != 0: pc += sb(bc[pc+2])
                else: pc += 4
            else: pc += 1
        
        return {i: regs[i] for i in range(16)}, cycles


# ── Tests ──────────────────────────────────────────────

import unittest


class TestTestKit(unittest.TestCase):
    def test_basic_suite(self):
        suite = FluxTestSuite("basic")
        
        def my_test(ctx, vm):
            regs, _ = vm.run([0x18, 0, 42, 0x00])
            ctx.assert_register(regs, 0, 42)
        
        suite.add_test("movi_42", my_test)
        result = suite.run()
        self.assertEqual(result.passed, 1)
        self.assertEqual(result.total, 1)
    
    def test_failed_assertion(self):
        suite = FluxTestSuite("fail")
        
        def fail_test(ctx, vm):
            regs, _ = vm.run([0x18, 0, 42, 0x00])
            ctx.assert_register(regs, 0, 99)
        
        suite.add_test("wrong_value", fail_test)
        result = suite.run()
        self.assertEqual(result.failed, 1)
    
    def test_add_program(self):
        suite = FluxTestSuite("add")
        
        def add_test(ctx, vm):
            regs, _ = vm.run([0x18,0,10, 0x18,1,20, 0x20,2,0,1, 0x00])
            ctx.assert_register(regs, 2, 30, "R0+R1=R2")
        
        suite.add_test("add_10_20", add_test)
        result = suite.run()
        self.assertTrue(result.tests[0].passed)
    
    def test_multiple_tests(self):
        suite = FluxTestSuite("multi")
        
        for val in [10, 20, 30]:
            def make_test(v):
                def t(ctx, vm):
                    regs, _ = vm.run([0x18, 0, v, 0x00])
                    ctx.assert_register(regs, 0, v)
                return t
            suite.add_test(f"movi_{val}", make_test(val))
        
        result = suite.run()
        self.assertEqual(result.passed, 3)
    
    def test_error_handling(self):
        suite = FluxTestSuite("error")
        
        def crash_test(ctx, vm):
            raise RuntimeError("boom")
        
        suite.add_test("crash", crash_test)
        result = suite.run()
        self.assertEqual(result.errors, 1)
    
    def test_cycle_assertion(self):
        suite = FluxTestSuite("cycles")
        
        def cycle_test(ctx, vm):
            _, cycles = vm.run([0x18, 0, 42, 0x00])
            ctx.assert_cycles(cycles, 100, "should complete fast")
        
        suite.add_test("fast", cycle_test)
        result = suite.run()
        self.assertTrue(result.tests[0].passed)
    
    def test_markdown_report(self):
        suite = FluxTestSuite("report")
        suite.add_test("t1", lambda ctx, vm: ctx.assert_register({0:42}, 0, 42))
        result = suite.run()
        md = result.to_markdown()
        self.assertIn("report", md)
        self.assertIn("✅", md)
    
    def test_bytecode_size_assertion(self):
        suite = FluxTestSuite("size")
        
        def size_test(ctx, vm):
            bc = [0x18, 0, 42, 0x00]
            ctx.assert_bytecode_size(bc, 10, "program fits in 10 bytes")
        
        suite.add_test("size", size_test)
        result = suite.run()
        self.assertTrue(result.tests[0].passed)


if __name__ == "__main__":
    unittest.main(verbosity=2)
