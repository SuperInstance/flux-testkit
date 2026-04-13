# FLUX TestKit — Comprehensive Test Harness for FLUX VM Programs

Write and run FLUX program tests with rich assertion helpers, fixture generators, and property-based testing.

## Features

- **Assertion helpers**: `assert_register_eq`, `assert_register_ne`, `assert_register_range`, `assert_flag_zero`, `assert_flag_negative`, `assert_halted`, `assert_true`, `assert_false`, `assert_greater`, `assert_less`, `assert_in_range`, `assert_cycles`, `assert_bytecode_size`, `assert_no_error`, `skip`
- **BytecodeBuilder**: Fluent builder for constructing FLUX bytecode programs (movi, add, sub, mul, div, mod, and_, or_, xor, seq, slt, movr, beq, bne, incr, decr, push, pop, nop, halt)
- **Fixture generators**: Pre-built test programs (movi, add, factorial, loop, NOP sled, push/pop, edge cases), plus seeded random generators
- **Property-based testing**: `PropertyChecker` with `for_all_values` and `for_all_bytecodes` for fuzz-like testing with counterexample reporting
- **Snapshot testing**: `SnapshotTester` for disassembly output comparison (auto-create, match, mismatch detection, update mode)
- **Per-opcode reporting**: Tag tests with opcode names and get pass/fail rates per opcode
- **Multi-format reports**: Terminal, Markdown, and JSON
- **Disassembler**: Human-readable disassembly of FLUX bytecode

## Usage

```python
from testkit import FluxTestSuite, FluxTestContext, BytecodeBuilder, FixtureGenerator, PropertyChecker, SnapshotTester, disassemble

# Basic suite
suite = FluxTestSuite("my_tests")
suite.add_test("add", lambda ctx, vm: ctx.assert_register(
    vm.run([0x18,0,10, 0x18,1,20, 0x20,2,0,1, 0x00])[0], 2, 30
))
result = suite.run()
print(result.to_markdown())
print(result.per_opcode_report())

# BytecodeBuilder
bc = BytecodeBuilder().movi(0, 10).movi(1, 20).add(2, 0, 1).halt().build()

# Fixtures
bc = FixtureGenerator.factorial_program(6)

# Property-based testing
checker = PropertyChecker(seed=42)
result = checker.for_all_values("positive", range(1, 1000), lambda x: x > 0)

# Snapshot testing
st = SnapshotTester()
ok, msg = st.assert_match_snapshot("my_test", bc)

# Disassembly
print(disassemble(bc))
```

56 tests passing.
