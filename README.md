# FLUX TestKit — Test Harness Framework

Write and run FLUX program tests with assertion helpers.

## Features
- Test suite definition with `add_test()` or `@test` decorator
- Assertion helpers: `assert_register`, `assert_cycles`, `assert_bytecode_size`, `assert_true`
- Built-in lightweight VM for test execution
- Markdown report generation with ✅/❌/💥 icons
- Error handling with graceful failure reporting

## Usage
```python
from testkit import FluxTestSuite

suite = FluxTestSuite("my_tests")
suite.add_test("factorial", lambda ctx, vm: (
    ctx.assert_register(vm.run([0x18,0,6, 0x18,1,1, 0x22,1,1,0, 0x09,0, 0x3D,0,0xFA,0, 0x00])[0], 1, 720)
))
result = suite.run()
print(result.to_markdown())
```

8 tests passing.
