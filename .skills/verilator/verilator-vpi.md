---
name: verilator-vpi
description: VPI module structure - verilated_vpi.cpp, --vpi vs --vpi-lazy, callbacks, PLI/VPI integration
---

# Verilator VPI Skill

## VPI Overview

Verilator supports two VPI modes:
- **`--vpi`** - Full VPI, all modules registered at startup
- **`--vpi-lazy`** - Lazy registration, modules loaded on demand (default)

## Key Files

| File | Purpose |
|------|---------|
| `include/verilated_vpi.cpp` | VPI registration, callback dispatch |
| `include/verilated_vpi.h` | VPI function declarations |
| `include/verilated.cpp` | Main runtime, VPI initialization |
| `src/V3EmitCMain.cpp` | VPI module emission |

## VPI Callbacks Supported

| Callback | When Called |
|----------|-------------|
| `vlog_startup_routines_bootstrap` | Before simulation starts |
| `cbStartOfSimulation` | After elaboration, before first eval |
| `cbEndOfSimulation` | After simulation ends |
| `cbValueChange` | On signal value change |
| `cbNextSimTime` | At next scheduled simulation time |

## Adding VPI Function

1. **Declare in `verilated_vpi.h`:**
```cpp
extern "C" PLI_INT32 my_vpi_func(p_vpi_systf_data);
```

2. **Implement in `verilated_vpi.cpp`:**
```cpp
PLI_INT32 my_vpi_func(p_vpi_systf_data data) {
    vpiHandle sys = vpi_handle(vpiSysTfCall, NULL);
    // Access arguments via vpi_iterate/vpi_scan
    return 0;
}
```

3. **Register in `verilated_vpi.cpp::vlog_startup_routines_bootstrap()`:**
```cpp
vpi_register_systf(&my_systf_data);
```

## VPI Module Structure (emitted by V3EmitC)

```cpp
// Generated in obj_dir/V<modulename>__Vpi.cpp
// Contains:
// - vpi registration table
// - Callback wrappers
// - Signal handle creation
```

## Thread Safety

```cpp
// VPI callbacks run in simulation thread
// Use VL_GUARDED_BY for shared data
// No async calls from VPI into simulation
```

## Testing VPI

```systemverilog
// test_regress/t/t_vpi_<feature>.v
module t;
    import "DPI-C" function int my_vpi_func();
    initial $my_vpi_func();
endmodule
```

```python
# test_regress/t/t_vpi_<feature>.py
import vltest_bootstrap
test.sim(v_flags=["--vpi", "--trace"])  # or --vpi-lazy
test.passes()
```

## Common Patterns

| Task | Implementation |
|------|----------------|
| Access signal value | `vpi_get(vpiValue, handle)` |
| Iterate hierarchy | `vpi_iterate(vpiModule, NULL)` |
| Register callback | `vpi_register_cb(&cb_data)` |
| Get simulation time | `vpi_get(vpiSimulationTime, NULL)` |

## --vpi vs --vpi-lazy

| Aspect | `--vpi` | `--vpi-lazy` |
|--------|---------|--------------|
| Startup time | Slower (all modules) | Faster (on demand) |
| Memory | Higher | Lower |
| Use case | Full VPI access needed | Occasional VPI calls |

## Token Efficiency

- VPI changes are rare - search `verilated_vpi.cpp` for patterns
- Test both `--vpi` and `--vpi-lazy` modes
- Follow existing callback patterns in `verilated_vpi.cpp`