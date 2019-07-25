#!/usr/bin/env python3

# This file ONLY is placed into the Public Domain, for any use,
# without warranty, 2019 by Wilson Snyder.

# Simple python example of using the add.v verilog module.
# Can be run in python directly, or pytest

import os
import sys

if __name__ == "__main__":
    print("args:", sys.argv[1:])
    sys.path.extend(sys.argv[1:])
    import example
    import example2
    import example3


def create_callback():
    class _TestCallback(example.VerilatedCallback):
        """A custom callback that does not touch global variables"""
        def __init__(self):
            super().__init__()
            self.output = []
            self.finished = False
            self.stopped = False
            self.fataled = False
            self.should_stop = False

        def on_finish(self, filename, linenum, hier):
            if self.finished:
                self.on_fatal(filename, linenum, hier, "$finish called twice")
            self.finished = True
            self.should_stop = True

        def on_stop(self, filename, linenum, hier):
            self.stopped = True
            self.should_stop = True
            raise example.VerilatedException("$stop called")

        def on_fatal(self, filename, linenum, hier, msg):
            self.fataled = True
            self.should_stop = True
            raise example.VerilatedException("$fatal called")

        def on_print(self, text):
            self.output.append(text)
    return _TestCallback()


def verilator_trace(pymod, m):
    """Generate a convenience wrapper around a Verilated module"""
    class VTrace(m):
        def __init__(self):
            super(VTrace, self).__init__()
            self._tfp = None
            self._timestep = 0

        def trace_start(self, filename):
            if self._tfp:
                self.trace_stop()
            self._timestep = 0
            pymod.Verilated.traceEverOn(True)
            self._tfp = pymod.VerilatedVcd()
            self.trace(self._tfp, 99)
            assert self._tfp.closed
            self._tfp.open(filename)

        def trace_stop(self):
            if self._tfp:
                self._tfp.close()
            self._tfp = None

        def cycle(self):
            self.clk = 0
            self.eval()
            if self._tfp:
                self._tfp.dump(self._timestep)
                self._timestep += 1
            self.clk = 1
            self.eval()

    return VTrace


# Wrap Verilated modules
Add = verilator_trace(example, example.Vadd)
Add2 = verilator_trace(example2, example2.Vadd)
Add3 = verilator_trace(example3, example3.Vadd)
Add3b = verilator_trace(example3, example3.Vadd2)


def test_custom_callback():
    """Test custom callbacks + not touching global variables (if all methods are overridden) + removing callback"""
    cb = create_callback()
    example.Verilated.set_callback(cb)
    example.Verilated.finished = False

    a = Add()
    values = iter(range(100))
    limit = 1
    try:
        while not cb.finished:
            v = next(values)
            print('Assigning', v)
            a.value = v
            a.cycle()
            limit += 1
            if limit > 1000:
                assert False, "hit limit"
        assert cb.finished == True
        assert cb.stopped == False
        assert cb.fataled == False
        assert v == 42

        assert example.Verilated.finished == False, "The custom callback should not touch this global variable"
        assert example2.Verilated.finished == False, "It should also not touch other global variables"
        example.Verilated.set_callback(None)
        a.value = 42
        a.cycle()
        assert example.Verilated.finished == True, "The default callback sets the global variable"
        assert example2.Verilated.finished == False, "and keep its hand of other global variables"

    except example.VerilatedException:
        assert False


def test_exception():
    """Tests whether the """
    try:
        example.VerilatedCallback().on_fatal(__file__, 1337, "test function", "example oops")
        assert False
    except example.VerilatedException:
        assert True
    except example2.VerilatedException:
        assert False
    except example3.VerilatedException:
        assert False

    try:
        example2.VerilatedCallback().on_fatal(__file__, 1337, "test function", "example2 oops")
        assert False
    except example.VerilatedException:
        assert False
    except example2.VerilatedException:
        assert True
    except example3.VerilatedException:
        assert False

    try:
        example3.VerilatedCallback().on_fatal(__file__, 1337, "test function", "example3 oops")
        assert False
    except example.VerilatedException:
        assert False
    except example2.VerilatedException:
        assert False
    except example3.VerilatedException:
        assert True


def test_arguments():
    """Test passing arguments to a Verilated module"""
    example.Verilated.parse_arguments(["whatever", "+verilator+seed+4", "+verilator+debug"])
    args = example.Verilated.arguments
    assert args[0] == "whatever"
    assert args[1] == "+verilator+seed+4"
    assert args[2] == "+verilator+debug"


def test_assertions():
    """Test setting global assertions"""
    assert 'assertions' in dir(example.Verilated)

    example.Verilated.assertions = False
    assert example.Verilated.assertions == False
    example.Verilated.assertions = True
    assert example.Verilated.assertions == True
    example.Verilated.assertions = False
    assert example.Verilated.assertions == False


def test_calculate_unused_signals():
    """Test settings global calculate_unused_signals"""
    assert 'calculate_unused_signals' in dir(example.Verilated)

    example.Verilated.calculate_unused_signals = False
    assert example.Verilated.calculate_unused_signals == False
    example.Verilated.calculate_unused_signals = True
    assert example.Verilated.calculate_unused_signals == True
    example.Verilated.calculate_unused_signals = False
    assert example.Verilated.calculate_unused_signals == False


def test_debug_level():
    """Test setting global debug_level"""
    assert 'debug_level' in dir(example.Verilated)

    example.Verilated.debug_level = 0
    assert example.Verilated.debug_level == (0 if example.Verilated.debug_available else 0)
    example.Verilated.debug_level = 4
    assert example.Verilated.debug_level == (4 if example.Verilated.debug_available else 0)
    example.Verilated.debug_level = 2
    assert example.Verilated.debug_level == (2 if example.Verilated.debug_available else 0)
    example.Verilated.debug_level = 0
    assert example.Verilated.debug_level == (0 if example.Verilated.debug_available else 0)


def test_finished():
    """Test setting global finished"""
    assert 'finished' in dir(example.Verilated)

    example.Verilated.finished = False
    assert example.Verilated.finished == False
    example.Verilated.finished = True
    assert example.Verilated.finished == True
    example.Verilated.finished = False
    assert example.Verilated.finished == False


def test_product_name_version():
    """Test fetching product_name and product_version"""
    assert 'product_name' in dir(example.Verilated)
    assert 'product_version' in dir(example.Verilated)

    assert 'Verilator' in example.Verilated.product_name
    version = example.Verilated.product_version.split(' ', 1)
    float(version[0])


def test_threads_profiling_properties():
    """Test setting global profiling threads option"""
    assert 'profiling_threads_filename' in dir(example.Verilated)
    assert 'profiling_threads_start' in dir(example.Verilated)
    assert 'profiling_threads_window' in dir(example.Verilated)

    example.Verilated.profiling_threads_filename = "test.dat"
    assert example.Verilated.profiling_threads_filename == "test.dat"
    example.Verilated.profiling_threads_filename = "profile_threads.dat"
    assert example.Verilated.profiling_threads_filename == "profile_threads.dat"

    example.Verilated.profiling_threads_start = 4
    assert example.Verilated.profiling_threads_start == 4
    example.Verilated.profiling_threads_start = 0
    assert example.Verilated.profiling_threads_start == 0
    example.Verilated.profiling_threads_start = 1
    assert example.Verilated.profiling_threads_start == 1

    example.Verilated.profiling_threads_window = 9
    assert example.Verilated.profiling_threads_window == 9
    example.Verilated.profiling_threads_window = 0
    assert example.Verilated.profiling_threads_window == 0
    example.Verilated.profiling_threads_window = 1
    assert example.Verilated.profiling_threads_window == 1


def test_reset_randomized():
    """Test setting global randomized reset option"""
    assert 'reset_randomized' in dir(example.Verilated)

    example.Verilated.reset_randomized = False
    assert example.Verilated.reset_randomized == False
    example.Verilated.reset_randomized = True
    assert example.Verilated.reset_randomized == True
    example.Verilated.reset_randomized = False
    assert example.Verilated.reset_randomized == False


def test_example_vadd():
    """Test use of an a Verilated module: an adder (1st module: example)"""
    a = example.Vadd()
    a.clk = 0
    a.rst = 1
    a.eval()
    a.clk = 1
    a.eval()
    a.clk = 0
    a.rst = 0
    a.eval()
    a.value = 5
    assert a.result == 0
    a.clk = 1
    a.eval()
    assert a.result == 6


def test_example2_vadd():
    """Test use of a Verilated module using the convenience wrapper (2nd module: example2)"""
    example2.Verilated.finished = False
    example2.Verilated.set_callback(None)

    a = Add2()
    a.trace_start("test_example.vcd")
    a.rst = 1
    a.cycle()
    a.rst = 0
    a.value = 11
    a.cycle()
    assert a.result == 13
    a.cycle()
    a.value = 42
    a.cycle()
    try:
        a.cycle()
    except example2.VerilatedException as e:
        print("An exception was thrown: {}".format(repr(e)))
    a.trace_stop()
    os.unlink("test_example.vcd")


def test_multiple_python_modules_independence():
    """Test independence between multiple python modules both containing Verilated modules"""
    example.Verilated.finished = False
    example2.Verilated.finished = False
    example.Verilated.set_callback(None)
    example2.Verilated.set_callback(None)

    a1 = Add()
    a2 = Add2()

    a1.rst, a2.rst = 1, 1
    a1.cycle()
    a2.cycle()

    a1.rst, a2.rst = 0, 0
    a1.cycle()
    a2.cycle()

    a1.value = 42
    a1.cycle()
    a2.cycle()

    assert example.Verilated.finished == True
    assert example2.Verilated.finished == False


def test_vcd():
    """Test methods of VerilatedVcd object"""
    vcd = example3.VerilatedVcd()
    vcd.set_time_unit("ns")
    vcd.set_time_resolution("ns")
    # vcd.rollover_MB(1)
    assert vcd.closed
    try:
        os.unlink("file.vcd")
    except FileNotFoundError:
        pass
    assert not os.path.exists("file.vcd")
    vcd.open("file.vcd")
    vcd.dump(0)
    # vcd.open_next(True)
    vcd.dump(1)
    vcd.flush()
    vcd.close()
    assert vcd.closed
    assert os.path.exists("file.vcd")
    try:
        os.unlink("file.vcd")
    except FileNotFoundError:
        pass


def test_fst():
    """Test methods of VerilatedFst object"""
    fst= example3.VerilatedFst()
    fst.set_time_unit("ns")
    fst.set_time_resolution("ns")
    # vcd.rollover_MB(1)
    assert fst.closed
    try:
        os.unlink("file.fst")
    except FileNotFoundError:
        pass
    assert not os.path.exists("file.fst")
    fst.open("file.fst")
    fst.dump(0)
    fst.dump(1)
    fst.flush()
    fst.close()
    assert fst.closed
    assert os.path.exists("file.fst")
    try:
        os.unlink("file.fst")
    except FileNotFoundError:
        pass


def test_width_1():
    """Test basic properties of a 1 bit signal"""
    a = Add2()

    a.in1 = 1
    a.cycle()
    assert a.out1 == 1, a.out1

    a.in1 = 0
    a.cycle()
    assert a.out1 == 0, a.out1

    a.in1 = 1
    a.cycle()
    assert a.out1 == 1, a.out1

    try:
        a.in1 = -1
        assert False
    except ValueError:
        pass


def test_width_8():
    """Test basic properties of an 8 bit signal"""
    a = Add2()

    a.in8 = 1
    a.cycle()
    assert a.out8 == 1, a.out8

    a.in8 = 0
    a.cycle()
    assert a.out8 == 0, a.out8

    a.in8 = 1
    a.cycle()
    assert a.out8 == 1, a.out8

    for i in (0, 4, 9, 45, 58, 0x80, 0xe0, 0xfe, 0xff):
        a.in8 = i
        a.cycle()
        assert a.out8 == i, (a.out8, i, )

        if i != 0:
            try:
                a.in8 = -i
                assert False
            except ValueError:
                pass


def test_width_16():
    """Test basic properties of a 16 bit signal"""
    a = Add2()

    a.in16 = 1
    a.cycle()
    assert a.out16 == 1, a.out16

    a.in16 = 0
    a.cycle()
    assert a.out16 == 0, a.out16

    a.in16 = 1
    a.cycle()
    assert a.out16 == 1, a.out16

    for i in (0, 0x10, 0x100, 0x500, 0x1000, 0x8000, 0xff00, 0xffff):
        a.in16 = i
        a.cycle()
        assert a.out16 == i, (a.out16, i, )

        if i != 0:
            try:
                a.in16 = -i
                assert False
            except ValueError:
                pass


def test_width_32():
    """Test basic properties of a 32 bit signal"""
    a = Add2()

    a.in32 = 1
    a.cycle()
    assert a.out32 == 1, a.out32

    a.in32 = 0
    a.cycle()
    assert a.out32 == 0, a.out32

    a.in32 = 1
    a.cycle()
    assert a.out32 == 1, a.out32

    for i in (0, 0x10, 0x100, 0x500, 0x1000, 0x8000, 0xff00, 0xffff,
              0x10000, 0x100000, 0x1000000, 0x10000000, 0xf0000000, 0xff000000,
              0xffffffff):
        a.in32 = i
        a.cycle()
        assert a.out32 == i, (a.out32, i, )

        if i != 0:
            try:
                a.in32 = -i
                assert False
            except ValueError:
                pass


def test_width_64():
    """Test basic properties of a 64 bit signal"""
    a = Add2()

    a.in64 = 1
    a.cycle()
    assert a.out64 == 1, a.out64

    a.in64 = 0
    a.cycle()
    assert a.out64 == 0, a.out64

    a.in64 = 1
    a.cycle()
    assert a.out64 == 1, a.out64

    for i in (0, 0x10, 0x100, 0x500, 0x1000, 0x8000, 0xff00, 0xffff,
              0x10000, 0x100000, 0x1000000, 0x10000000, 0xf0000000, 0xff000000,
              0xffffffff,
              0x100000000, 0x1000000000, 0x10000000000, 0x1000000000000000,
              0x8000000000000000, 0xffffffffffffffff):
        a.in64 = i
        a.cycle()
        assert a.out64 == i, (a.out64, i, )

        if i != 0:
            try:
                a.in64 = -i
                assert False
            except ValueError:
                pass


def test_width_128():
    """Test basic properties of a 128 bit signal"""
    a = Add2()

    a.in128 = 1
    a.cycle()
    assert a.out128 == 1, a.out128

    a.in128 = 0
    a.cycle()
    assert a.out128 == 0, a.out128

    a.in128 = 1
    a.cycle()
    assert a.out128 == 1, a.out128

    for i in (0, 0x10, 0x100, 0x500, 0x1000, 0x8000, 0xff00, 0xffff,
              0x10000, 0x100000, 0x1000000, 0x10000000, 0xf0000000, 0xff000000,
              0xffffffff,
              0x100000000, 0x1000000000, 0x10000000000, 0x1000000000000000,
              0x8000000000000000, 0xffffffffffffffff, 0xffffffffffffffffffffffffff):
        a.in128 = i
        a.cycle()
        assert a.out128 == i, (hex(a.out128), hex(i), )

        if i != 0:
            try:
                a.in128 = -i
                assert False
            except ValueError:
                pass


def test_width_128_2():
    """Test basic properties of an 128 bit signal (which is defined with start/end bit inex != 0)"""
    a = Add2()

    a.in128_2 = 1
    a.cycle()
    assert a.out128_2 == 1, a.out128_2

    a.in128_2 = 0
    a.cycle()
    assert a.out128_2 == 0, a.out128_2

    a.in128_2 = 1
    a.cycle()
    assert a.out128_2 == 1, a.out128_2

    for i in (0, 0x10, 0x100, 0x500, 0x1000, 0x8000, 0xff00, 0xffff,
              0x10000, 0x100000, 0x1000000, 0x10000000, 0xf0000000, 0xff000000,
              0xffffffff,
              0x100000000, 0x1000000000, 0x10000000000, 0x1000000000000000,
              0x8000000000000000, 0xffffffffffffffff, 0xffffffffffffffffffffffffff):
        a.in128_2 = i
        a.cycle()
        assert a.out128_2 == i, (hex(a.out128_2), hex(i), )

        if i != 0:
            try:
                a.in128_2 = -i
                assert False
            except ValueError:
                pass


def test_signed_width_1():
    """Test properties of a signed 1 bit signal"""
    a = Add2()

    a.in1_s = -1
    a.cycle()
    assert a.out1_s == -1


def test_unsigned_width_1():
    """Test properties of an unsigned 1 bit signal"""
    a = Add2()

    try:
        a.in1 = -1
        assert False
    except ValueError:
        pass


def test_overflow_width_1():
    """Test overflow of an unsigned 1 bit signal"""
    a = Add2()

    try:
        a.in1 = 0xffffffffffffffffffffffffff
        assert False
    except OverflowError:
        pass


def test_signed_width_8():
    """Test properties of a signed 8 bit signal"""
    a = Add2()

    a.in8_s = -1
    a.cycle()
    assert a.out8_s == -1


def test_unsigned_width_8():
    """Test properties of an unsigned 8 bit signal"""
    a = Add2()

    try:
        a.in8 = -1
        assert False
    except ValueError:
        pass


def test_overflow_width_8():
    """Test overflow of an unsigned 8 bit signal"""
    a = Add2()

    try:
        a.in8 = 0xffffffffffffffffffffffffff
        assert False
    except OverflowError:
        pass


def test_signed_width_16():
    """Test properties of a signed 16 bit signal"""
    a = Add2()

    a.in16_s = -1
    a.cycle()
    assert a.out16_s == -1


def test_unsigned_width_16():
    """Test properties of an unsigned 16 bit signal"""
    a = Add2()

    try:
        a.in16 = -1
        assert False
    except ValueError:
        pass


def test_overflow_width_16():
    """Test overflow of an unsigned 16 bit signal"""
    a = Add2()

    try:
        a.in16 = 0xffffffffffffffffffffffffff
        assert False
    except OverflowError:
        pass


def test_signed_width_32():
    """Test properties of a signed 32 bit signal"""
    a = Add2()

    a.in32_s = -1
    a.cycle()
    assert a.out32_s == -1


def test_unsigned_width_32():
    """Test properties of an unsigned 32 bit signal"""
    a = Add2()

    try:
        a.in32 = -1
        assert False
    except ValueError:
        pass


def test_overflow_width_32():
    """Test overflow of an unsigned 32 bit signal"""
    a = Add2()

    try:
        a.in32 = 0xffffffffffffffffffffffffff
        assert False
    except OverflowError:
        pass


def test_signed_width_64():
    """Test properties of a signed 64 bit signal"""
    a = Add2()

    a.in64_s = -1
    a.cycle()
    assert a.out64_s == -1


def test_unsigned_width_64():
    """Test properties of an unsigned 64 bit signal"""
    a = Add2()

    try:
        a.in64 = -1
        assert False
    except ValueError:
        pass


def test_overflow_width_64():
    """Test overflow of an unsigned 64 bit signal"""
    a = Add2()

    try:
        a.in1 = 0xffffffffffffffffffffffffff
        assert False
    except OverflowError:
        pass


def test_signed_width_128():
    """Test properties of a signed 128 bit signal"""
    a = Add2()

    a.in128_s = -1
    a.cycle()
    assert a.out128_s == -1


def test_unsigned_width_128():
    """Test properties of an unsigned 128 bit signal"""
    a = Add2()

    try:
        a.in128 = -1
        assert False
    except ValueError:
        pass


def test_overflow_width_128():
    """Test overflow of an unsigned 128 bit signal"""
    a = Add2()

    try:
        a.in128 = 0xffffffffffffffffffffffffffffffffffff
        assert False
    except OverflowError:
        pass


def main():
    test_functions = {n:f for (n, f) in globals().items() if n.startswith('test_')}
    results = {}
    for n, tf in test_functions.items():
        print("{:=^80}".format(' ' + n + ' '))
        try:
            tf()
            results[n] = "SUCCESS"
        except Exception:
            results[n] = "FAILURE"
            print('FAILURE')
        print("{:=^80}".format(''))
        print()

    successes = list(n for (n, r) in results.items() if r == "SUCCESS")
    failures = list(n for (n, r) in results.items() if r == "FAILURE")
    assert len(successes) + len(failures) == len(results)
    print()
    print("TOTAL: {} SUCCESS: {} FAILURE: {}".format(len(results), len(successes), len(failures)))
    if failures:
        print("The following tests failed:")
        for f in failures:
            print("-", f)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
