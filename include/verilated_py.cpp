// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Definition of global Verilator python wrappers
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************

#include "verilated_py.h"

#include "verilated.h"
#include "verilatedos.h"

#include <pybind11/stl.h>

#include <cstdarg>
#include <cstdint>
#include <exception>
#include <string>
#include <utility>
#include <vector>

#pragma GCC visibility push(hidden)

namespace py = pybind11;

namespace vl_py {
namespace impl {
py::int_ read_port(const vluint32_t* words, size_t width, bool is_signed) {
    size_t msb = width - 1;
    auto w = words + msb / 32;
    py::int_ i(*w);
    py::int_ s(32);
    while (--w >= words) {
        i = (i << s) | py::int_(*w);
    }

    if (is_signed && (words[msb / 32] >> (msb % 32))) { //Negative
        py::int_ one(1);
        py::int_ msk(one << py::int_(msb));
        return (i & (msk - one)) - msk;
    }

    return i;
}

void write_port(vluint32_t* words, size_t width, py::int_ v, bool is_signed) {
    py::int_ s(32);
    py::int_ msk(0xFFFFFFFF);
    for (auto w = words; w < words + (width + 31) / 32; w++) {
        *w = py::int_(v & msk);
        v = v >> s;
    }
    int i = v;
    if (!(i == 0 || (is_signed && i == -1))) {
        PyErr_SetString(PyExc_OverflowError, "Integer overflow when assigning to wide port");
        throw py::error_already_set();
    }
}
} // namespace impl

py::object s_pymodule;

class VerilatedException : public std::exception {
std::string m_msg;
py::handle m_owner;
public:
    VerilatedException(const std::string& msg, py::handle owner)
        : std::exception{}
        , m_msg(msg)
        , m_owner(owner){
    }
    const char* what() const noexcept override {
        return m_msg.c_str();
    }
    py::handle owner() const noexcept {
        return m_owner;
    }
};

class VLCallback {
public:
    VLCallback() {}
    virtual ~VLCallback() {}
    virtual void on_finish(const char* filename, int linenum, const char* /*hier*/) {
        VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
            "- %s:%d: Verilog $finish\n", filename, linenum);
        if (Verilated::gotFinish()) {
            VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
                "- %s:%d: Second verilog $finish\n", filename, linenum);
            on_flush();
            throw VerilatedException("Second verilog $finish", s_pymodule);
        }
        Verilated::gotFinish(true);
    }

    virtual void on_stop(const char* filename, int linenum, const char* hier) {
        Verilated::gotFinish(true);
        on_flush();
        on_fatal(filename, linenum, hier, "Verilog $stop");
    }

    virtual void on_fatal(const char* filename, int linenum, const char* hier, const char* msg) {
        Verilated::gotFinish(true);
        VL_PRINTF(  // Not VL_PRINTF_MT, already on main thread
            "%%Error: %s:%d: %s\n", filename, linenum, msg);
        on_flush();
        throw VerilatedException(msg, s_pymodule);
    }

    virtual void on_flush() {
    }

    virtual void on_print(const char* txt) {
        py::print(py::str(txt), py::arg("end")="");
    }
};

class PyVLCallback : public VLCallback {
public:
    using VLCallback::VLCallback;
    ~PyVLCallback() override {}
    void on_finish(const char* filename, int linenum, const char* hier) override {
        PYBIND11_OVERLOAD(
            void,                           // Return type
            VLCallback,                     // Parent class
            on_finish,                      // Name of function in C++ (must match Python name)
            filename, linenum, hier         // Argument(s)
        );
    }

    void on_stop(const char* filename, int linenum, const char* hier) override {
        PYBIND11_OVERLOAD(
            void,                           // Return type
            VLCallback,                     // Parent class
            on_stop,                        // Name of function in C++ (must match Python name)
            filename, linenum, hier         // Argument(s)
        );
    }

    void on_fatal(const char* filename, int linenum, const char* hier, const char* msg) override {
        PYBIND11_OVERLOAD(
            void,                           // Return type
            VLCallback,                     // Parent class
            on_fatal,                       // Name of function in C++ (must match Python name)
            filename, linenum, hier, msg    // Argument(s)
        );
    }

    void on_flush() override {
        PYBIND11_OVERLOAD(
            void,                           // Return type
            VLCallback,                     // Parent class
            on_flush,                       // Name of function in C++ (must match Python name)
                                            // Argument(s)
        );
    }

    void on_print(const char* txt) override {
        PYBIND11_OVERLOAD(
            void,                           // Return type
            VLCallback,                     // Parent class
            on_print,                       // Name of function in C++ (must match Python name)
            txt                             // Argument(s)
        );
    }
};

static py::object s_vl_callback;

static void vl_callback_flush() {
    s_vl_callback.attr("on_flush")();
}

static void set_callback(py::module m, py::object obj) {
    if (obj.is_none()) {
         s_vl_callback = m.attr("VerilatedCallback")();
         Verilated::flushCb(vl_callback_flush);
    } else {
        s_vl_callback = obj;
    }
}


namespace impl {

struct {
    std::vector<std::string> strings;
    std::vector<const char*> c_strings;
} args_buffer;

// Helper function to add documentation on static properties
static void attr_doc(const py::object& o, const char* name, const char* doc) {
    auto attr = o.attr(name);
    std::string s = std::string("\n\n.. data:: ") + name + "\n    :annotation: = "
        + py::cast<std::string>(py::repr(attr)) + "\n\n    " + doc;
    o.doc() = py::cast<std::string>(o.doc()) + s;
}
}

void declare_globals(py::module& m) {
    using namespace impl;

    s_pymodule = m;

    /* Register the VerilatedException exception:
     * Because the catch block will confuse VerilatedException objects from different Verilated python modules,
     * differentiate between them by using the current module.
     */
    static py::exception<VerilatedException> ex(m, "VerilatedException");
    py::register_exception_translator([](std::exception_ptr p) {
        try {
            if (p) std::rethrow_exception(p);
        } catch (const VerilatedException& e) {
            if (!e.owner().equal(s_pymodule)) {
                std::rethrow_exception(p);
            }
            ex(e.what());
        }
    });

    py::class_<VLCallback, PyVLCallback, std::shared_ptr<VLCallback>> vl_class_callback(m, "VerilatedCallback", py::module_local{});
    vl_class_callback
        .def(py::init<>())
        .def("on_finish", &VLCallback::on_finish, py::arg("filename"), py::arg("linenum"), py::arg("hier"),
            "Routine to call for $finish.")
        .def("on_stop", &VLCallback::on_stop, py::arg("filename"), py::arg("linenum"), py::arg("hier"),
            "Routine to call for $stop.")
        .def("on_fatal", &VLCallback::on_fatal, py::arg("filename"), py::arg("linenum"), py::arg("hier"), py::arg("msg"),
            "Routine to call for fatal messages.")
        .def("on_flush", &VLCallback::on_flush,
            "Flush all streams.")
        .def("on_print", &VLCallback::on_print,
            "Routine to call when Verilator wants to print something.");

    m.def("VL_THREAD_ID", &VL_THREAD_ID);

    py::class_<VerilatedMutex> vl_class_mutex(m, "VerilatedMutex", py::module_local{});
    vl_class_mutex
        .def(py::init<>())
        .def("lock", &VerilatedMutex::lock,
            "Try to acquire the lock by spinning.\n"
            "If the wait is short, avoids a trap to the OS plus OS scheduler overhead.")
        .def("unlock", &VerilatedMutex::unlock,
            "Release/unlock mutex")
        .def("try_lock", &VerilatedMutex::try_lock,
            "Try to acquire mutex.  Returns true on success, and false on failure.");

    py::class_<VerilatedModule> vl_class_verilated_module(m, "VerilatedModule", py::module_local{});
    vl_class_verilated_module
        .def_property_readonly("name", &VerilatedModule::name,
            "Name of module");

    py::class_<Verilated>vl_class_verilated(m, "Verilated", "Verilator global static information class", py::module_local{});
    vl_class_verilated.def_property_static("reset_randomized",
        [](py::object) {return Verilated::randReset();},
        [](py::object, int v) { Verilated::randReset(v);});
    attr_doc(vl_class_verilated, "reset_randomized",
        "Select initial value of otherwise uninitialized signals.\n"
        "    0 = Set to zeros\n"
        "    1 = Set all bits to one\n"
        "    2 = Randomize all bits");
    vl_class_verilated.def_property_static("debug_level",
        [](py::object) {return Verilated::debug();},
        [](py::object, int v) { Verilated::debug(v);});
    attr_doc(vl_class_verilated, "debug_level",
        "Debug level of internal verilated code.\n"
        "    When multithreaded, this may not immediately react to another thread changing the level (no mutex)");
    vl_class_verilated.def_property_readonly_static("debug_available",
        [](py::object) {
#           ifdef VL_DEBUG
                return true;
#           else
                return false;
#           endif
    });
    attr_doc(vl_class_verilated, "debug_available",
        "Check whether the Verilated module has debug support");
    vl_class_verilated.def_property_static("calculate_unused_signals",
        [](py::object) {return Verilated::calcUnusedSigs();},
        [](py::object, int v) { Verilated::calcUnusedSigs(v);});
    attr_doc(vl_class_verilated, "calculate_unused_signals",
        "Enable calculation of unused signals");
    vl_class_verilated.def_property_static("finished",
        [](py::object) {return Verilated::gotFinish();},
        [](py::object, bool v) { Verilated::gotFinish(v);});
    attr_doc(vl_class_verilated, "finished", "Did the simulation $finish?");
    vl_class_verilated.def_property_static("assertions",
        [](py::object) {return Verilated::assertOn();},
        [](py::object, bool v) { Verilated::assertOn(v);});
    attr_doc(vl_class_verilated, "assertions", "Enable/disable assertions");
    vl_class_verilated.def_property_static("vpi_error_fatal",
        [](py::object) {return Verilated::fatalOnVpiError();},
        [](py::object, bool v) { Verilated::fatalOnVpiError(v);});
    attr_doc(vl_class_verilated, "assertions", "Enable/disable vpi fatal");
    vl_class_verilated.def_property_static("profiling_threads_start",
        [](py::object) {return Verilated::profThreadsStart();},
        [](py::object, vluint64_t v) { Verilated::profThreadsStart(v);});
    attr_doc(vl_class_verilated, "profiling_threads_start", "When using --prof-threads, Verilator will wait until this time,\n"
        "    then start the profiling warmup. Set to 0 to disable threads profiling.");
    vl_class_verilated.def_property_static("profiling_threads_window",
        [](py::object) {return Verilated::profThreadsWindow();},
        [](py::object, vluint64_t v) { Verilated::profThreadsWindow(v);});
    attr_doc(vl_class_verilated, "profiling_threads_window", "When using --prof-threads, Verilator will warm up the profiling\n"
        "    for this number of eval() calls, then will capture the profiling of this number of eval() calls.");
    vl_class_verilated.def_property_static("profiling_threads_filename",
        [](py::object) {return Verilated::profThreadsFilenamep();},
        [](py::object, const char* v) { Verilated::profThreadsFilenamep(v);});
    attr_doc(vl_class_verilated, "profiling_threads_filename", "When using --prof-threads, the filename to dump to.");
    vl_class_verilated.def_property_readonly_static("product_name",
        [](py::object) {return Verilated::productName();});
    attr_doc(vl_class_verilated, "product_name", "Product name for (at least) VPI");
    vl_class_verilated.def_property_readonly_static("product_version",
        [](py::object) {return Verilated::productVersion();});
    attr_doc(vl_class_verilated, "product_version", "Product version for (at least) VPI");
    vl_class_verilated.def_static("traceEverOn", &Verilated::traceEverOn, py::arg("flag"),
            "Allow traces to at some point be enabled (disables some optimizations)")
        .def_static("set_callback", [m](py::object obj) {set_callback(m, obj); }, py::arg("callback"), "Set callback")
        .def_static("quiesce", &Verilated::quiesce,
            "When multithreaded, quiesce the model to prepare for trace/saves/coverage\n"
            "This may only be called when no locks are held.")
        .def_static("dump_internals", &Verilated::internalsDump,
            "For debugging, print much of the Verilator internal state.\n"
            "The output of this function may change in future\n"
            "releases - contact the authors before production use.")
        .def_static("dump_scopes", &Verilated::scopesDump,
            "For debugging, print text list of all scope names with\n"
            "dpiImport/Export context.  This function may change in future\n"
            "releases - contact the authors before production use.")
        .def_static("parse_arguments", [](std::vector<std::string>& args) {
            impl::args_buffer.strings = args;
            impl::args_buffer.c_strings.clear();
            impl::args_buffer.c_strings.reserve(args.size());
            for (const std::string& s: impl::args_buffer.strings) {
                impl::args_buffer.c_strings.push_back(s.c_str());
            }
            Verilated::commandArgs(impl::args_buffer.c_strings.size(), impl::args_buffer.c_strings.data());
        });
    vl_class_verilated.def_property_readonly_static("arguments", [](py::object) {
        std::vector<std::string> result;
        const auto vl_args = Verilated::getCommandArgs();
        result.reserve(vl_args->argc);
        for (size_t arg_i = 0; arg_i < vl_args->argc; ++arg_i) {
            result.push_back(vl_args->argv[arg_i]);
        }
        return result;
    });

#if VM_TRACE_VCD
    py::class_<VerilatedVcdC> vl_class_verilated_vcd_c(m, "VerilatedVcd", py::module_local{});
    vl_class_verilated_vcd_c
        .def(py::init<>())
        .def_property_readonly("closed", [](const VerilatedVcdC& o) { return !o.isOpen();},
            "Is file closed?")
        .def("open", &VerilatedVcdC::open,
            py::arg("filename"),
            "Open a new VCD file.\n"
            "This includes a complete header dump each time it is called,\n"
            "just as if this object was deleted and reconstructed.")
        .def("open_next", &VerilatedVcdC::openNext,
            py::arg("inc_filename"),
            "Continue a VCD dump by rotating to a new file name.\n"
            "The header is only in the first file created, this allows\n"
            "\"cat\" to be used to combine the header plus any number of data files.")
        .def("rollover_MB", &VerilatedVcdC::rolloverMB,
            py::arg("rollover_MB"),
            "Set size in megabytes after which new file should be created")
        .def("close", &VerilatedVcdC::close,
            "Close the file")
        .def("flush", &VerilatedVcdC::flush,
            "Flush any remaining data to this file")
        .def("dump", py::overload_cast<vluint64_t>(&VerilatedVcdC::dump),
            py::arg("timestamp"),
            "Write one cycle of dump data")
        .def("set_time_unit", py::overload_cast<const std::string&>(&VerilatedVcdC::set_time_unit),
            py::arg("unit"),
            "Set time units (s/ms, defaults to ns)\n"
            "See also VL_TIME_PRECISION, and VL_TIME_MULTIPLIER in verilated.h")
        .def("set_time_resolution", py::overload_cast<const std::string&>(&VerilatedVcdC::set_time_resolution),
            py::arg("unit"),
            "Set time resolution (s/ms, defaults to ns)\n"
            "See also VL_TIME_PRECISION, and VL_TIME_MULTIPLIER in verilated.h");
#endif
#if VM_TRACE_FST
    py::class_<VerilatedFstC> vl_class_verilated_fst_c(m, "VerilatedFst", py::module_local{});
    vl_class_verilated_fst_c
        .def(py::init<>())
        .def_property_readonly("closed", [](const VerilatedFstC& o) { return !o.isOpen();},
            "Is file closed?")
        .def("open", &VerilatedFstC::open,
            py::arg("filename"),
            "Open a new FST file")
        .def("close", &VerilatedFstC::close,
            "Close dump")
        .def("flush", &VerilatedFstC::flush,
            "Flush dump")
        .def("dump", py::overload_cast<vluint64_t>(&VerilatedFstC::dump),
            py::arg("timestamp"),
            "Write one cycle of dump data")
        .def("set_time_unit", py::overload_cast<const std::string&>(&VerilatedFstC::set_time_unit),
            py::arg("unit"),
            "Set time units (s/ms, defaults to ns)\n"
            "See also VL_TIME_PRECISION, and VL_TIME_MULTIPLIER in verilated.h")
        .def("set_time_resolution", py::overload_cast<const std::string&>(&VerilatedFstC::set_time_resolution),
            py::arg("unit"),
            "Set time resolution (s/ms, defaults to ns)\n"
            "See also VL_TIME_PRECISION, and VL_TIME_MULTIPLIER in verilated.h");
#endif

#if VM_COVERAGE
    py::class_<VerilatedCov> vl_class_coverage(m, "VerilatedCov", py::module_local{});
    vl_class_coverage
        .def_static("write", &VerilatedCov::write,
            py::arg("filename"),
            "Write out coverage data to specified file")
        .def_static("clear", &VerilatedCov::clear,
            "Clear coverage points (and call delete on all items)")
        .def_static("clearNonMatch", &VerilatedCov::clearNonMatch,
            py::arg("match"),
            "Clear items not matching the provided string")
        .def_static("zero", &VerilatedCov::zero,
            "Zero coverage points");
#endif

    set_callback(m, py::none());
    m.add_object("_cleanup", py::capsule([]() {
        // vl_callback must not be removed from flushCb because
        // there is only one callback active at one time using `set_callback`
        fflush(stdout);
        s_vl_callback.release().dec_ref();
        s_pymodule.release().dec_ref();
    }));
}

int vl_vprintf(const char* fmt, va_list args) {
    char buf[256];
    const int len = VL_VSNPRINTF(buf, sizeof(buf), fmt, args);
    py::str s(buf, len);
    s_vl_callback.attr("on_print")(buf);
    return len;
}

int vl_printf(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    const int len = vl_vprintf(fmt, args);
    va_end(args);
    return len;
}

} // namespace vl_py

void vl_finish(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    assert(static_cast<bool>(vl_py::s_vl_callback));
    vl_py::s_vl_callback.attr("on_finish")(filename, linenum, hier);
}

void vl_stop(const char* filename, int linenum, const char* hier) VL_MT_UNSAFE {
    assert(static_cast<bool>(vl_py::s_vl_callback));
    vl_py::s_vl_callback.attr("on_stop")(filename, linenum, hier);
}

void vl_fatal(const char* filename, int linenum, const char* hier, const char* msg) VL_MT_UNSAFE {
    assert(static_cast<bool>(vl_py::s_vl_callback));
    vl_py::s_vl_callback.attr("on_fatal")(filename, linenum, hier, msg);
}

#pragma GCC visibility pop
