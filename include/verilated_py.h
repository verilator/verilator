// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2003-2018 by Wilson Snyder. This program is free software; you can
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
/// \brief Verilator: Common include for verilator python wrappers
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_PY_H_
#define _VERILATED_PY_H_ 1 ///< Header Guard

#include "verilated.h"
#include <pybind11/pybind11.h>
#ifdef VM_TRACE
#ifdef VM_TRACE_FST
#include "verilated_fst_c.h"
#else
#include "verilated_vcd_c.h"
#endif
#endif

namespace vl_py {

inline void declare_globals(pybind11::module& m) {
    m.def("VL_THREAD_ID", &VL_THREAD_ID);
    pybind11::class_<VerilatedMutex>(m, "VerilatedMutex")
        .def("lock", &VerilatedMutex::lock)
        .def("unlock", &VerilatedMutex::unlock);
    pybind11::class_<VerilatedModule>(m, "VerilatedModule")
        .def("name", &VerilatedModule::name);
    pybind11::class_<Verilated>(m, "Verilated")
        .def_static("randReset", pybind11::overload_cast<int>(&Verilated::randReset))
        .def_static("randReset", pybind11::overload_cast<>(&Verilated::randReset))
        .def_static("debug", pybind11::overload_cast<int>(&Verilated::debug))
        .def_static("debug", pybind11::overload_cast<>(&Verilated::debug))
        .def_static("calcUnusedSigs", pybind11::overload_cast<bool>(&Verilated::calcUnusedSigs))
        .def_static("calcUnusedSigs", pybind11::overload_cast<>(&Verilated::calcUnusedSigs))
        .def_static("gotFinish", pybind11::overload_cast<bool>(&Verilated::gotFinish))
        .def_static("gotFinish", pybind11::overload_cast<>(&Verilated::gotFinish))
        .def_static("traceEverOn", &Verilated::traceEverOn)
        .def_static("assertOn", pybind11::overload_cast<bool>(&Verilated::assertOn))
        .def_static("assertOn", pybind11::overload_cast<>(&Verilated::assertOn))
        .def_static("fatalOnVpiError", pybind11::overload_cast<bool>(&Verilated::fatalOnVpiError))
        .def_static("fatalOnVpiError", pybind11::overload_cast<>(&Verilated::fatalOnVpiError))
        .def_static("profThreadsStart", pybind11::overload_cast<vluint64_t>(&Verilated::profThreadsStart))
        .def_static("profThreadsStart", pybind11::overload_cast<>(&Verilated::profThreadsStart))
        .def_static("profThreadsWindow", pybind11::overload_cast<vluint64_t>(&Verilated::profThreadsWindow))
        .def_static("profThreadsWindow", pybind11::overload_cast<>(&Verilated::profThreadsWindow))
        .def_static("profThreadsFilenamep", pybind11::overload_cast<const char*>(&Verilated::profThreadsFilenamep))
        .def_static("profThreadsFilenamep", pybind11::overload_cast<>(&Verilated::profThreadsFilenamep))
        .def_static("flushCall", &Verilated::flushCall)
        .def_static("productName", &Verilated::productName)
        .def_static("productVersion", &Verilated::productVersion)
        .def_static("quiesce", &Verilated::quiesce)
        .def_static("internalsDump", &Verilated::internalsDump)
        .def_static("scopesDump", &Verilated::scopesDump);
#ifdef VM_TRACE
#ifdef VM_TRACE_FST
    pybind11::class_<VerilatedFstC>(m, "VerilatedFstC")
        .def(pybind11::init<>())
        .def("isOpen", &VerilatedFstC::isOpen)
        .def("open", &VerilatedFstC::open)
        .def("close", &VerilatedFstC::close)
        .def("flush", &VerilatedFstC::flush)
        .def("dump", pybind11::overload_cast<vluint64_t>(&VerilatedFstC::dump))
        .def("set_time_unit", pybind11::overload_cast<const std::string&>(&VerilatedVcdC::set_time_unit))
        .def("set_time_resolution", pybind11::overload_cast<const std::string&>(&VerilatedVcdC::set_time_resolution));
#else
    pybind11::class_<VerilatedVcdC>(m, "VerilatedVcdC")
        .def(pybind11::init<>())
        .def("isOpen", &VerilatedVcdC::isOpen)
        .def("open", &VerilatedVcdC::open)
        .def("openNext", &VerilatedVcdC::openNext)
        .def("rolloverMB", &VerilatedVcdC::rolloverMB)
        .def("close", &VerilatedVcdC::close)
        .def("flush", &VerilatedVcdC::flush)
        .def("dump", pybind11::overload_cast<vluint64_t>(&VerilatedVcdC::dump))
        .def("set_time_unit", pybind11::overload_cast<const std::string&>(&VerilatedVcdC::set_time_unit))
        .def("set_time_resolution", pybind11::overload_cast<const std::string&>(&VerilatedVcdC::set_time_resolution));
#endif
#endif
}

} // namespace vl_py

#ifndef VL_PY_MODULE
#define VL_PY_MODULE(m, t) pybind11::class_<t, VerilatedModule>(m, #t) \
                            .def(pybind11::init<const char*>(), pybind11::arg("name") = "TOP")
#endif
#ifndef VL_PY_PORT
#define VL_PY_PORT(n, p) .def_readwrite(#p, &n::p)
#endif
#ifndef VL_PY_PARAM
#define VL_PY_PARAM(n, p) .def_readonly(#p, &n::p)
#endif
#ifndef VL_PY_FUNC
#define VL_PY_FUNC(n, f) .def(#f, &n::f)
#endif
#ifndef VL_PY_FUNC_STATIC
#define VL_PY_FUNC_STATIC(n, f) .def_static(#f, &n::f)
#endif
#ifndef VL_PY_FUNC_TRACE
#define VL_PY_FUNC_TRACE(n) .def("trace", &n::trace, pybind11::arg("tfp"), pybind11::arg("levels"), pybind11::arg("options") = 0)
#endif
#ifndef VL_PY_VAR
#define VL_PY_VAR(n, v) .def_readwrite(#v, &n::v)
#endif

#endif /*_VERILATED_PY_H_*/
