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
/// \brief Verilator: Common include for Verilator python wrappers
///
/// Code available from: http://www.veripool.org/verilator
///
//*************************************************************************


#ifndef _VERILATED_PY_H_
#define _VERILATED_PY_H_ 1 ///< Header Guard

#if VM_TRACE_VCD
#include "verilated_vcd_c.h"
#endif
#if VM_TRACE_FST
#include "verilated_fst_c.h"
#endif
#include "verilatedos.h"

#include <pybind11/pybind11.h>

#include <cstdarg>

namespace py = pybind11;

namespace vl_py {

void declare_globals(pybind11::module& m);

int vl_printf(const char* , ...);

int vl_vprintf(const char* fmt, va_list args);

namespace impl {
py::int_ read_port(const vluint32_t* words, size_t width, bool is_signed);

void write_port(vluint32_t* words, size_t width, py::int_ v, bool is_signed);

template <typename T, bool is_signed>
struct port_type;

template <typename T>
struct port_type<T, true> {
    using type = typename std::make_signed<T>::type;
};

template <typename T>
struct port_type<T, false> {
    using type = typename std::make_unsigned<T>::type;
};


} // namespace impl
} // namespace vl_py

#include <iostream>
#include <type_traits>

#define _SET_ERR(msg) PyErr_SetString(PyExc_TypeError, msg)


#define _VL_PY_ABS(X) ((X)>=0?(X):-(X))

#define _VL_PY_PORT_READ(n, p, msb, lsb, s) \
    [](n& module) { return static_cast<::vl_py::impl::port_type<decltype(n::p), s>::type>(module.p);}
#define _VL_PY_PORT_WRITE(n, p, msb, lsb, s) \
    [](n& module, py::int_ value) { \
        if (!s) { \
            if (_PyLong_Sign(value.ptr()) < 0) {\
                throw std::invalid_argument("Cannot assign a negative value to an unsigned port"); return; \
            } \
        } \
        module.p = static_cast<::vl_py::impl::port_type<decltype(n::p), s>::type>(value); \
        if (PyErr_Occurred()) { \
            throw py::error_already_set(); \
        } \
    }

#define _VL_PY_PORT_READ_W(n, p, msb, lsb, s) \
    [](const n& module) {return ::vl_py::impl::read_port(module.p, _VL_PY_ABS(msb-lsb), s);}
#define _VL_PY_PORT_WRITE_W(n, p, msb, lsb, s) \
    [](n& module, py::int_ value) { \
        if (!s) { \
            if (_PyLong_Sign(value.ptr()) < 0) {\
                throw std::invalid_argument("Cannot assign a negative value to an unsigned port"); return; \
            } \
        } \
        ::vl_py::impl::write_port(module.p, _VL_PY_ABS(msb-lsb), value, s);; \
    }

#define VL_PY_MODULE(m, t) pybind11::class_<t, VerilatedModule>(m, #t, py::module_local{}) \
                            .def(pybind11::init<const char*>(), pybind11::arg("name") = #t)

#define VL_PY_INPORT(n, p, msb, lsb, s) .def_property(#p, _VL_PY_PORT_READ(n, p, msb, lsb, s), _VL_PY_PORT_WRITE(n, p, msb, lsb, s))
#define VL_PY_OUTPORT(n, p, msb, lsb, s) .def_property_readonly(#p, _VL_PY_PORT_READ(n, p, msb, lsb, s))
#define VL_PY_INOUTPORT(n, p, msb, lsb, s) .def_property(#p, _VL_PY_PORT_READ(n, p, msb, lsb, s), _VL_PY_PORT_WRITE(n, p, msb, lsb, s))

#define VL_PY_INPORT_W(n, p, msb, lsb, s) .def_property(#p, _VL_PY_PORT_READ_W(n, p, msb, lsb, s), _VL_PY_PORT_WRITE_W(n, p, msb, lsb, s))
#define VL_PY_OUTPORT_W(n, p, msb, lsb, s) .def_property_readonly(#p, _VL_PY_PORT_READ_W(n, p, msb, lsb, s))
#define VL_PY_INOUTPORT_W(n, p, msb, lsb, s) .def_property(#p, _VL_PY_PORT_READ(n, p, msb, lsb, s), _VL_PY_PORT_WRITE(n, p, msb, lsb, s))

#define VL_PY_PARAM(n, p) .def_readonly(#p, &n::p)
#define VL_PY_FUNC(n, f) .def(#f, &n::f)
#define VL_PY_FUNC_STATIC(n, f) .def_static(#f, &n::f)
#define VL_PY_FUNC_TRACE(n) .def("trace", &n::trace, pybind11::arg("tfp"), pybind11::arg("levels"), pybind11::arg("options") = 0, "Trace signals in the model.")
#define VL_PY_VAR(n, v) .def_readwrite(#v, &n::v)

#endif  // Guard
