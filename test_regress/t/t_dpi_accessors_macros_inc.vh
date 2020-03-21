// DESCRIPTION: Verilator: Generic accessor macros for test of DPI accessors
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0
//
// Contributed by Jeremy Bennett and Jie Xu
//
// See t_dpi_accessors.v for details of the test. This file should be included
// by the top level module to define the generic accessor macros.

// Accessor macros, to keep stuff concise
`define R_ACCESS(type_spec, name, expr)  \
   export "DPI-C" function name``_read;  \
   function bit type_spec name``_read;   \
      name``_read = (expr);              \
   endfunction

`define W_ACCESS(type_spec, name, expr)   \
   export "DPI-C" task  name``_write;     \
   task name``_write;                     \
      input bit type_spec in;             \
      expr = in;                          \
   endtask

`define RW_ACCESS(type_spec, name, expr) \
   `R_ACCESS (type_spec, name, expr);    \
   `W_ACCESS (type_spec, name, expr)
