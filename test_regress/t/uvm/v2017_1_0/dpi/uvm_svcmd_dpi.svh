//
//------------------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2013-2018 Cadence Design Systems, Inc.
// Copyright 2010-2012 AMD
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//------------------------------------------------------------------------------

// Import DPI functions used by the interface to generate the
// lists.

`ifndef UVM_CMDLINE_NO_DPI
import "DPI-C" function string uvm_dpi_get_next_arg_c (int init);
import "DPI-C" function string uvm_dpi_get_tool_name_c ();
import "DPI-C" function string uvm_dpi_get_tool_version_c ();

function string uvm_dpi_get_next_arg(int init=0);
  return uvm_dpi_get_next_arg_c(init);
endfunction

function string uvm_dpi_get_tool_name();
  return uvm_dpi_get_tool_name_c();
endfunction

function string uvm_dpi_get_tool_version();
  return uvm_dpi_get_tool_version_c();
endfunction

import "DPI-C" function chandle uvm_dpi_regcomp(string regex);
import "DPI-C" function int uvm_dpi_regexec(chandle preg, string str);
import "DPI-C" function void uvm_dpi_regfree(chandle preg);

`else
function string uvm_dpi_get_next_arg(int init=0);
  return "";
endfunction

function string uvm_dpi_get_tool_name();
  return "?";
endfunction

function string uvm_dpi_get_tool_version();
  return "?";
endfunction


function chandle uvm_dpi_regcomp(string regex); return null; endfunction
function int uvm_dpi_regexec(chandle preg, string str); return 0; endfunction
function void uvm_dpi_regfree(chandle preg); endfunction

`endif
