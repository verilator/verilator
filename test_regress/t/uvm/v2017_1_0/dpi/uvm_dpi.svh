//----------------------------------------------------------------------
// Copyright 2010-2011 Mentor Graphics Corporation
// Copyright 2010 Synopsys, Inc.
// Copyright 2010-2018 Cadence Design Systems, Inc.
// Copyright 2010 AMD
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
//----------------------------------------------------------------------

`ifndef UVM_DPI_SVH
`define UVM_DPI_SVH

//
// Top-level file for DPI subroutines used by UVM.
//
// Tool-specific distribution overlays may be required.
//
// To use UVM without any tool-specific overlay, use +defin+UVM_NO_DPI
//

`ifdef UVM_NO_DPI
  `define UVM_HDL_NO_DPI
  `define UVM_REGEX_NO_DPI
  `define UVM_CMDLINE_NO_DPI
`endif

`include "dpi/uvm_hdl.svh"
`include "dpi/uvm_svcmd_dpi.svh"
`include "dpi/uvm_regex.svh"

`endif // UVM_DPI_SVH
