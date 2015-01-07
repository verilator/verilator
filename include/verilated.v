//*************************************************************************
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License.
// Version 2.0.
//
// This is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//=========================================================================
//
// DESCRIPTION: Verilator: Include in verilog files to hide verilator defines

`ifdef _VERILATED_V_ `else
 `define _VERILATED_V_ 1

 // Hide verilator pragmas from other tools
 `ifdef VERILATOR `else
  `define coverage_block_off
 `endif

 // Hide file descriptor difference - deprecated - for older versions
 `define verilator_file_descriptor integer

`endif // guard
