// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

//*****************************************************************************
// PAD_GPIO - General Purpose I/O Pad (Dummy!!!!)
//*****************************************************************************

module pad_gpio
#( parameter ID = 0 )
  (
   input  logic pullup_en,
   input  logic pulldown_en,
   input  logic output_en,
   input  logic output_val,
   input  logic slew_limit_en,
   input  logic input_en,
   output logic input_val,

   inout  wire  ana,

   inout wire pad
   );

   // **** Analog <-> pad connection ****
`ifndef VERILATOR //TODO alias
   alias ana = pad;
`endif


  // **** Digital driver <-> pad connection ****
  assign pad = (output_en) ? output_val : 1'bz;


  // **** Digital pull-up/pull-down <-> pad connection ****
  // TO BE ADDED!!!!


  // **** Digital input <-> pad connection ****
  assign input_val = (input_en) ? pad : 1'b0;



endmodule // pad_gpio
