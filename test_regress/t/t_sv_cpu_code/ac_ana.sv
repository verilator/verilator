// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

module ac_ana
// #( parameter
//      ID = 1 )
 (
  // ***************************************************************************
  // Module Interface (interfaces, outputs, and inputs)
  // ***************************************************************************

  // **** Interfaces ****
  pads_if.mp_ana  padsif,


  // **** Outputs ****
  output logic       acout,


  // **** Inputs ****
  input  logic       acenable,


  // - System -
  input  logic       clk,
  input  logic       rst
 );

  // ***************************************************************************
  // Analog Model
  // ***************************************************************************

  assign acout = (padsif.ana[1] - padsif.ana[2]) & acenable;

  assign padsif.ana_override[1] = 1'b0;
  assign padsif.ana_override[2] = 1'b0;


endmodule // ac_ana
