// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

module ac
 #( parameter
      ID = 1 )
 (
  // ***************************************************************************
  // Module Interface (interfaces, outputs, and inputs)
  // ***************************************************************************

  // **** Interfaces ****
  genbus_if.slave dbus,
  pads_if.mp_ana  padsif,

  // - System -
  input  logic       clk,
  input  logic       rst
 );

  // ***************************************************************************
  // Regs and Wires, Automatics
  // ***************************************************************************

  /*AUTOWIRE*/
  // Beginning of automatic wires (for undeclared instantiated-module outputs)
  logic                 acenable;               // From i_ac_dig of ac_dig.v
  logic                 acout;                  // From i_ac_ana of ac_ana.v
  // End of automatics


  // ***************************************************************************
  // Digital Control
  // ***************************************************************************

  ac_dig
    #( .ID(ID) )
       i_ac_dig
         (
          .dbus                         (dbus),
          /*AUTOINST*/
          // Outputs
          .acenable                     (acenable),
          // Inputs
          .acout                        (acout),
          .clk                          (clk),
          .rst                          (rst));


  // ***************************************************************************
  // Analog Model
  // ***************************************************************************

  ac_ana
       i_ac_ana
         (
          .padsif                       (padsif),
          /*AUTOINST*/
          // Outputs
          .acout                        (acout),
          // Inputs
          .acenable                     (acenable),
          .clk                          (clk),
          .rst                          (rst));

endmodule // ac
