// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.

// Contributed by M W Lund, Atmel Corporation.

`ifndef _PORTS_H_SV_
 `define _PORTS_H_SV_

// *****************************************************************************
//
// *****************************************************************************

// !!!! Incomplete!
localparam int str_pinid [0:15] =
'{
 "DEF", "ERR", "ERR", "ERR", "ERR", "ERR", "ERR", "ERR",
 "PA0", "PA1", "PA2", "PA3", "PA4", "PA5", "PA6", "PA7"
 };


// **** Port Identifiers ****
typedef enum int
{
 PORTID_A = 32'd0,                    // MUST BE ZERO!
 PORTID_B,
 PORTID_C,
 PORTID_D,
 PORTID_E,
 PORTID_F,
 PORTID_G,
 PORTID_H,
 // PORTID_I, -> DO NOT USE!
 PORTID_J,
 PORTID_K,
 PORTID_L,
 PORTID_M,
 PORTID_N,
 // PORTID_O, -> DO NOT USE!
 PORTID_P,
 PORTID_Q,
 PORTID_R
 } t_portid;



`endif // !`ifdef _PORTS_H_SV_

// **** End of File ****
