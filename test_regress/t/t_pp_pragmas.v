// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

`timescale 1ns/10ps
`verilog

`suppress_faults
`nosuppress_faults
`enable_portfaults
`disable_portfaults

`delay_mode_distributed
`delay_mode_path
`delay_mode_unit
`delay_mode_zero

`default_decay_time 1
`default_decay_time 1.0
`default_decay_time infinite
// unsupported (recommended not to): `default_trireg_strength 10

`default_nettype wire
// unsupported: `default_nettype tri
// unsupported: `default_nettype tri0
// unsupported: `default_nettype wand
// unsupported: `default_nettype triand
// unsupported: `default_nettype wor
// unsupported: `default_nettype trior
// unsupported: `default_nettype trireg
`default_nettype none

`autoexpand_vectornets

`accelerate
`noaccelerate
`expand_vectornets
`noexpand_vectornets
`remove_gatenames
`noremove_gatenames
`remove_netnames
`noremove_netnames
`resetall

// unsupported: `unconnected_drive pull1
// unsupported: `unconnected_drive pull0
`nounconnected_drive

`line 100 "hallo.v" 0

// unsupported: `uselib file=../moto_lib.v
// unsupported: `uselib dir=../lib.dir libext=.v

module t;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
