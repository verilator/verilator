// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by John Stevenson.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef logic [31:0] unique_id_t;
   typedef struct packed {
      unique_id_t foo;
   } inner_thing_t;
   typedef struct packed {
      inner_thing_t bar;
      inner_thing_t baz;
   } outer_thing_t;

endpackage

import pkg::*;

interface the_intf
  #(parameter M=5);
    outer_thing_t [M-1:0] things;
    logic                 valid;
    modport i (
               output things,
               output valid);
    modport t (
               input things,
               input valid);
endinterface

module ThingMuxOH
  #(
    parameter NTHINGS = 1,
    parameter       M = 5 )
   (
    input logic [NTHINGS-1:0] select_oh,
    the_intf.t things_in [NTHINGS-1:0],
    the_intf.i thing_out
    );
    assign thing_out.valid = things_in[0].valid;
endmodule

module ThingMuxShort
  #(
    parameter NTHINGS = 1,
    parameter       M = 5 )
   (
    input logic [NTHINGS-1:0] select_oh,
    the_intf.t things_in [NTHINGS],
    the_intf.i thing_out
    );
    assign thing_out.valid = things_in[0].valid;
endmodule

module Thinker
  #(
    parameter M = 5,
    parameter N = 2)
   (
    input logic clk,
    input logic reset,
    input       unique_id_t uids[0:N-1],
    the_intf.t thing_inp,
    the_intf.i thing_out
    );

   the_intf #(.M(M)) curr_things [N-1:0] ();
   the_intf #(.M(M)) prev_things [N-1:0] ();
   the_intf #(.M(M)) s_things [N] ();
   the_intf #(.M(M)) curr_thing ();
   the_intf #(.M(M)) prev_thing ();
   the_intf #(.M(M)) s_thing ();

   logic [N-1:0] select_oh;

   // 1st mux:
   ThingMuxOH #(
    .NTHINGS  ( N           ),
    .M        ( M           ))
   curr_thing_mux(
    .select_oh( select_oh   ),
    .things_in( curr_things ),
    .thing_out( curr_thing  ));

   // 2nd mux, comment this out and no problem:
   ThingMuxOH #(
    .NTHINGS  ( N           ),
    .M        ( M           ))
   prev_thing_mux(
    .select_oh( select_oh   ),
    .things_in( prev_things ),
    .thing_out( prev_thing  ));

   // 3rd mux, using short array nomenclature:
   ThingMuxShort #(
    .NTHINGS  ( N           ),
    .M        ( M           ))
   s_thing_mux(
    .select_oh( select_oh   ),
    .things_in( s_things ),
    .thing_out( s_thing  ));

endmodule

module t
  (
   input logic clk,
   input logic reset
   );

   localparam M = 5;
   localparam N = 2;

   unique_id_t uids[0:N-1];

   the_intf #(.M(M)) thing_inp();
   the_intf #(.M(M)) thing_out();

   Thinker #(
    .M        ( M         ),
    .N        ( N         ))
   thinker(
    .clk      ( clk       ),
    .reset    ( reset     ),
    .uids     ( uids      ),
    .thing_inp( thing_inp ),
    .thing_out( thing_out ));

   // Previously there was a problem in V3Inst if non-default parameters was used
   localparam K = 2;
   the_intf #(.M(K)) thing_inp2();
   the_intf #(.M(K)) thing_out2();

   Thinker #(
    .M        ( K         ),
    .N        ( N         ))
   thinker2(
    .clk      ( clk       ),
    .reset    ( reset     ),
    .uids     ( uids      ),
    .thing_inp( thing_inp2 ),
    .thing_out( thing_out2 ));
endmodule
