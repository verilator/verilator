// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   typedef struct packed {
      logic [2:0] _foo;
      logic [2:0] _bar;
   } struct_t;

   logic [2:0] meh;
   struct_t param;
   localparam integer twentyone = 21;

   // verilator lint_off WIDTH
   assign param = '{
      _foo: twentyone % 8 + 1,
      _bar: (twentyone / 8) + 1
   };
   assign meh = twentyone % 8 + 1;
   // verilator lint_on WIDTH

   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $display("param: %d, %d, %b, %d", param._foo, param._bar, param, meh);
`endif
      if (param._foo != 6) $stop;
      if (param._bar != 3) $stop;
      if (param != 6'b110011) $stop;
      if (meh != 6) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
