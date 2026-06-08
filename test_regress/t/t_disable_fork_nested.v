// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Clock-period detector exercising a named-block `disable` of a block whose
// body contains a nested fork..join. Disabling such a block from a sibling
// process must release the enclosing fork..join so the surrounding `always`
// block keeps iterating.

module disable_fork (
    input  logic i_clk,
    output logic [2:0] o_counter
);
   time delay1 = 500ns;  // min period
   time delay2 = 3333ns;  // max period

   logic clk_re = 1'b0;  // rising edge of the clock
   logic [2:0] counter = 3'b000;

   always begin
      fork
         begin : check1
            #delay1;
            #1 disable check2;
            fork
               begin : check3
                  #(delay2 - delay1);
                  clk_re <= 1'b0;
                  #1 disable check4;
                  if (counter < 3'b111) counter <= counter + 3'b001;
               end
               begin : check4
                  @(posedge i_clk);
                  clk_re <= 1'b1;
                  counter <= 3'b000;
                  #1 disable check3;
               end
            join
         end
         begin : check2
            @(posedge i_clk);
            clk_re <= 1'b0;
            #1 disable check1;
            if (counter < 3'b111) counter <= counter + 3'b001;
         end
      join
   end

   assign o_counter = counter;
endmodule

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
   logic clk;
   logic [2:0] counter;

   task clk_cycle(input time half_period);
      clk = 1'b1;
      #half_period;
      clk = 1'b0;
      #half_period;
   endtask : clk_cycle

   initial begin
      // Fast clock (period below delay1): every edge arrives before the
      // min-period timeout, so the counter saturates at its max.
      repeat (100) clk_cycle(200ns);
      $display("Fast clock (200ns half-period): o_counter=%0d", counter);
      `checkh(counter, 3'h7);
      // Slow clock (period above delay2): the nested fork path runs, which
      // only works if disabling check1 releases the inner fork..join.
      repeat (100) clk_cycle(5400ns);
      $display("Slow clock (5400ns half-period): o_counter=%0d", counter);
      `checkh(counter, 3'h3);
      $write("*-* All Finished *-*\n");
      $finish;
   end

   disable_fork a_inst(.i_clk(clk), .o_counter(counter));
endmodule
