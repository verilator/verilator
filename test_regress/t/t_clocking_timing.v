// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`timescale 10ns/1ns

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

`ifndef TEST_WIDTH
`define TEST_WIDTH 4
`endif
`ifndef TEST_BITS
`define TEST_BITS 4*`TEST_WIDTH
`endif

`ifndef TEST_CLK_PERIOD
`define TEST_CLK_PERIOD 10
`endif
`ifndef TEST_INPUT_SKEW
`define TEST_INPUT_SKEW 2
`endif
`ifndef TEST_OUTPUT_SKEW
`define TEST_OUTPUT_SKEW 6
`endif
`ifndef TEST_CYCLE_DELAY
`define TEST_CYCLE_DELAY 4
`endif

module t;
   typedef logic[`TEST_BITS-1:0] sig_t;
   sig_t D, Q;
   always @(posedge clk) Q <= D;

   logic clk = 0;
   always #(`TEST_CLK_PERIOD/2) clk = ~clk;

   always @(posedge clk) `WRITE_VERBOSE(("[%0t] posedge clk\n", $time));

   default clocking cb @(posedge clk);
      default input #`TEST_INPUT_SKEW output #`TEST_OUTPUT_SKEW;
      input Q;
      output D;
   endclocking

`ifdef TEST_VERBOSE
   initial $monitor("[%0t] --> D=%x\t\tQ=%x\t\tcb.Q=%x", $time, D, Q, cb.Q);
`endif

   always
      begin
         sig_t val = '0;
         cb.D <= val;
         for (int i = 0; i < 5; i++) begin ##(`TEST_CYCLE_DELAY+`TEST_OUTPUT_SKEW/`TEST_CLK_PERIOD+1)
            val = {`TEST_WIDTH{(`TEST_BITS/`TEST_WIDTH)'('ha + i)}};
            `WRITE_VERBOSE(("[%0t] cb.D <= ##%0d %x\n", $time, `TEST_CYCLE_DELAY, val));
            cb.D <= ##(`TEST_CYCLE_DELAY) val;
            fork
                #(`TEST_CYCLE_DELAY*`TEST_CLK_PERIOD+`TEST_OUTPUT_SKEW-0.1) begin
                    if (D == val) begin
                        `WRITE_VERBOSE(("[%0t] D == %x == %x\n", $time, D, val));
                        $stop;
                    end
                    if (cb.Q != D) begin
                        `WRITE_VERBOSE(("[%0t] cb.Q == %x != %x\n", $time, cb.Q, D));
                        $stop;
                    end
                end
                #(`TEST_CYCLE_DELAY*`TEST_CLK_PERIOD+`TEST_OUTPUT_SKEW+0.1) begin
                    if (D != val) begin
                        `WRITE_VERBOSE(("[%0t] D == %x != %x\n", $time, D, val));
                        $stop;
                    end
                    if (cb.Q == D) begin
                        `WRITE_VERBOSE(("[%0t] cb.Q == %x == %x\n", $time, cb.Q, D));
                        $stop;
                    end
                end
            join_none
         end
         ##4
         $write("*-* All Finished *-*\n");
         $finish;
      end
endmodule
