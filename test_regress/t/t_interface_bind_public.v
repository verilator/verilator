// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Alex Solomatnikov.
// SPDX-License-Identifier: CC0-1.0

interface hex2ram_if
  (
   input bit trigger
   );

   string    instance_path  = $sformatf("%m");
   string    testfile       = "";
   bit       has_testfile   = |($value$plusargs("testfile=%s", testfile));
   bit       armed          = 1'b1;
   bit       armed_trigger;

   initial begin
      $display("successfully bound hex2ram_if to %s", instance_path);
      armed = has_testfile && 1'b1;
   end

   assign armed_trigger = armed && trigger;

   always @(posedge armed_trigger) begin
      $display("%m(%0t): saw deassertion of reset", $time);
   end

endinterface : hex2ram_if

module t
  (
   clk
   );

   input clk /*verilator clocker*/;
   bit reset;

   wire      success;
   SimpleTestHarness testHarness
     (
      .clk(clk),
      .reset(reset),
      .io_success(success)
      );

   integer   cyc=0;

   always @ (posedge clk) begin
      cyc = cyc + 1;
      if (cyc<10) begin
         reset <= '0;
      end
      else if (cyc<20) begin
         reset <= '1;
      end
      else if (cyc<30) begin
         reset <= '0;
      end
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

bind testharness_ext  hex2ram_if i_hex2ram (.trigger(!t.reset));

module testharness_ext
  (
   input          W0_clk,
   input [24:0]   W0_addr,
   input          W0_en,
   input [127:0]  W0_data,
   input [0:0]    W0_mask,
   input          R0_clk,
   input [24:0]   R0_addr,
   input          R0_en,
   output [127:0] R0_data
   );

   reg [24:0]     reg_R0_addr;
   wire [127:0]   R0_rdata_mask;
   reg [127:0]    ram [33554431:0];
   wire [127:0]   W0_wdata_mask;

   always @(posedge R0_clk)
     if (R0_en) reg_R0_addr <= R0_addr;

   always @(posedge W0_clk)
     if (W0_en) begin
        if (W0_mask[0]) ram[W0_addr] <= W0_data ^ W0_wdata_mask;
     end
   assign R0_data = ram[reg_R0_addr] ^ R0_rdata_mask;;
   assign R0_rdata_mask = 0;
   assign W0_wdata_mask = 0;

endmodule

module SimpleTestHarness
  (
   input  clk,
   input  reset,
   output io_success);

   wire [24:0] testharness_ext_R0_addr;
   wire        testharness_ext_R0_en;
   wire        testharness_ext_R0_clk;
   wire [127:0] testharness_ext_R0_data;
   wire [24:0]  testharness_ext_W0_addr;
   wire         testharness_ext_W0_en;
   wire         testharness_ext_W0_clk;
   wire [127:0] testharness_ext_W0_data;
   wire [0:0]  testharness_ext_W0_mask;

   testharness_ext testharness_ext
     (
      .R0_addr(testharness_ext_R0_addr),
      .R0_en(testharness_ext_R0_en),
      .R0_clk(testharness_ext_R0_clk),
      .R0_data(testharness_ext_R0_data),
      .W0_addr(testharness_ext_W0_addr),
      .W0_en(testharness_ext_W0_en),
      .W0_clk(testharness_ext_W0_clk),
      .W0_data(testharness_ext_W0_data),
      .W0_mask(testharness_ext_W0_mask)
      );

endmodule
