// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   reg [3:0]  in;
   tri [3:0]  bus = in;

   int        never_driven;
   int        never_forced;

   task force_bus;
      force bus[1:0] = 2'b10;
   endtask

   task release_bus;
      release bus;
   endtask

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         in <= 4'b0101;
      end
      else if (cyc == 1) begin
         `checkh(in, 4'b0101);
      end
      // Check forces with no driver
      if (cyc == 1) begin
         force never_driven = 32'h888;
      end
      else if (cyc == 2) begin
         `checkh(never_driven, 32'h888);
      end
      // Check release with no force
      else if (cyc == 10) begin
         never_forced <= 5432;
      end
      else if (cyc == 11) begin
         `checkh(never_forced, 5432);
      end
      else if (cyc == 12) begin
         release never_forced;  // no-op
      end
      else if (cyc == 13) begin
         `checkh(never_forced, 5432);
      end
      //
      // bus
      else if (cyc == 10) begin
         `checkh(bus, 4'b0101);
         force bus = 4'b0111;
      end
      else if (cyc == 11) begin
         `checkh(bus, 4'b0111);
         force bus = 4'b1111;
      end
      else if (cyc == 12) begin
         `checkh(bus, 4'b1111);
         release bus;
      end
      else if (cyc == 13) begin
         `checkh(bus, 4'b0101);
      end
      else if (cyc == 20) begin
         force_bus();
      end
      else if (cyc == 21) begin
         `checkh(bus, 4'b0110);
      end
      else if (cyc == 22) begin
         release bus[0];
      end
      else if (cyc == 23) begin
         `checkh(bus, 4'b0111);
         release_bus();
      end
      else if (cyc == 24) begin
         `checkh(in, 4'b0101);
         `checkh(bus, 4'b0101);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
