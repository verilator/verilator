// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Driss Hafdi
// SPDX-License-Identifier: CC0-1.0

interface validData
  (
   input wire clk,
   input wire rst
   );

   logic      data;
   logic      valid;

   modport sink
     (
      input data, valid, clk, rst
      );

   modport source
     (
      input  clk, rst,
      output data, valid
      );
endinterface

module sinkMod
  (
   validData.sink ctrl,
   output logic valid_data
   );
   always_ff @(posedge ctrl.clk) begin
      if (ctrl.valid) valid_data <= ctrl.data;
   end
endmodule

module sourceMod
  (
   validData.source ctrl
   );
   always_ff @(posedge ctrl.clk) begin
      ctrl.data <= ~ctrl.data;
      ctrl.valid <= ~ctrl.valid;
   end
endmodule

module parentSourceMod
  (
   validData.sink ctrl
   );
   sourceMod source_i (.ctrl);
endmodule


module t (/*AUTOARG*/
   // Outputs
   data,
   // Inputs
   clk, rst
   );
   input clk;
   input rst;
   output logic data;

   validData ctrl(.clk, .rst);
   sinkMod sink_i (.ctrl, .valid_data(data));
   parentSourceMod source_i (.ctrl);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
