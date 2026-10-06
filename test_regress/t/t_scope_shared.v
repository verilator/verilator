// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package scope_pkg;
  bit [6:0] mask = 7'h35;
  class transform;
    static function logic [6:0] apply_mask(input logic [6:0] value);
      return value ^ mask;
    endfunction
  endclass
endpackage

interface scope_channel;
  logic [6:0] data;
  logic [6:0] result;
  modport port (input data, output result);
endinterface

module scope_leaf (
    input logic clk,
    scope_channel.port channel
);
  always_ff @(posedge clk) channel.result <= scope_pkg::transform::apply_mask(channel.data);
endmodule

module scope_pair (
    input logic clk,
    input logic [6:0] data,
    output logic [6:0] result
);
  scope_channel first();
  scope_channel second();
  assign first.data = data;
  assign second.data = first.result + 7'd9;
  scope_leaf u_first (.clk, .channel(first));
  scope_leaf u_second (.clk, .channel(second));
  assign result = second.result;
endmodule

module t (
    input logic clk
);
  int unsigned cycles = 0;
  always @(negedge clk) begin
    cycles <= cycles + 1;
    scope_pkg::mask <= scope_pkg::mask + 7'd3;
  end

  for (genvar i = 0; i < 127; i++) begin : instances
    logic [6:0] result;
    scope_pair u_pair (.clk, .data(7'(cycles + i)), .result);
    always @(negedge clk) begin
      if (cycles >= 2) begin
        `checkh(u_pair.first.result, 7'(cycles + i) ^ 7'('h35 + 3 * cycles));
        `checkh(result, 7'((7'(cycles - 1 + i) ^ 7'('h35 + 3 * (cycles - 1))) + 7'd9)
            ^ 7'('h35 + 3 * cycles));
      end
    end
  end

  always @(negedge clk) begin
    if (cycles == 40) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
