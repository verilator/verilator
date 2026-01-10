// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Luca Colagrande.
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  localparam logic [1:0] INST1 = 2'b0?;
  localparam logic [1:0] INST2 = 2'b0?;
  localparam logic [1:0] INST3 = 2'b1?;

  logic [1:0] in, out;

  always_comb begin
    unique casez (in)
      INST1, INST2: begin
        if (in == 2'b00) out = 2'b01;
        else out = 2'b00;
      end
      INST3: begin
        out = 2'b10;
      end
      default: begin
        out = 2'b11;
      end
    endcase
  end

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] in=%x out=%x\n", $time, in, out);
`endif
    if (in == 0) begin
      if (out != 2'b01) $stop;
    end
    else if (in == 1) begin
      if (out != 2'b00) $stop;
    end
    else if (in == 2) begin
      if (out != 2'b10) $stop;
    end
    else if (in == 3) begin
      if (out != 2'b10) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
    in <= in + 1;
  end

endmodule
