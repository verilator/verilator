// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`ifdef PROCESS_TOP
module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  logic [7:0] in = 0;
  logic [7:0] out_comb, out_reg;
  logic [31:0] count = 0;

  secret i_secret (
      .clk(clk),
      .in(in),
      .out_comb(out_comb),
      .out_reg(out_reg)
  );

  always @(posedge clk) begin
    count <= count + 32'd1;
    in <= in + 8'd7;
    if (count > 32'd1) begin
      if (out_comb != in + 8'd1) begin
        $display("Mismatch in:%h out_comb:%h", in, out_comb);
        $stop;
      end
      // The library numbers evaluations from zero, so the count stays small
      if (i_secret.last_combo_seqnum__V > 1000 || i_secret.last_seq_seqnum__V > 1000) begin
        $display("Bad seqnum combo:%0d seq:%0d", i_secret.last_combo_seqnum__V,
                 i_secret.last_seq_seqnum__V);
        $stop;
      end
    end
    if (count == 32'd20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

`else
module secret (
    input clk,
    input [7:0] in,
    output [7:0] out_comb,
    output logic [7:0] out_reg
);
  assign out_comb = in + 8'd1;
  always_ff @(posedge clk) out_reg <= in;
endmodule
`endif
