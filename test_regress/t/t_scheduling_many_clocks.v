// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  localparam int ITERATIONS = 5;
  localparam int N = 227;

  logic [N-1:0] gclk = {N{1'b0}};

  // Not actually used, but creates an extra internal trigger
  export "DPI-C" function toggle;
  function void toggle();
    gclk = ~gclk;
  endfunction

  int cyc = 0;
  bit par = 0;
  always @(posedge clk) begin
     if (~|gclk) begin
       gclk[0] = 1'b1;
     end else begin
       gclk = {gclk[N-2:0], gclk[N-1]};
     end

     // This make the always block requires a 'pre' trigger (and makes it non splitable)
     par <= ^gclk;

     cyc <= cyc + 32'd1;
     if (cyc == ITERATIONS*N - 1) begin
         $display("final cycle: %0d, par: %0d", cyc, par);
         $write("*-* All Finished *-*\n");
         $finish;
     end
  end

  for (genvar n = 0; n < N; n++) begin : gen
    int cnt = 0;
    always @(posedge gclk[n]) cnt <= cnt + 1;

    int cnt_plus_one;
    always_comb cnt_plus_one = cnt + 1;

    final begin
      `checkh(cnt_plus_one, ITERATIONS + 1);
    end
  end

endmodule
