// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  integer cyc = 0;

  logic in[-3:-5];

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      in[-4] <= 1;
    end else if (cyc == 1) begin
      `checkh(in[-4], 1);
    end else if (cyc == 2) begin
      force in[-4] = 0;
    end else if (cyc == 3) begin
      `checkh(in[-4], 0);
      in[-4] <= 1;
    end else if (cyc == 4) begin
      `checkh(in[-4], 0);
    end else if (cyc == 5) begin
      release in[-4];
    end else if (cyc == 6) begin
      `checkh(in[-4], 0);
      in[-4] <= 1;
    end else if (cyc == 7) begin
      `checkh(in[-4], 1);
    end
    else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
