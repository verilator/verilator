// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef struct  {
   logic        l;
   real         r;
} struct_t;

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  integer cyc = 0;

  struct_t in[2];

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      in[0].r <= 1;
    end else if (cyc == 1) begin
      `checkr(in[0].r, 1);
    end else if (cyc == 2) begin
      force in[0].r = 0;
    end else if (cyc == 3) begin
      `checkr(in[0].r, 0);
      in[0].r <= 1;
    end else if (cyc == 4) begin
      `checkr(in[0].r, 0);
    end else if (cyc == 5) begin
      release in[0].r;
    end else if (cyc == 6) begin
      `checkr(in[0].r, 0);
      in[0].r <= 1;
    end else if (cyc == 7) begin
      `checkr(in[0].r, 1);
    end
    else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
