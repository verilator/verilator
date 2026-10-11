// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Packed arrays and structs marked with split_var, mostly ones that cannot be split

typedef struct packed {
  logic [4:0] a;
  logic [6:0] b;
} ps_t;

module t (
    input clk,
    // Primary input, not split
    input ps_t in  /*verilator split_var*/
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  // Marked and split
  ps_t ok  /*verilator split_var*/;
  // Public, not split
  ps_t pub  /*verilator public*/  /*verilator split_var*/;
  // Select spanning members, not decomposed, but bitblasted
  ps_t span  /*verilator split_var*/;
  // Variable index, not split
  logic [3:0][2:0] vix  /*verilator split_var*/;

  always_comb begin
    ok.a = crc[4:0];
    ok.b = 7'(ok.a) ^ crc[11:5];
    pub.a = crc[4:0];
    pub.b = crc[11:5];
    span.a = crc[4:0];
    span.b = crc[11:5];
    vix[0] = crc[2:0];
    vix[1] = vix[0] + 3'd1;
    vix[2] = vix[1] + 3'd1;
    vix[3] = vix[2] + 3'd1;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    `checkh(ok.b, 7'(crc[4:0]) ^ crc[11:5]);
    `checkh(pub.b, crc[11:5]);
    `checkh(span[8:3], {crc[1:0], crc[11:8]});
    `checkh(vix[crc[1:0]], 3'(crc[2:0] + 3'(crc[1:0])));
    `checkh(in, 12'h0);
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
