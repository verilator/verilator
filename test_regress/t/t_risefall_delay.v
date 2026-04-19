// DESCRIPTION: Verilator: Rise/fall delays on continuous assigns and gates
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0)
`define check_scalar(exp) do begin `checkh(out_assign, exp); `checkh(out_buf, exp); `checkh(out_net, exp); end while(0)

module t;
  logic in = 0;
  logic [3:0] in_vec = 4'h0;
  wire out_assign;
  wire out_buf;
  wire #(5,3) out_net;
  wire [3:0] out_vec_assign;

  assign #(5,3) out_assign = in;
  buf #(5,3) u_buf (out_buf, in);
  assign out_net = in;
  assign #(5,3) out_vec_assign = in_vec;

  initial begin
    #4;
    `check_scalar(1'b0);
    `checkh(out_vec_assign, 4'h0);

    // Rise canceled by a fall before the rise delay expires.
    in = 1'b1;
    #2;
    `check_scalar(1'b0);

    in = 1'b0;
    #4;
    `check_scalar(1'b0);

    // A committed rise.
    in = 1'b1;
    #4;
    `check_scalar(1'b0);
    #1;
    `check_scalar(1'b1);

    // Fall canceled by a new rise before the fall delay expires.
    in = 1'b0;
    #2;
    `check_scalar(1'b1);
    in = 1'b1;
    #4;
    `check_scalar(1'b1);
    #1;
    `check_scalar(1'b1);

    // A committed fall.
    in = 1'b0;
    #2;
    `check_scalar(1'b1);
    #1;
    `check_scalar(1'b0);

    // Whole-value vector rise canceled by a fall back to zero.
    in_vec = 4'h3;
    #2;
    `checkh(out_vec_assign, 4'h0);
    in_vec = 4'h0;
    #4;
    `checkh(out_vec_assign, 4'h0);

    // Zero to nonzero uses the rise delay.
    in_vec = 4'h3;
    #4;
    `checkh(out_vec_assign, 4'h0);
    #1;
    `checkh(out_vec_assign, 4'h3);

    // Nonzero to nonzero still uses the rise delay on the whole value.
    in_vec = 4'h5;
    #4;
    `checkh(out_vec_assign, 4'h3);
    #1;
    `checkh(out_vec_assign, 4'h5);

    // A pending fall back to zero is canceled by a new nonzero value.
    in_vec = 4'h0;
    #2;
    `checkh(out_vec_assign, 4'h5);
    in_vec = 4'h6;
    #4;
    `checkh(out_vec_assign, 4'h5);
    #1;
    `checkh(out_vec_assign, 4'h6);

    // Nonzero to zero uses the fall delay.
    in_vec = 4'h0;
    #2;
    `checkh(out_vec_assign, 4'h6);
    #1;
    `checkh(out_vec_assign, 4'h0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
