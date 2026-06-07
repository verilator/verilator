// DESCRIPTION: Verilator: Verilog Test module
//
// $bits() of interface member signals used as a child module parameter value.
// $bits reads the type, not the hierarchical value, so it is legal in a
// parameter (IEEE 1800-2023 6.20.2 forbids hierarchical values only).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

interface axi_if #(
    parameter int ID_W = 8,
    parameter int ADDR_W = 32
);
  logic [ID_W-1:0] AWID;
  logic [ADDR_W-1:0] AWADDR;
  logic [7:0] AWLEN;
endinterface

module chkmod #(
    parameter int PAYLOAD_WIDTH = 1,
    parameter int EXPECT = 1
);
  initial `checkh(PAYLOAD_WIDTH, EXPECT);
endmodule

module bridge #(
    parameter int EXPECT = 1
) (
    axi_if axi
);
  // $bits of a concat of interface members
  chkmod #(
      .PAYLOAD_WIDTH($bits({axi.AWID, axi.AWADDR, axi.AWLEN})),
      .EXPECT(EXPECT)
  ) u_concat ();
  // $bits of a single interface member
  chkmod #(
      .PAYLOAD_WIDTH($bits(axi.AWADDR)),
      .EXPECT(EXPECT - 12 - 8)
  ) u_single ();
endmodule

module t;
  axi_if #(
      .ID_W(12),
      .ADDR_W(64)
  ) if0 ();  // 12 + 64 + 8 = 84
  axi_if #(
      .ID_W(12),
      .ADDR_W(16)
  ) if1 ();  // 12 + 16 + 8 = 36

  bridge #(.EXPECT(84)) dut0 (.axi(if0));
  bridge #(.EXPECT(36)) dut1 (.axi(if1));

  initial begin
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
