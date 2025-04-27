// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

module top;
  logic pEdge = 1'b0;
  logic nEdge = 1'b1;
  logic edgeP = 1'b0;
  logic edgeN = 1'b1;
  logic changeP = 1'b0;
  logic changeN = 1'b1;

  int pEdgeCnt = 0;
  int nEdgeCnt = 0;
  int edgePCnt = 0;
  int edgeNCnt = 0;
  int changePCnt = 0;
  int changeNCnt = 0;

  time pEdgeTime[3] = '{-1, -1, -1};
  time nEdgeTime[3] = '{-1, -1, -1};
  time edgePTime[3] = '{-1, -1, -1};
  time edgeNTime[3] = '{-1, -1, -1};
  time changePTime[3] = '{-1, -1, -1};
  time changeNTime[3] = '{-1, -1, -1};

  initial begin
    pEdge = 1'b1;
    nEdge = 1'b0;
    edgeP = 1'b1;
    edgeN = 1'b0;
    changeP = 1'b1;
    changeN = 1'b0;

    #10;
    pEdge = 1'b0;
    nEdge = 1'b1;
    edgeP = 1'b0;
    edgeN = 1'b1;
    changeP = 1'b0;
    changeN = 1'b1;

    #10;
    pEdge = 1'b1;
    nEdge = 1'b0;
    edgeP = 1'b1;
    edgeN = 1'b0;
    changeP = 1'b1;
    changeN = 1'b0;

    #10;
    $display("pEdgeCnt: %0d", pEdgeCnt);
    $display("nEdgeCnt: %0d", nEdgeCnt);
    $display("edgePCnt: %0d", edgePCnt);
    $display("edgeNCnt: %0d", edgeNCnt);
    $display("changePCnt: %0d", changePCnt);
    $display("changeNCnt: %0d", changeNCnt);

    $display("pEdgeTime: %p", pEdgeTime);
    $display("nEdgeTime: %p", nEdgeTime);
    $display("edgePTime: %p", edgePTime);
    $display("edgeNTime: %p", edgeNTime);
    $display("changePTime: %p", changePTime);
    $display("changeNTime: %p", changeNTime);

    `checkh(pEdgeCnt, 2);
    `checkh(nEdgeCnt, 2);
    `checkh(edgePCnt, 3);
    `checkh(edgeNCnt, 3);
    `checkh(changePCnt, 3);
    `checkh(changeNCnt, 3);

    `checkh(pEdgeTime[0],  0);
    `checkh(pEdgeTime[1], 20);
    `checkh(pEdgeTime[2], -1);
    `checkh(nEdgeTime[0],  0);
    `checkh(nEdgeTime[1], 20);
    `checkh(nEdgeTime[2], -1);
    `checkh(edgePTime[0],  0);
    `checkh(edgePTime[1], 10);
    `checkh(edgePTime[2], 20);
    `checkh(edgeNTime[0],  0);
    `checkh(edgeNTime[1], 10);
    `checkh(edgeNTime[2], 20);
    `checkh(changePTime[0],  0);
    `checkh(changePTime[1], 10);
    `checkh(changePTime[2], 20);
    `checkh(changeNTime[0],  0);
    `checkh(changeNTime[1], 10);
    `checkh(changeNTime[2], 20);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  always @(posedge pEdge) pEdgeTime[pEdgeCnt++] = $time;
  always @(negedge nEdge) nEdgeTime[nEdgeCnt++] = $time;
  always @(edge edgeP) edgePTime[edgePCnt++] = $time;
  always @(edge edgeN) edgeNTime[edgeNCnt++] = $time;
  always @(changeP) changePTime[changePCnt++] = $time;
  always @(changeN) changeNTime[changeNCnt++] = $time;

endmodule // test
