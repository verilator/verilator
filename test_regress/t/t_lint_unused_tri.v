// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module Receiver(in);
   inout [31:0] in;
   always @(in) $display(in);
endmodule

module Sender(out);
   inout [31:0] out;
   assign out = 12;
endmodule

module t;
   // ports of submodule recv
   tri [31 : 0] recvIn;

   // submodule recv
   Receiver recv(.in(recvIn));

   // submodule send
   Sender send(.out(recvIn));
endmodule
