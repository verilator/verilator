// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Thierry Tambe.
// SPDX-License-Identifier: CC0-1.0

module t ();

   sub sub [1] ();

   ahb_slave_intf AHB_S[1]();

   AHB_MEM uMEM(.S(AHB_S[0]));
//   AHB_MEM uMEM(.S(AHB_S[0].source));

endmodule

module sub;
endmodule

module AHB_MEM
  (
   ahb_slave_intf.source S
   );

endmodule

interface ahb_slave_intf
   ();

   logic [31:0] HADDR;

   modport source (input HADDR);

endinterface
