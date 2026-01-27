// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Thierry Tambe
// SPDX-License-Identifier: CC0-1.0

module t ();

   ahb_slave_intf AHB_S[1]();

   AHB_MEM uMEM(.S(AHB_S[0].source));
//   AHB_MEM V_MEM(.S(AHB_S[0]));

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
