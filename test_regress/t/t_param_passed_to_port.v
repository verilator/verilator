// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

parameter int HwDataAttr[1] = '{1};

module flash_mp_data_region_sel (
   input int  region_attrs_i[1],
   output int o
);
   assign o = region_attrs_i[0];
endmodule

module t;
   int o;
   flash_mp_data_region_sel u_hw_sel (.region_attrs_i(HwDataAttr), .o(o));
   initial begin
      if (o != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
