// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

parameter int HwDataAttr[1] = '{1};

module flash_mp_data_region_sel (
   input int region_attrs_i[1]
);
   initial begin
      int o = 0;
      for (int i = 0; i < 1; i++) begin
         o = region_attrs_i[i];
      end
      if (o != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module t;
   flash_mp_data_region_sel u_hw_sel (.region_attrs_i(HwDataAttr));
endmodule
