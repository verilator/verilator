// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(aw_addr, orig_aw_size);

   typedef logic [63:0] addr_t;
   typedef logic [7:0][7:0] mst_data_t;

   logic [127:0] slv_req_i_w_data;
   input addr_t aw_addr;
   mst_data_t w_data;
   input logic [2:0] orig_aw_size;

   always_comb begin

      // verilator lint_off WIDTHEXPAND
      automatic addr_t mst_port_offset = aw_addr[2:0];
      automatic addr_t slv_port_offset = aw_addr[3:0];

      w_data = '0;

      for (int b=0; b<16; b++) begin
         if ((b >= slv_port_offset) &&
             (b - slv_port_offset < (1 << orig_aw_size)) &&
             (b + mst_port_offset - slv_port_offset < 8)) begin
            automatic addr_t index = b + mst_port_offset - slv_port_offset;

            // verilator lint_on WIDTHEXPAND
            // [#][7:0] = [ +: 8]
            w_data[index] = slv_req_i_w_data[8*b +: 8];

         end
      end
   end
endmodule
