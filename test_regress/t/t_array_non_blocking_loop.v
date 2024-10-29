// DESCRIPTION: Verilator: Demonstrate struct literal param assignment problem
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


interface intf
  #(
    parameter int write_data_width) ();
    logic [write_data_width-1:0] writedata;
endinterface
module t( /*AUTOARG*/
    clk
);

    input clk;
    generate
        genvar num_chunks;
        for (num_chunks = 1; num_chunks <= 2; num_chunks++) begin : gen_n
            localparam int decoded_width = 55 * num_chunks;
                intf #(
                    .write_data_width(decoded_width))
                the_intf ();
                always @(posedge clk) begin
                    for (int i = 0; i < decoded_width; i++)
                        the_intf.writedata[i] <= '1;
                    $display("%0d", the_intf.writedata);
                end
        end
    endgenerate

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
