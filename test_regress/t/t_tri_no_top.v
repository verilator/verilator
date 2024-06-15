// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

// The module t_tri_top_en_out is used to test that we can
// force verilator to include __en and __out variables for
// inouts. This test checks that the tests within that module
// pass. They should pass regardless of the presence of C or
// SystemVerilog in the level above.

module
   t_tri_no_top
     ();

   timeunit 1ns;
   timeprecision 1ps;

   wire single_bit_io;

   wire bidir_single_bit_io;

   wire [63:0] bus_64_io;

   wire [63:0] bidir_bus_64_io;

   wire [127:0] bus_128_io;

   wire [127:0] bidir_bus_128_io;

   reg [3:0]     drv_en;

   reg         test_en;

   wire     loop_done;

   wire     sub_io;

   t_tri_top_en_out
     t_tri_top_en_out
       (.*);

   initial
     begin
       test_en = 1'b1;
       drv_en = 4'd0;

       forever
         begin
           @(loop_done);
           if (loop_done === 1'b1)
              begin
                if (drv_en == 4'hf)
                  begin
                    test_en = 1'b0;
                  end
                else
                  begin
                    drv_en++;
                  end
             end
         end
     end // initial begin

endmodule // top
