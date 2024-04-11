// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Paul Wright.
// SPDX-License-Identifier: CC0-1.0

// A submodule to ensure that __en and __out propagate upwards
module
   t_sub_io
     (
      inout my_io,
      input drv_en,
      input op_val
     );

   timeunit 1ns;
   timeprecision 1ps;

   assign my_io = drv_en ? op_val : 1'bz;

endmodule

`ifndef T_TRI_TOP_NAME
 `define T_TRI_TOP_NAME t_tri_top_en_out
`endif

// The top module
// __en and __out should be added for the inout ports
module
   `T_TRI_TOP_NAME
     (
      inout single_bit_io,
      inout bidir_single_bit_io,
      inout [63:0] bus_64_io,
      inout [63:0] bidir_bus_64_io,
      inout [127:0] bus_128_io,
      inout [127:0] bidir_bus_128_io,
      input [3:0] drv_en,
      input test_en,
      output logic loop_done,
      inout sub_io
      );

   timeunit 1ns;
   timeprecision 1ps;

   bit      rand_bit;

   assign single_bit_io       = 1'bz;
   assign bidir_single_bit_io = drv_en[0] ? rand_bit : 1'bz;
   assign bus_64_io           = {64{1'bz}};

   assign bidir_bus_64_io[15:0]  = drv_en[0] ? {16{rand_bit}} : {16{1'bz}};
   assign bidir_bus_64_io[31:16] = drv_en[1] ? {16{rand_bit}} : {16{1'bz}};
   assign bidir_bus_64_io[47:32] = drv_en[2] ? {16{rand_bit}} : {16{1'bz}};
   assign bidir_bus_64_io[63:48] = drv_en[3] ? {16{rand_bit}} : {16{1'bz}};

   assign bus_128_io          = {128{1'bz}};

   assign bidir_bus_128_io[31:0]   = drv_en[0] ? {32{rand_bit}} : {32{1'bz}};
   assign bidir_bus_128_io[63:32]  = drv_en[1] ? {32{rand_bit}} : {32{1'bz}};
   assign bidir_bus_128_io[95:64]  = drv_en[2] ? {32{rand_bit}} : {32{1'bz}};
   assign bidir_bus_128_io[127:96] = drv_en[3] ? {32{rand_bit}} : {32{1'bz}};

   int loop_cnt;
   int error_cnt;

   initial begin : init_error
       error_cnt = 'd0;
   end

   initial begin : test_and_loop
        loop_cnt = 0;
        #(1ps);
        while (test_en == 1) begin
           loop_done = 0;
           rand_bit = (($urandom_range(1,0) & 'd1) == 'd1);
           chk_sigs;
           #(1ns) $display("Info:(v): 1ns");
           rand_bit = ~rand_bit;
           chk_sigs;
           #(1ns) $display("Info:(v): 2ns");
           rand_bit = ~rand_bit;
           chk_sigs;
           #(1ns);
           loop_done = 1;
           loop_cnt++;
           #(1ps);
        end
        if (error_cnt == 'd0) begin
            $display("Info:(v): Error count was = %0d", error_cnt);
             $write("*-* All Finished *-*\n");
          end
        else begin
           $display("Info:(v): Error count was non-zero %0d", error_cnt);
          end
        $finish(1);
     end

   always @(loop_cnt)
     begin
       if (loop_cnt > 32) begin
           $display("%%Error:(v): Excessive loop count");
           $display("drv_en = %b, test_en = %b", drv_en, test_en);
           $finish(1);
         end
     end

   final begin
        $display("Info:(v): All done at %t", $time);
        $display("Info:(v): Error count = %0d", error_cnt);
        chk_err: assert(error_cnt == 0);
     end

   wire internal_sub_io;

   logic [15:0] my_64_segment;
   logic [31:0] my_128_segment;

   task chk_sigs;
     begin
        #(1ps);
        $display("Info:(v): rand_bit = %b", rand_bit);
        if (|drv_en) begin
             $display("Info:(v): drv_en = %b", drv_en);
             $display("Info:(v): bidir_single_bit_io = %b", bidir_single_bit_io);
             $display("Info:(v): bidir_bus_64_io = %b,%b,%b,%b",
                      bidir_bus_64_io[63:48], bidir_bus_64_io[47:32],
                      bidir_bus_64_io[31:16],bidir_bus_64_io[15:0]);
             $display("Info:(v): bidir_bus_128_io = %b,%b,%b,%b",
                      bidir_bus_128_io[127:96], bidir_bus_128_io[95:64],
                      bidir_bus_128_io[63:32], bidir_bus_128_io[31:0]);

             for (int i=0;i<4;i++) begin
                 if (drv_en[0]) begin
                     if (bidir_single_bit_io !== rand_bit) begin
                         $display("%%Error:(v): bidir_single_bit_io is wrong (expect %b got %b)",
                                  rand_bit, bidir_single_bit_io);
                         error_cnt++;
                       end
                     if (sub_io !== rand_bit) begin
                         $display("%%Error:(v): sub_io is wrong (expect %b, got %b)",
                                  rand_bit, sub_io);
                       end
                 end

                 if (drv_en[1]) begin
                     if (internal_sub_io !== ~rand_bit) begin
                         $display("%%Error:(v): sub_io is wrong");
                         error_cnt++;
                       end
                 end

                 if (drv_en[i]) begin
                     int msb, lsb;
                     msb = ((i+1)*16-1);
                     lsb = i*16;

                     case(i)
                      'd0: my_64_segment = bidir_bus_64_io[15:0];
                      'd1: my_64_segment = bidir_bus_64_io[31:16];
                      'd2: my_64_segment = bidir_bus_64_io[47:32];
                      default: my_64_segment = bidir_bus_64_io[63:48];
                     endcase

                     case(i)
                      'd0: my_128_segment     = bidir_bus_128_io[31:0];
                      'd1: my_128_segment     = bidir_bus_128_io[63:32];
                      'd2: my_128_segment     = bidir_bus_128_io[95:64];
                      default: my_128_segment = bidir_bus_128_io[127:96];
                     endcase

                     if (my_64_segment !== {16{rand_bit}}) begin
                         $display("%%Error:(v): bidir_bus_64_io is wrong");
                         $display("Error:(v): Should be bidir_bus_64_io[%0d:%0d] = %b, was = %b",
                                  msb, lsb, {16{rand_bit}}, my_64_segment);
                         error_cnt++;
                       end
                     else begin
                         $display("Info:(v): Pass: bidir_bus_64_io[%0d:%0d] = %b",
                                  msb, lsb, {16{rand_bit}});
                       end

                     msb = ((i+1)*32-1);
                     lsb = i*32;
                     if (my_128_segment !== {32{rand_bit}}) begin
                         $display("%%Error:(v): bidir_bus_128_io is wrong");
                         $display("Error:(v):Should be bidir_bus_128_io[%0d:%0d] = %b, was = %b",
                                  msb, lsb, {32{rand_bit}}, my_128_segment);
                         error_cnt++;
                       end
                     else
                       begin
                         $display("Info:(v): Pass: bidir_bus_128_io[%0d:%0d] = %b",
                                  msb, lsb, {32{rand_bit}});
                       end
                   end
              end
         end
     end
  endtask

  // Connects to top level
  t_sub_io
    t_sub_io
      (
       .my_io  (sub_io),
       .drv_en (drv_en[0]),
       .op_val (rand_bit)
      );

  // Does not connect to top-level
  t_sub_io
    t_sub_io_internal
      (
       .my_io  (internal_sub_io),
       .drv_en (drv_en[1]),
       .op_val (~rand_bit)
      );

endmodule
