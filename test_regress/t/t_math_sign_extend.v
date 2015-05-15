// DESCRIPTION: Verilator: Verilog Test module
//
//  This test demonstrates an issue with sign extension.
//  Assigning to localparms larger than 32 bits broke in 3.862 
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Mike Thyer.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   
   localparam [ 0:0] one1_lp = 1;
   localparam [ 1:0] one2_lp = 1;
   localparam [ 2:0] one3_lp = 1;
   localparam [ 3:0] one4_lp = 1;
   localparam [ 4:0] one5_lp = 1;
   localparam [ 5:0] one6_lp = 1;
   localparam [ 6:0] one7_lp = 1;
   localparam [ 7:0] one8_lp = 1;
   localparam [ 8:0] one9_lp = 1;
   localparam [ 9:0] one10_lp = 1;
   localparam [19:0] one20_lp = 1;
   localparam [29:0] one30_lp = 1;
   localparam [30:0] one31_lp = 1;
   localparam [31:0] one32_lp = 1;
   localparam [32:0] one33_lp = 1;
   localparam [33:0] one34_lp = 1;
   localparam [34:0] one35_lp = 1;
   localparam [35:0] one36_lp = 1;
   localparam [36:0] one37_lp = 1;
   localparam [37:0] one38_lp = 1;
   localparam [38:0] one39_lp = 1;
   localparam [39:0] one40_lp = 1;
   localparam [49:0] one50_lp = 1;
   localparam [59:0] one60_lp = 1;
   localparam [60:0] one61_lp = 1;
   localparam [61:0] one62_lp = 1;
   localparam [62:0] one63_lp = 1;
   localparam [63:0] one64_lp = 1;
   localparam [64:0] one65_lp = 1;
   localparam [65:0] one66_lp = 1;
   localparam [66:0] one67_lp = 1;
   localparam [67:0] one68_lp = 1;
   localparam [68:0] one69_lp = 1;
   localparam [69:0] one70_lp = 1;
   
   bit all_ok = 1;

   initial begin
`ifdef TEST_VERBOSE
     $display("one1_lp : %x %d", one1_lp, one1_lp==1); 
     $display("one2_lp : %x %d", one2_lp, one2_lp==1); 
     $display("one3_lp : %x %d", one3_lp, one3_lp==1); 
     $display("one4_lp : %x %d", one4_lp, one4_lp==1); 
     $display("one5_lp : %x %d", one5_lp, one5_lp==1); 
     $display("one6_lp : %x %d", one6_lp, one6_lp==1); 
     $display("one7_lp : %x %d", one7_lp, one7_lp==1); 
     $display("one8_lp : %x %d", one8_lp, one8_lp==1); 
     $display("one9_lp : %x %d", one9_lp, one9_lp==1); 
     $display("one10_lp: %x %d", one10_lp, one10_lp==1); 
     $display("one20_lp: %x %d", one20_lp, one20_lp==1); 
     $display("one30_lp: %x %d", one30_lp, one30_lp==1); 
     $display("one31_lp: %x %d", one31_lp, one31_lp==1); 
     $display("one32_lp: %x %d", one32_lp, one32_lp==1); 
     $display("one33_lp: %x %d", one33_lp, one33_lp==1); 
     $display("one34_lp: %x %d", one34_lp, one34_lp==1); 
     $display("one35_lp: %x %d", one35_lp, one35_lp==1); 
     $display("one36_lp: %x %d", one36_lp, one36_lp==1); 
     $display("one37_lp: %x %d", one37_lp, one37_lp==1); 
     $display("one38_lp: %x %d", one38_lp, one38_lp==1); 
     $display("one39_lp: %x %d", one39_lp, one39_lp==1); 
     $display("one40_lp: %x %d", one40_lp, one40_lp==1); 
     $display("one50_lp: %x %d", one50_lp, one50_lp==1); 
     $display("one60_lp: %x %d", one60_lp, one60_lp==1); 
     $display("one61_lp: %x %d", one61_lp, one61_lp==1); 
     $display("one62_lp: %x %d", one62_lp, one62_lp==1); 
     $display("one63_lp: %x %d", one63_lp, one63_lp==1); 
     $display("one64_lp: %x %d", one64_lp, one64_lp==1); 
     $display("one65_lp: %x %d", one65_lp, one65_lp==1); 
     $display("one66_lp: %x %d", one66_lp, one66_lp==1); 
     $display("one67_lp: %x %d", one67_lp, one67_lp==1); 
     $display("one68_lp: %x %d", one68_lp, one68_lp==1); 
     $display("one69_lp: %x %d", one69_lp, one69_lp==1); 
     $display("one70_lp: %x %d", one70_lp, one70_lp==1);
`endif
  
     all_ok &= one1_lp  == 1;
     all_ok &= one2_lp  == 1;
     all_ok &= one3_lp  == 1;
     all_ok &= one4_lp  == 1;
     all_ok &= one5_lp  == 1;
     all_ok &= one6_lp  == 1;
     all_ok &= one7_lp  == 1;
     all_ok &= one8_lp  == 1;
     all_ok &= one9_lp  == 1;
     all_ok &= one10_lp == 1;
     all_ok &= one20_lp == 1;
     all_ok &= one30_lp == 1;
     all_ok &= one31_lp == 1;
     all_ok &= one32_lp == 1;
     all_ok &= one33_lp == 1;
     all_ok &= one34_lp == 1;
     all_ok &= one35_lp == 1;
     all_ok &= one36_lp == 1;
     all_ok &= one37_lp == 1;
     all_ok &= one38_lp == 1;
     all_ok &= one39_lp == 1;
     all_ok &= one40_lp == 1;
     all_ok &= one50_lp == 1;
     all_ok &= one60_lp == 1;
     all_ok &= one61_lp == 1;
     all_ok &= one62_lp == 1;
     all_ok &= one63_lp == 1;
     all_ok &= one64_lp == 1;
     all_ok &= one65_lp == 1;
     all_ok &= one66_lp == 1;
     all_ok &= one67_lp == 1;
     all_ok &= one68_lp == 1;
     all_ok &= one69_lp == 1;
     all_ok &= one70_lp == 1;
     
     if (!all_ok) $stop;
     $write("*-* All Finished *-*\n");
     $finish;
     
   end
endmodule

