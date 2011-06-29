// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer 	cyc=0;
   reg [63:0] 	crc;
   reg [63:0] 	sum;

   // Take CRC data and apply to testblock inputs
   wire [3:0]  l_stop     = crc[3:0];
   wire [3:0]  l_break    = crc[7:4];
   wire [3:0]  l_continue = crc[11:8];

   /*AUTOWIRE*/

   wire [15:0] out0 = Test0(l_stop, l_break, l_continue);
   wire [15:0] out1 = Test1(l_stop, l_break, l_continue);
   wire [15:0] out2 = Test2(l_stop, l_break, l_continue);
   wire [15:0] out3 = Test3(l_stop, l_break, l_continue);

   // Aggregate outputs into a single result vector
   wire [63:0] result = {out3,out2,out1,out0};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
	 // Setup
	 crc <= 64'h5aef0c8d_d70a4497;
	 sum <= 64'h0;
      end
      else if (cyc<10) begin
	 sum <= 64'h0;
      end
      else if (cyc<90) begin
	 if (out0!==out1) $stop;
	 if (out0!==out2) $stop;
	 if (out0!==out3) $stop;
      end
      else if (cyc==99) begin
	 $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
	 if (crc !== 64'hc77bb9b3784ea091) $stop;
	 // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h293e9f9798e97da0
	 if (sum !== `EXPECTED_SUM) $stop;
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

   function [15:0] Test0;
      input  [3:0] loop_stop;
      input [3:0]  loop_break;
      input [3:0]  loop_continue;
      integer 	   i;
      reg 	   broken;

      Test0 = 0;
      broken = 0;
      begin
	 for (i=1; i<20; i=i+1) begin
	    if (!broken) begin
	       Test0 = Test0 + 1;
	       if (i[3:0] != loop_continue) begin // continue
		  if (i[3:0] == loop_break) begin
		     broken = 1'b1;
		  end
		  if (!broken) begin
		     Test0 = Test0 + i[15:0];
		  end
	       end
	    end
	 end
      end
   endfunction

   function [15:0] Test1;
      input  [3:0] loop_stop;
      input  [3:0] loop_break;
      input  [3:0] loop_continue;
      integer 	     i;

      Test1 = 0;
      begin : outer_block
         for (i=1; i<20; i=i+1) begin : inner_block
   	 Test1 = Test1 + 1;
	 // continue, IE jump to end-of-inner_block.  Must be inside inner_block.
         if (i[3:0] == loop_continue) disable inner_block;
	 // break, IE jump to end-of-outer_block.  Must be inside outer_block.
   	 if (i[3:0] == loop_break) disable outer_block;
   	 Test1 = Test1 + i[15:0];
         end : inner_block
      end : outer_block
   endfunction

   function [15:0] Test2;
      input  [3:0] loop_stop;
      input  [3:0] loop_break;
      input  [3:0] loop_continue;
      integer 	     i;

      Test2 = 0;
      begin
         for (i=1; i<20; i=i+1) begin
   	 Test2 = Test2 + 1;
   	 if (i[3:0] == loop_continue) continue;
   	 if (i[3:0] == loop_break) break;
   	 Test2 = Test2 + i[15:0];
         end
      end
   endfunction

   function [15:0] Test3;
      input  [3:0] loop_stop;
      input  [3:0] loop_break;
      input  [3:0] loop_continue;
      integer 	     i;

      Test3 = 0;
      begin
         for (i=1; i<20; i=i+1) begin
   	 Test3 = Test3 + 1;
   	 if (i[3:0] == loop_continue) continue;
	 // return, IE jump to end-of-function optionally setting return value
   	 if (i[3:0] == loop_break) return Test3;
   	 Test3 = Test3 + i[15:0];
         end
      end
   endfunction

endmodule
