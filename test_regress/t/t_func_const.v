// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package testpackage;
 localparam PARAM = 1024 >> 3;
endpackage
import testpackage::*;

module t;

   localparam P4 = f_add(P3,1);
   localparam P8 = f_add2(P3,P3,f_add(1,1));
   localparam P5 = f_while(7);
   localparam P16 = f_for(P4);
   localparam P18 = f_case(P4);
   localparam P6 = f_return(P4);
   localparam P3 = 3;
   localparam P128 = f_package();

   typedef struct packed {
      logic [7:0] data;
   } type_t;
   typedef type_t [1:0] flist;
   localparam flist PLIST = {8'd4,8'd8};
   localparam flist PARR = f_list_swap_2(PLIST);
   typedef struct packed {
      logic first;
      logic second;
      logic [31:0] data;
   } bigstruct_t;
   localparam bigstruct_t bigparam = f_return_struct(1'b1, 1'b0, 32'hfff12fff);

   initial begin
`ifdef TEST_VERBOSE
      $display("P5=%0d P8=%0d P16=%0d P18=%0d",P5,P8,P16,P18);
`endif
      if (P3 !== 3) $stop;
      if (P4 !== 4) $stop;
      if (P5 !== 5) $stop;
      if (P6 !== 6) $stop;
      if (P8 !== 8) $stop;
      if (P16 !== 16) $stop;
      if (P18 !== 18) $stop;
      if (PARR[0] != PLIST[1]) $stop;
      if (PARR[1] != PLIST[0]) $stop;
      if (bigparam.first != 1'b1) $stop;
      if (bigparam.second != 1'b0) $stop;
      if (bigparam.data != 32'hfff12fff) $stop;
      if (P128 != 128) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

   function integer f_package();
      return PARAM;
   endfunction

   function integer f_add(input [31:0] a, input [31:0] b);
      f_add = a+b;
   endfunction

   // Speced ok: function called from function
   function integer f_add2(input [31:0] a, input [31:0] b, input [31:0] c);
      f_add2 = f_add(a,b)+c;
   endfunction

   // Speced ok: local variables
   function integer f_for(input [31:0] a);
      integer i;
      integer times;
      begin
         times = 1;
         for (i=0; i<a; i=i+1) times = times*2;
         f_for = times;
      end
   endfunction

   function integer f_while(input [31:0] a);
      integer i;
      begin
         i=0;
         begin : named
            f_while = 1;
         end : named
         while (i<=a) begin
            if (i[0]) f_while = f_while + 1;
            i = i + 1;
         end
      end
   endfunction

   // Speced ok: local variables
   function integer f_case(input [31:0] a);
      case(a)
        32'd1: f_case = 1;
        32'd0, 32'd4: f_case = 18;
        32'd1234: begin $display("never get here"); $stop; end
        default: f_case = 99;
      endcase
   endfunction

   function integer f_return(input [31:0] a);
      integer out = 2;
      while (1) begin
         out = out+1;
         if (a>1) break;
      end
      while (1) begin
         out = out+1;
         if (a>1) return 2+out;
      end
      f_return = 0;
   endfunction

   function flist f_list_swap_2(input flist in_list);
      f_list_swap_2[0].data = in_list[1].data;
      f_list_swap_2[1].data = in_list[0].data;
   endfunction

   function bigstruct_t f_return_struct(input first, input second, input [31:0] data);
      bigstruct_t result;
      result.data = data;
      result.first = first;
      result.second = second;
      return result;
   endfunction
endmodule
