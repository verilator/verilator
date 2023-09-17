// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef bit signed [11:0] s12_t;
typedef bit unsigned [11:0] u12_t;
typedef bit signed [69:0] s70_t;
typedef bit unsigned [69:0] u70_t;

import "DPI-C" context function void dpii_inv_s12(input s12_t in, output s12_t out);
import "DPI-C" context function void dpii_inv_u12(input u12_t in, output u12_t out);
import "DPI-C" context function void dpii_inv_s70(input s70_t in, output s70_t out);
import "DPI-C" context function void dpii_inv_u70(input s70_t in, output u70_t out);

class Cls #(type T = bit);
   static function void get(inout T value);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      value = ~value;
   endfunction
endclass

module t;

   parameter MSG_PORT_WIDTH = 4350;
   localparam PAYLOAD_MAX_BITS = 4352;

   reg [MSG_PORT_WIDTH-1:0] msg;

   function void func (output bit [PAYLOAD_MAX_BITS-1:0] data);
`ifdef TEST_NOINLINE
      // verilator no_inline_task
`endif
      data = {PAYLOAD_MAX_BITS{1'b1}};
   endfunction

   s12_t ds12;
   u12_t du12;
   s70_t ds70;
   u70_t du70;
   s12_t qs12;
   u12_t qu12;
   s70_t qs70;
   u70_t qu70;

   initial begin
      // Operator TASKREF 'func' expects 4352 bits on the Function Argument, but Function Argument's VARREF 'msg' generates 4350 bits.
      // verilator lint_off WIDTHEXPAND
      func(msg);
      if (msg !== {MSG_PORT_WIDTH{1'b1}}) $stop;

      begin
         // narrow connect to wide
         ds12 = 12'h234;
         Cls#(s70_t)::get(ds12);
         `checkh(ds12, 12'hdcb);
         ds12 = 12'he34;  // negative if signed
         Cls#(s70_t)::get(ds12);
         `checkh(ds12, 12'h1cb);

         du12 = 12'h244;
         Cls#(u70_t)::get(du12);
         `checkh(du12, 12'hdbb);
         du12 = 12'he34;  // negative if signed
         Cls#(u70_t)::get(du12);
         `checkh(du12, 12'h1cb);

         // wie connect to narrow
         ds70 = 12'h254;
         Cls#(s12_t)::get(ds70);
         `checkh(ds70, 70'h3ffffffffffffffdab);
         ds70 = 12'he34;  // negative if signed
         Cls#(s12_t)::get(ds70);
         `checkh(ds70, 70'h0000000000000001cb);

         du70 = 12'h264;
         Cls#(u12_t)::get(du70);
         `checkh(du70, 70'h000000000000000d9b);
         du70 = 12'he34;  // negative if signed
         Cls#(u12_t)::get(du70);
         `checkh(du70, 70'h0000000000000001cb);
      end

      begin
         // narrow connect to wide
         ds12 = 12'h234;
         dpii_inv_s70(ds12, qs12);
         `checkh(qs12, 12'hdcb);
         ds12 = 12'he34;  // negative if signed
         dpii_inv_s70(ds12, qs12);
         `checkh(qs12, 12'h1cb);

         du12 = 12'h244;
         dpii_inv_u70(du12, qu12);
         `checkh(qu12, 12'hdbb);
         du12 = 12'he34;  // negative if signed
         dpii_inv_u70(ds12, qs12);
         `checkh(qs12, 12'h1cb);

         // wie connect to narrow
         ds70 = 12'h254;
         dpii_inv_s12(ds70, qs70);
         `checkh(qs70, 70'h3ffffffffffffffdab);
         ds70 = 12'he34;  // negative if signed
         dpii_inv_s12(ds70, qs70);
         `checkh(qs70, 70'h0000000000000001cb);

         du70 = 12'h264;
         dpii_inv_u12(du70, qu70);
         `checkh(qu70, 70'h000000000000000d9b);
         du70 = 12'he34;  // negative if signed
         dpii_inv_u12(du70, qu70);
         `checkh(qu70, 70'h0000000000000001cb);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
