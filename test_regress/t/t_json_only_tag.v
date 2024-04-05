// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Chris Randall.
// SPDX-License-Identifier: CC0-1.0

interface ifc;
   integer value;
   modport out_modport (output value);
endinterface

module m
  (
   input  clk_ip, //  verilator tag clk_ip
   input  rst_ip,
   output foo_op);  // verilator tag foo_op

   // This is a comment

   typedef struct packed  {
      logic       clk;    /* verilator tag this is clk */
      logic       k;      /* verilator lint_off UNUSED */
      logic       enable; // verilator tag enable
      logic       data;   // verilator tag data
   } my_struct;  // verilator tag my_struct

   // This is a comment

   ifc itop();

   my_struct this_struct [2];  // verilator tag this_struct

   wire [31:0] dotted = itop.value;

   function f(input string m);
      $display("%s", m);
   endfunction

   initial begin
      // Contains all 256 characters except 0 (null character)
      f("\x01\x02\x03\x04\x05\x06\a\x08\t\n\v\f\r\x0e\x0f\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\x7f\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7\xc8\xc9\xca\xcb\xcc\xcd\xce\xcf\xd0\xd1\xd2\xd3\xd4\xd5\xd6\xd7\xd8\xd9\xda\xdb\xdc\xdd\xde\xdf\xe0\xe1\xe2\xe3\xe4\xe5\xe6\xe7\xe8\xe9\xea\xeb\xec\xed\xee\xef\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9\xfa\xfb\xfc\xfd\xfe\xff");
   end

endmodule
