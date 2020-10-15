// DESCRIPTION: Verilator: Verilog Test module
// Ref. to  IEEE Std 1800-2017  11.4.14 & A.8.1
//
// stream pack/unpack for integer_type only
// slice_size ::= simple_type | constant_expression
//  simple_type ::=
//   integer_type | non_integer_type | ps_type_identifier | ps_parameter_identifier
//                  non_integer_type ::= shortreal | real | realtime
//   integer_type ::=
//   integer_vector_type | integer_atom_type
//                         integer_atom_type ::= byte | shortint | int | longint | integer | time
//   integer_vector_type ::= bit | logic | reg
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Victor Besyakov.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [31:0] packed_data_32;
   logic [31:0] packed_data_32_ref;

   logic [31:0] v_packed_data_32;
   logic [31:0] v_packed_data_32_ref;

   logic [63:0] packed_data_64;
   logic [63:0] packed_data_64_ref;

   logic [63:0] v_packed_data_64;
   logic [63:0] v_packed_data_64_ref;

   logic [127:0] packed_data_128;
   logic [127:0] packed_data_128_ref;

   logic [127:0] v_packed_data_128;
   logic [127:0] v_packed_data_128_ref;

   logic [127:0] packed_data_128_i;
   logic [127:0] packed_data_128_i_ref;

   logic [255:0] packed_data_256;
   logic [255:0] packed_data_256_ref;

   logic [255:0] packed_time_256;
   logic [255:0] packed_time_256_ref;
   //
   //integer_atom_type
   //
   byte          byte_in[4];
   byte          byte_out[4];
   //
   int           int_in[4];
   int           int_out[4];
   //
   //
   shortint      shortint_in[4];
   shortint      shortint_out[4];
   //
   longint       longint_in[4];
   longint       longint_out[4];
   //
   integer       integer_in[4];
   integer       integer_out[4];
   //
   time          time_in[4];
   time          time_out[4];

   //integer_vector_type
   typedef bit [7:0] test_byte;
   typedef bit [15:0] test_short;
   typedef bit [31:0] test_word;
   typedef bit [63:0] test_long;
   //
   test_byte bit_in[4];
   test_byte bit_out[4];
   //
   test_short logic_in[4];
   test_short logic_out[4];
   //
   test_word reg_in[4];
   test_word reg_out[4];
   //
   string             error = "";

   initial begin
      //init
      $write("*-* START t_stream_pack_unpack *-*\n");
      error = test_integer_type_1(error);
`ifdef TEST_VERBOSE
      print_all_data("test_integer_type_1");
`endif
      error = test_integer_type_2(error);
`ifdef TEST_VERBOSE
      print_all_data("test_integer_type_2");
`endif
      //
      if (error == "") $write("*-* All Finished *-*\n");
      else begin
         $write("*-* TEST failed error %s *-*:\n", error);
         print_data_error(error);
      end
      $finish;
   end // initial begin

   function string test_integer_type_1(string error);
      automatic string error_;
      automatic string function_name_ = "test_integer_type_1";

      error_ = error;
      if (error_ == "") begin
         clean_packed_data ();
         init_data();
         //pack
         packed_data_32    = {<<8{byte_in}};
         packed_data_64    = {<<16{shortint_in}};
         packed_data_128   = {<<32{int_in}};
         packed_data_128_i = {<<32{integer_in}};
         packed_data_256   = {<<64{longint_in}};
         packed_time_256   = {<<64{time_in}};
         v_packed_data_32  = {<<8{bit_in}};
         v_packed_data_64  = {<<16{logic_in}};
         v_packed_data_128 = {<<32{reg_in}};
         //unpack
         {<<8{byte_out}}      = packed_data_32;
         {<<16{shortint_out}} = packed_data_64;
         {<<32{int_out}}      = packed_data_128;
         {<<32{integer_out}}  = packed_data_128_i;
         {<<64{longint_out}}  = packed_data_256;
         {<<64{time_out}}     = packed_time_256;
         {<<8{bit_out}}       = v_packed_data_32;
         {<<16{logic_out}}    = v_packed_data_64;
         {<<32{reg_out}}      = v_packed_data_128;
         error_ = comp_in_out();
      end // if (error == "")
      return error_;
   endfunction : test_integer_type_1

   function string test_integer_type_2(string error);
      automatic string error_;
      automatic string function_name_ = "test_integer_type_2";
      error_ = error;
      if (error_ == "") begin
         clean_packed_data ();
         init_data();
         //pack
         packed_data_32    = {<<byte{byte_in}};
         packed_data_64    = {<<shortint{shortint_in}};
         packed_data_128   = {<<int{int_in}};
         packed_data_128_i = {<<integer{integer_in}};
         packed_data_256   = {<<longint{longint_in}};
         packed_time_256   = {<<time{time_in}};
         v_packed_data_32  = {<<test_byte{bit_in}};
         v_packed_data_64  = {<<test_short{logic_in}};
         v_packed_data_128 = {<<test_word{reg_in}};
         //unpack
         {<<byte{byte_out}}         = packed_data_32;
         {<<shortint{shortint_out}} = packed_data_64;
         {<<int{int_out}}           = packed_data_128;
         {<<integer{integer_out}}   = packed_data_128_i;
         {<<longint{longint_out}}   = packed_data_256;
         {<<time{time_out}}         = packed_time_256;
         {<<test_byte{bit_out}}     = v_packed_data_32;
         {<<test_short{logic_out}}  = v_packed_data_64;
         {<<test_word{reg_out}}     = v_packed_data_128;
         error_ = comp_in_out();
      end // if (error_ == "")
      return error_;
   endfunction : test_integer_type_2

   function void clean_packed_data ();
      packed_data_32    = 0;
      packed_data_64    = 0;
      packed_data_128   = 0;
      v_packed_data_32  = 0;
      v_packed_data_64  = 0;
      v_packed_data_128 = 0;
      packed_data_128_i = 0;
      packed_data_256   = 0;
      packed_time_256   = 0;
   endfunction : clean_packed_data

   function void print_packed_data ();
      $display("TEST: packed_data_32=%0h", packed_data_32);
      $display("TEST: packed_data_64=%0h", packed_data_64);
      $display("TEST: packed_data_128=%0h", packed_data_128);
      $display("TEST: packed_data_128_i=%0h", packed_data_128_i);
      $display("TEST: packed_data_256=%0h", packed_data_256);
      $display("TEST: packed_time_256=%0h", packed_time_256);
      //
      $display("TEST: v_packed_data_32=%0h", v_packed_data_32);
      $display("TEST: v_packed_data_64=%0h", v_packed_data_64);
      $display("TEST: v_packed_data_128=%0h", v_packed_data_128);
   endfunction : print_packed_data

   function void print_data_error (string error);
      if (error == "integer_atom_type byte") begin
         foreach (byte_in[i]) $display("byte_in[%0d]=%0h, byte_out=%0h ", i, byte_in[i], byte_out[i]);
         $display("packed_data_32=%0h, packed_data_32_ref=%0h", packed_data_32, packed_data_32_ref);
      end
      if (error == "integer_atom_type shortint") begin
         foreach (shortint_in[i]) $display("shortint_in[%0d]=%0h, shortint_ou=%0h", i, shortint_in[i], shortint_out[i]);
         $display("packed_data_64=%0h, packed_data_64_ref=%0h", packed_data_64, packed_data_64_ref);
      end
      if (error == "integer_atom_type int") begin
         foreach (int_in[i]) $display("int_in[%0d]=%0h, int_out=%0h", i, int_in[i], int_out[i]);
         $display("packed_data_128=%0h, packed_data_128_ref=%0h ", packed_data_128, packed_data_128_ref);
      end
      if (error == "integer_atom_type integer") begin
         foreach (integer_in[i]) $display("integer_in[%0d]=%0h, integer_out=%0h", i, integer_in[i], integer_out[i]);
         $display("packed_data_128_i=%0h, packed_data_128_i_ref=%0h", packed_data_128_i, packed_data_128_i_ref);
      end
      if (error == "integer_atom_type longin") begin
         foreach (longint_in[i]) $display("longint_in[%0d]=%0h, longint_out=%0h", i, longint_in[i], longint_out[i]);
         $display("packed_data_256=%0h, packed_data_256_ref=%0h ", packed_data_256, packed_data_256_ref);
      end
      if (error == "integer_atom_type time") begin
         foreach (time_in[i]) $display("time_in[%0d]=%0h, time_out=%0h", i, time_in[i], time_out[i]);
         $display("packed_time_256=%0h, packed_time_256=%0h", packed_time_256, packed_time_256_ref);
      end
      //
      if (error == "integer_vector_type bit") begin
         foreach (bit_in[i]) $display("bit_in[%0d]=%0h, bit_out=%0h", i, bit_in[i], bit_out[i]);
         $display("v_packed_data_32=%0h, v_packed_data_32_ref=%0h", v_packed_data_32, v_packed_data_32_ref);
      end
      if (error == "integer_vector_type logic") begin
         foreach (logic_in[i]) $display("logic_in[%0d]=%0h, logic_out=%0h", i, logic_in[i], logic_out[i]);
         $display("v_packed_data_64=%0h, v_packed_data_64_ref=%0h", v_packed_data_64, v_packed_data_64_ref);
      end
      if (error == "integer_vector_type reg") begin
         foreach (reg_in[i]) $display("reg_in[%0d]%0h, reg_out=%0h", i, reg_in[i], reg_out[i]);
         $display("v_packed_data_128=%0h, v_packed_data_128_ref=%0h", v_packed_data_128, v_packed_data_128_ref);
      end
   endfunction : print_data_error

   function void print_all_data (string name = "");
      foreach (byte_in[i]) $display(" %s byte_in[%0d]=%0h, byte_out=%0h ", name, i, byte_in[i], byte_out[i]);
      $display(" %s packed_data_32=%0h, packed_data_32_ref=%0h", name, packed_data_32, packed_data_32_ref);

      foreach (shortint_in[i]) $display(" %s shortint_in[%0d]=%0h, shortint_ou=%0h", name, i, shortint_in[i], shortint_out[i]);
      $display(" %s packed_data_64=%0h,packed_data_64_ref=%0h", name, packed_data_64, packed_data_64_ref);

      foreach (int_in[i]) $display(" %s int_in[%0d]=%0h, int_out=%0h", name, i, int_in[i], int_out[i]);
      $display(" %s packed_data_128=%0h,packed_data_128_ref=%0h ",name, packed_data_128, packed_data_128_ref);

      foreach (integer_in[i]) $display(" %s integer_in[%0d]=%0h, integer_out=%0h", name, i, integer_in[i], integer_out[i]);
      $display(" %s packed_data_128_i=%0h,packed_data_128_i_ref=%0h", name, packed_data_128_i, packed_data_128_i_ref);

      foreach (longint_in[i]) $display(" %s longint_in[%0d]=%0h, longint_out=%0h", name, i, longint_in[i], longint_out[i]);
      $display(" %s packed_data_256=%0h, packed_data_256_ref=%0h ", name, packed_data_256, packed_data_256_ref);

      foreach (time_in[i]) $display(" %s time_in[%0d]=%0h, time_out=%0h", name, i, time_in[i], time_out[i]);
      $display(" %s packed_time_256=%0h,packed_time_256=%0h", name, packed_time_256, packed_time_256_ref);
      //
      foreach (bit_in[i]) $display(" %s bit_in[%0d]=%0h, bit_out=%0h", name, i, bit_in[i], bit_out[i]);
      $display(" %s v_packed_data_32=%0h, v_packed_data_32_ref=%0h", name, v_packed_data_32, v_packed_data_32_ref);

      foreach (logic_in[i]) $display(" %s logic_in[%0d]=%0h, logic_out=%0h", name, i, logic_in[i], logic_out[i]);
      $display(" %s v_packed_data_64=%0h, v_packed_data_64_ref=%0h", name, v_packed_data_64, v_packed_data_64_ref);

      foreach (reg_in[i]) $display(" %s reg_in[%0d]%0h, reg_out=%0h", name, i, reg_in[i], reg_out[i]);
      $display(" %s v_packed_data_128=%0h, v_packed_data_128_ref=%0h", name, v_packed_data_128, v_packed_data_128_ref);
   endfunction : print_all_data

   function void init_data();
      foreach (byte_in[i])     byte_in[i]     = byte'(i)+1;
      foreach (shortint_in[i]) shortint_in[i] = 'h100+shortint'(i)+1;
      foreach (int_in[i])      int_in[i]      = 'h200+int'(i)+1;
      foreach (integer_in[i])  integer_in[i]  = 'h300+integer'(i)+1;
      foreach (longint_in[i])  longint_in[i]  = 'h400+longint'(i)+1;
      foreach (time_in[i])     time_in[i]     = 'h500+time'(i)+1;
      //
      foreach (bit_in[i])   bit_in[i]   = 'h10+test_byte'(i)+1;
      foreach (logic_in[i]) logic_in[i] = 'h700+test_short'(i)+1;
      foreach (reg_in[i])   reg_in[i]   = 'h800+test_word'(i)+1;
      //
      packed_data_32_ref    = {byte_in[3], byte_in[2], byte_in[1], byte_in[0]};
      packed_data_64_ref    = {shortint_in[3], shortint_in[2], shortint_in[1], shortint_in[0]};
      packed_data_128_ref   = {int_in[3], int_in[2], int_in[1], int_in[0]};
      packed_data_128_i_ref = {integer_in[3], integer_in[2], integer_in[1], integer_in[0]};
      packed_data_256_ref   = {longint_in[3], longint_in[2], longint_in[1], longint_in[0]};
      packed_time_256_ref   = {time_in[3], time_in[2], time_in[1], time_in[0]};
      v_packed_data_32_ref  = {bit_in[3], bit_in[2], bit_in[1], bit_in[0]};
      v_packed_data_64_ref  = {logic_in[3], logic_in[2], logic_in[1], logic_in[0]};
      v_packed_data_128_ref = {reg_in[3], reg_in[2], reg_in[1], reg_in[0]};
      //
      packed_data_32    = 0;
      packed_data_64    = 0;
      packed_data_128   = 0;
      packed_data_128_i = 0;
      packed_data_256   = 0;
      packed_time_256   = 0;
   endfunction : init_data

   function string comp_in_out();
      automatic string error_ = "";
      automatic string function_name_ = "comp_in_out";

      if (error_ == "") foreach (byte_in[i]) if (byte_in[i] !== byte_out[i]) error_ = "integer_atom_type byte";
      if (error_ == "") if (packed_data_32 !== packed_data_32_ref) error_ = "integer_atom_type byte";

      if (error_ == "") foreach (shortint_in[i]) if (shortint_in[i] !== shortint_out[i]) error_ = "integer_atom_type shortint";
      if (error_ == "") if (packed_data_64 !== packed_data_64_ref)  error_ = "integer_atom_type shortint";

      if (error_ == "") foreach (int_in[i]) if (int_in[i] !== int_out[i]) error_ = "integer_atom_type int";
      if (error_ == "") if (packed_data_128 !== packed_data_128_ref) error_ = "integer_atom_type int";

      if (error_ == "") foreach (integer_in[i]) if (integer_in[i] !== integer_out[i]) error_ = "integer_atom_type integer";
      if (error_ == "") if (packed_data_128_i !== packed_data_128_i_ref) error_ = "integer_atom_type integer";

      if (error_ == "") foreach (longint_in[i]) if (longint_in[i] !== longint_out[i]) error_ = "integer_atom_type longin";
      if (error_ == "") if (packed_data_256 !== packed_data_256_ref) error_ = "integer_atom_type longin";

      if (error_ == "") foreach (time_in[i]) if (time_in[i] !== time_out[i]) error_ = "integer_atom_type time";
      if (error_ == "") if (packed_time_256 !== packed_time_256_ref) error_ = "integer_atom_type time";
      //
      if (error_ == "") foreach (bit_in[i]) if (bit_in[i] !== bit_out[i]) error_ = "integer_vector_type bit";
      if (error_ == "") if (v_packed_data_32 !== v_packed_data_32_ref) error_ = "integer_vector_type bit";

      if (error_ == "") foreach (logic_in[i]) if (logic_in[i] !== logic_out[i]) error_ = "integer_vector_type logic";
      if (error_ == "") if (v_packed_data_64 !== v_packed_data_64_ref) error_ = "integer_vector_type logic";

      if (error_ == "") foreach (reg_in[i]) if (reg_in[i] !== reg_out[i]) error_ = "integer_vector_type reg";
      if (error_ == "") if (v_packed_data_128 !== v_packed_data_128_ref) error_ = "integer_vector_type reg";

      return error_;
   endfunction : comp_in_out

endmodule
