// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Todd Strader.

module foo
   #(parameter type a_type = logic,
     parameter type b_type = int)
   ();

   initial begin
      if (type(a_type) != type(logic[7:0])) begin
         $display("%%Error: a_type is wrong");
         $stop();
      end

      if (type(b_type) != type(real)) begin
         $display("%%Error: b_type is wrong");
         $stop();
      end

      if (type(a_type) == type(logic)) begin
         $display("%%Error: a_type is the default value");
         $stop();
      end

      if (type(b_type) == type(int)) begin
         $display("%%Error: b_type is the default value");
         $stop();
      end

      if (type(a_type) == type(b_type)) begin
         $display("%%Error: a_type equals b_type");
         $stop();
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module t();

   foo #(
      .a_type (logic[7:0]),
      .b_type (real)) the_foo ();

   // From 6.22.1 (mostly)
   shortint shortint_v;
   int int_v;
   longint longint_v;
   byte byte_v;
   bit bit_v;
   logic logic_v;
   reg reg_v;
   integer integer_v;
   time time_v;

   typedef bit node;        // 'bit' and 'node' are matching types
   typedef node type1;
   typedef type1 type2;     // 'type1' and 'type2' are matching types

   struct packed {int A; int B;} AB1, AB2;  // AB1, AB2 have matching types
   struct packed {int A; int B;} AB3;       // the type of AB3 does not match
                                            // the type of AB1

   typedef struct packed {int A; int B;} AB_t;
   AB_t AB4; AB_t AB5;  // AB4 and AB5 have matching types
   typedef struct packed {int A; int B;} otherAB_t;
   otherAB_t AB6;       // the type of AB6 does not match the type of AB4 or AB5

   typedef bit signed [7:0] BYTE;   // matches the byte type
   /* verilator lint_off LITENDIAN */
   typedef bit signed [0:7] ETYB;   // does not match the byte type
   /* verilator lint_on LITENDIAN */
   typedef bit [7:0] UNSIGNED_BYTE;   // also does not match the byte type

   typedef byte MEM_BYTES [256];
   typedef bit signed [7:0] MY_MEM_BYTES [256];     // MY_MEM_BYTES matches
                                                    // MEM_BYTES
   typedef bit signed [7:0] [255:0] MEM_BYTES_PACKED;
   typedef bit signed [7:0] [255:0] MY_MEM_BYTES_PACKED;
   typedef logic [1:0] [3:0] NIBBLES;
   typedef logic [7:0] MY_BYTE; // MY_BYTE and NIBBLES are not matching types
   typedef logic MD_ARY [][2:0];
   typedef logic MD_ARY_TOO [][0:2]; // Does not match MD_ARY

   typedef byte signed MY_CHAR; // MY_CHAR matches the byte type

   // TODO -- this (6.22.1 h)
   //import the_pkg::*;

   bit should_be_true;

   initial begin
      if (type(shortint) != type(shortint_v)) $stop();
      if (type(int) != type(int_v)) $stop();
      if (type(longint) != type(longint_v)) $stop();
      if (type(byte) != type(byte_v)) $stop();
      if (type(bit) != type(bit_v)) $stop();
      if (type(logic) != type(logic_v)) $stop();
      if (type(reg) != type(reg_v)) $stop();
      if (type(integer) != type(integer_v)) $stop();
      if (type(time) != type(time_v)) $stop();
      if (type(bit) != type(node)) $stop();
      if (type(type1) != type(type2)) $stop();
      if (type(AB1) != type(AB2)) $stop();
      if (type(AB3) == type(AB1)) $stop();
      if (type(AB4) != type(AB5)) $stop();
      if (type(AB6) == type(AB4)) $stop();
      if (type(AB6) == type(AB5)) $stop();
      if (type(BYTE) != type(byte)) $stop();
      if (type(ETYB) == type(byte)) $stop();
      if (type(BYTE) == type(UNSIGNED_BYTE)) $stop();
      if (type(MEM_BYTES) != type(MY_MEM_BYTES)) $stop();
      if (type(MEM_BYTES_PACKED) != type(MY_MEM_BYTES_PACKED)) $stop();
      if (type(NIBBLES) == type(MY_BYTE)) $stop();
      if (type(MD_ARY) == type(MD_ARY_TOO)) $stop();
      if (type(MY_CHAR) != type(byte)) $stop();
      // TODO -- the rest
      // TODO -- case equal/not equal, ===, !===
      // TODO -- generate case
      // TODO -- test associative arrays
      // TODO -- test dynamic arrays
      // TODO -- test unsized arrays
      // TODO -- test const vars (both LHS and RHS) against const and non-const
      // TODO -- test queues
      // TODO -- test structs, enums and unions
      // TODO -- test struct member vs type

      if (type(shortint) !== type(shortint_v)) $stop();
      if (type(int) === type(shortint_v)) $stop();

      should_be_true = '0;
      case (type(shortint_v))
         type(shortint): should_be_true = '1;
         type(int): $stop();
         default: $stop();
      endcase

      if (!should_be_true) $stop();
   end


endmodule
