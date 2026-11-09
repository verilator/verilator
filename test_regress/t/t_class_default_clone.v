// DESCRIPTION: Verilator: Verilog Test module
// SPDX-License-Identifier: CC0-1.0

package p8;
   class Types;
      typedef logic [7:0] T;
      typedef enum int { READY = 5 } status_t;
      static int count = 0;
      function new(); count++; endfunction
   endclass
endpackage

package p16;
   class Types;
      typedef logic [15:0] T;
      typedef enum int { READY = 13 } status_t;
      static int count = 0;
      function new(); count++; endfunction
   endclass
endpackage

class Other;
   static int shared = 11;
endclass

class Plain;
   typedef enum int { READY = 3 } status_t;
   int x = 1;
   static int shared = 3;
   static int count = 0;
   function new(); count++; endfunction
   function int argument(int x); return x; endfunction
   function int local_value(); int x = 7; return x; endfunction
   function int local_enum_value();
      typedef enum int { READY = 17, LOCAL_ONLY = 19 } local_t;
      local_t value = READY;
      if (LOCAL_ONLY != 19) $stop;
      return int'(value);
   endfunction
   function int block_enum_value();
      int result;
      begin : local_block
         typedef enum int { READY = 23, BLOCK_ONLY = 29 } block_t;
         block_t value = READY;
         result = int'(value) + int'(BLOCK_ONLY);
      end
      return result;
   endfunction
   static function int foreign_value(); return Other::shared; endfunction
endclass

class Outer #(int ID = 1);
   class Inner;
      static int count = 0;
      function new(); count++; endfunction
      function int owner(); return ID; endfunction
   endclass
   class Unused #(type T = int);
      T value;
      function new(); value = new; endfunction
   endclass
   typedef logic [ID+7:0] payload_t;
   typedef Outer::payload_t copy_t;
endclass

class Holder #(type T = int);
   T value;
   static function Holder#(T) create();
      Holder#(T) h = new;
      return h;
   endfunction
endclass

class Types;
   class Nested;
   endclass
   typedef logic [7:0] byte_t;
   typedef byte_t values_t[$];
   typedef enum int { READY = 3, BUSY = 7 } status_t;
   typedef Holder#(values_t) queue_holder_t;
   typedef Holder#(byte_t) type_id;
endclass

class InheritedEnums extends Types;
   static function int value(); return int'(READY); endfunction
endclass

class HiddenEnums extends Types;
   typedef enum int { READY = 11 } own_state_t;
   static function int value(); return int'(READY); endfunction
endclass

module t;
   typedef Outer#() O0;
   typedef Outer#(1) O1;
   typedef Outer#(2) O2;
   typedef O0::Inner I0;
   typedef O1::Inner I1;
   typedef O2::Inner I2;
   typedef Holder#(p8::Types::T) P8Box;
   typedef Holder#(p16::Types::T) P16Box;

   initial begin
      automatic Plain p = new;
      automatic I0 i0 = new;
      automatic I1 i1 = new;
      automatic I2 i2 = new;
      automatic Types::queue_holder_t h = new;
      automatic Types::type_id b = Types::type_id::create();
      automatic p8::Types p8_first = new;
      automatic p8::Types p8_second = new;
      automatic p16::Types p16_first = new;
      automatic P8Box p8_box = new;
      automatic P16Box p16_box = new;
      automatic O0::copy_t default_copy = 9'h1a5;
      automatic O2::copy_t override_copy = 10'h2a5;
      i0 = i1;
      if (Plain::count != 1) $stop;
      if (p.argument(9) != 9 || p.local_value() != 7) $stop;
      if (Plain::READY != 3 || p.local_enum_value() != 17) $stop;
      if (p.block_enum_value() != 52) $stop;
      if (Plain::foreign_value() != 11 || Other::shared != 11) $stop;
      if (I0::count != 2 || I1::count != 2 || I2::count != 1) $stop;
      if (i0.owner() != 1 || i2.owner() != 2) $stop;
      if ($bits(default_copy) != 9 || $bits(override_copy) != 10) $stop;
      if (default_copy != 9'h1a5 || override_copy != 10'h2a5) $stop;
      h.value.push_back(8'h5a);
      h.value.push_back(8'ha5);
      if (h.value.pop_front() != 8'h5a || h.value.pop_front() != 8'ha5) $stop;
      if ($bits(b.value) != 8) $stop;
      if (Types::READY != 3 || Types::BUSY != 7) $stop;
      if (InheritedEnums::READY != 3 || InheritedEnums::value() != 3) $stop;
      if (HiddenEnums::READY != 11 || HiddenEnums::value() != 11 || Types::READY != 3) $stop;
      if (p8::Types::count != 2 || p16::Types::count != 1) $stop;
      if (p8::Types::READY != 5 || p16::Types::READY != 13) $stop;
      if ($bits(p8_box.value) != 8 || $bits(p16_box.value) != 16) $stop;
      p8_box.value = 8'h5a;
      p16_box.value = 16'hc35a;
      if (p8_box.value != 8'h5a || p16_box.value != 16'hc35a) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
