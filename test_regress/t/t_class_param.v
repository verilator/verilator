// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

// See also t_class_param_mod.v

typedef class Cls;

class Wrap #(parameter P = 13);
   function int get_p;
      return c1.get_p();
   endfunction
   function new;
      c1 = new;
   endfunction
   Cls#(PMINUS1 + 1) c1;
   localparam PMINUS1 = P - 1;  // Checking works when last
endclass

class Wrap2 #(parameter P = 35);
   function int get_p;
      return c1.get_p();
   endfunction
   function new;
      c1 = new;
   endfunction
   Wrap#(PMINUS1 + 1) c1;
   localparam PMINUS1 = P - 1;  // Checking works when last
endclass

class Cls #(parameter PBASE = 12);
   bit [PBASE-1:0] member;
   function bit [PBASE-1:0] get_member;
      return member;
   endfunction
   static function int get_p;
      return PBASE;
   endfunction
   typedef enum { E_PBASE = PBASE } enum_t;
endclass

typedef Cls#(8) Cls8_t;

class SelfRefClassTypeParam #(type T=logic);
   typedef SelfRefClassTypeParam #(int) self_int_t;
   T field;
endclass

class SelfRefClassIntParam #(int P=1);
   typedef SelfRefClassIntParam #(10) self_int_t;
endclass

class Sum #(type T);
   static int sum;
   static function void add(T element);
      sum += int'(element);
      endfunction
endclass

class IntQueue;
   int          q[$];
   function int getSum();
      foreach(q[i])
        Sum#(int)::add(q[i]);
      return Sum#(int)::sum;
   endfunction
endclass

class ClsStatic;
   static int   x = 1;
   static function int get_2;
      return 2;
   endfunction
endclass

class ClsParam #(type T);
   typedef T param_t;
endclass

class ClsWithParamField;
   int m_field = Sum#(int)::sum;
   int m_queue[$];

   function int get(int index);
      return m_queue[index];
   endfunction
endclass

class DictWrapper;
   int m_dict[string];
endclass

class DictOperator #(type T) extends T;
   function void set(string s, int x);
      m_dict[s] = x;
   endfunction

   function int get(string s);
      return m_dict[s];
   endfunction
endclass

class Getter1 #(int T=0);
   static function int get_1();
      return Getter1#(1)::T;
   endfunction
endclass

class Getter2 #(int T=5);
   static function int get_T();
      return T;
   endfunction

   static function int get_2();
      return Getter2#(2)::get_T();
   endfunction
endclass

class ClsParamString #(string S="abcde");
   typedef ClsParamString#(S) this_type;
   static this_type m_inst;
   int x = 0;
   string name = S;
endclass

typedef ClsParamString#("abcde") cls_param_string_def_t;
typedef ClsParamString#("xyz") cls_param_string_not_def_t;

module t (/*AUTOARG*/);

   Cls c12;
   Cls #(.PBASE(4)) c4;
   Cls8_t c8;
   Wrap #(.P(16)) w16;
   Wrap2 #(.P(32)) w32;
   SelfRefClassTypeParam src_logic;
   SelfRefClassTypeParam#()::self_int_t src_int;
   SelfRefClassIntParam src1;
   SelfRefClassIntParam#()::self_int_t src10;
   IntQueue qi;
   ClsWithParamField cls_param_field;
   DictOperator #(DictWrapper) dict_op;
   Getter1 getter1;
   Getter1 #(1) getter1_param_1;
   Getter2 getter2;
   cls_param_string_def_t cps_def;
   cls_param_string_not_def_t cps_not_def;
   int arr [1:0] = '{1, 2};
   initial begin
      c12 = new;
      c4 = new;
      c8 = new;
      w16 = new;
      w32 = new;
      src_int = new;
      src_logic = new;
      src1 = new;
      src10 = new;
      qi = new;
      cls_param_field = new;
      dict_op = new;
      getter1 = new;
      getter1_param_1 = new;
      getter2 = new;

      if (Cls#()::PBASE != 12) $stop;
      if (Cls#(4)::PBASE != 4) $stop;
      if (Cls8_t::PBASE != 8) $stop;

      if (Cls#()::E_PBASE != 12) $stop;
      if (Cls#(4)::E_PBASE != 4) $stop;
      if (Cls8_t::E_PBASE != 8) $stop;

      if (c12.PBASE != 12) $stop;
      if (c4.PBASE != 4) $stop;
      if (c8.PBASE != 8) $stop;

      if (Cls#()::get_p() != 12) $stop;
      if (Cls#(4)::get_p() != 4) $stop;
      if (Cls8_t::get_p() != 8) $stop;

      if (c12.get_p() != 12) $stop;
      if (c4.get_p() != 4) $stop;
      if (c8.get_p() != 8) $stop;
      if (w16.get_p() != 16) $stop;
      if (w32.get_p() != 32) $stop;

      // verilator lint_off WIDTH
      c12.member = 32'haaaaaaaa;
      c4.member = 32'haaaaaaaa;
      c8.member = 32'haaaaaaaa;
      // verilator lint_on WIDTH
      if (c12.member != 12'haaa) $stop;
      if (c4.member != 4'ha) $stop;
      if (c12.get_member() != 12'haaa) $stop;
      if (c4.get_member() != 4'ha) $stop;
      `checks($sformatf("%p", c12), "'{member:'haaa}");
      `checks($sformatf("%p", c4), "'{member:'ha}");

      if ($bits(src_logic.field) != 1) $stop;
      if ($bits(src_int.field) != 32) $stop;
      if (src1.P != 1) $stop;
      if (src10.P != 10) $stop;

      qi.q = '{2, 4, 6, 0, 2};
      if (qi.getSum() != 14) $stop;
      Sum#(int)::add(arr[0]);
      if(Sum#(int)::sum != 16) $stop;
      if(Sum#(real)::sum != 0) $stop;

      if (ClsParam#(ClsStatic)::param_t::x != 1) $stop;
      if (ClsParam#(ClsStatic)::param_t::get_2() != 2) $stop;

      cls_param_field.m_queue = '{1, 5, 7};
      if (cls_param_field.get(2) != 7) $stop;

      dict_op.set("abcd", 1);
      if(dict_op.get("abcd") != 1) $stop;

      if (getter1.get_1() != 1) $stop;
      if (Getter1#()::get_1() != 1) $stop;
      if (getter1_param_1.get_1() != 1) $stop;

      if (getter2.get_2() != 2) $stop;
      if (Getter2#()::get_2() != 2) $stop;
      if (Getter2#(2)::get_2() != 2) $stop;

      cls_param_string_def_t::m_inst = new;
      cls_param_string_def_t::m_inst.x = 1;
      cps_def = cls_param_string_def_t::m_inst;
      if (cps_def.x != 1) $stop;
      if (cps_def.name != "abcde") $stop;

      cls_param_string_not_def_t::m_inst = new;
      cls_param_string_not_def_t::m_inst.x = 2;
      cps_not_def = cls_param_string_not_def_t::m_inst;
      if (cps_not_def.x != 2) $stop;
      if (cps_not_def.name != "xyz") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
