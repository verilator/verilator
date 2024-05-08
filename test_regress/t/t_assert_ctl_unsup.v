// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
   unsupported_ctl_type unsupported_ctl_type();
   unsupported_ctl_type_expr unsupported_ctl_type_expr();
   bad_assertcontrol_ctl_type bad_assertcontrol_ctl_type();
   assert_class assert_class();
   assert_iface assert_iface();
   assert_iface_class assert_iface_class();
endmodule

module unsupported_ctl_type;
   initial begin
      $assertcontrol(1);
      $assertcontrol(2);
      $assertcontrol(6);
      $assertcontrol(7);
      $assertcontrol(8);
      $assertcontrol(9);
      $assertcontrol(10);
      $assertcontrol(11);
   end
endmodule

module unsupported_ctl_type_expr;
   int ctl_type = 1;
   initial begin
      $assertcontrol(ctl_type);
   end
endmodule

module bad_assertcontrol_ctl_type;
   initial begin
      $assertcontrol(0);
      $assertcontrol(100);
   end
endmodule

module assert_class;
   virtual class AssertCtl;
      pure virtual function void virtual_assert_ctl();
   endclass

   class AssertCls;
      static function void static_function();
         assert(0);
      endfunction
      static task static_task();
         assert(0);
      endtask
      function void assert_function();
         assert(0);
      endfunction
      task assert_task();
         assert(0);
      endtask
      virtual function void virtual_assert();
         assert(0);
      endfunction
   endclass

   class AssertOn extends AssertCtl;
      virtual function void virtual_assert_ctl();
         $asserton;
      endfunction
   endclass

   class AssertOff extends AssertCtl;
      virtual function void virtual_assert_ctl();
         $assertoff;
      endfunction
   endclass

   AssertCls assertCls;
   AssertOn assertOn;
   AssertOff assertOff;
   initial begin
      $assertoff;
      AssertCls::static_function();
      AssertCls::static_task();
      $asserton;
      AssertCls::static_function();
      AssertCls::static_task();

      assertCls = new;
      assertOn = new;
      assertOff = new;

      assertOff.virtual_assert_ctl();
      assertCls.assert_function();
      assertCls.assert_task();
      assertCls.virtual_assert();

      assertOn.virtual_assert_ctl();
      assertCls.assert_function();
      assertCls.assert_task();
      assertCls.virtual_assert();
      assertOff.virtual_assert_ctl();
      assertCls.assert_function();
   end
endmodule

interface Iface;
   function void assert_func();
      assert(0);
   endfunction

   function void assertoff_func();
      $assertoff;
   endfunction

   initial begin
      assertoff_func();
      assert(0);
      assert_func();
      $asserton;
      assert(0);
      assert_func();
   end
endinterface

module assert_iface;
   Iface iface();
   virtual Iface vIface = iface;
   initial begin
      vIface.assert_func();
      vIface.assertoff_func();
      vIface.assert_func();

      iface.assert_func();
      iface.assertoff_func();
      iface.assert_func();
   end
endmodule

interface class IfaceClass;
   pure virtual function void assertoff_func();
   pure virtual function void assert_func();
endclass

class IfaceClassImpl implements IfaceClass;
   virtual function void assertoff_func();
      $assertoff;
   endfunction
   virtual function void assert_func();
      assert(0);
   endfunction
endclass

module assert_iface_class;
   IfaceClassImpl ifaceClassImpl = new;
   initial begin
         ifaceClassImpl.assertoff_func();
         ifaceClassImpl.assert_func();
   end
endmodule
