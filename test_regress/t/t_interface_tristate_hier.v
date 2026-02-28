// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// verilator lint_off MULTIDRIVEN

interface ifc;
   wire we0, we2;
   tri [15:0] d;
endinterface

interface ifc_multi;
   wire we0, wea, web;
   tri [15:0] d;
endinterface

module bot (
   ifc io_ifc
);
   assign io_ifc.d = io_ifc.we2 ? 16'hd2 : 16'hzzzz;
endmodule

module passthru (
   ifc io_ifc
);
   bot u_bot (.*);
endmodule

module bot_a (
   ifc_multi io_ifc
);
   assign io_ifc.d = io_ifc.wea ? 16'hd2 : 16'hzzzz;
endmodule

module bot_b (
   ifc_multi io_ifc
);
   assign io_ifc.d = io_ifc.web ? 16'hd2 : 16'hzzzz;
endmodule

module passthru_multi_c (
   ifc_multi io_ifc
);
   bot_a u_bot_a (.*);
   bot_b u_bot_b (.*);
endmodule

module passthru_deep (
   ifc io_ifc
);
   passthru u_inner (.*);
endmodule

module t;
   ifc io_ifc ();
   ifc io_ifc_local ();
   ifc io_ifc_b0 ();
   ifc io_ifc_b1 ();
   ifc_multi io_ifc_mc ();
   ifc io_arr [1:0]();
   ifc io_ifc_deep ();

   // Test top assignment
   assign io_ifc.d = io_ifc.we0 ? 16'hd0 : 16'hzzzz;
   assign io_ifc_local.d = io_ifc_local.we0 ? 16'hd0 : 16'hzzzz;
   assign io_ifc_mc.d = io_ifc_mc.we0 ? 16'hd0 : 16'hzzzz;

   logic we0, we2;
   logic we2_b0, we2_b1;
   logic we0_mc, wea_mc, web_mc;
   assign io_ifc.we0 = we0;
   assign io_ifc.we2 = we2;
   assign io_ifc_local.we0 = we0;
   assign io_ifc_local.we2 = 1'b0;
   assign io_ifc_b0.we0 = 1'b0;
   assign io_ifc_b0.we2 = we2_b0;
   assign io_ifc_b1.we0 = 1'b0;
   assign io_ifc_b1.we2 = we2_b1;
   assign io_ifc_mc.we0 = we0_mc;
   assign io_ifc_mc.wea = wea_mc;
   assign io_ifc_mc.web = web_mc;

   // Interface array signals
   logic we2_arr0, we2_arr1;
   assign io_arr[0].we0 = 1'b0;
   assign io_arr[0].we2 = we2_arr0;
   assign io_arr[1].we0 = 1'b0;
   assign io_arr[1].we2 = we2_arr1;

   // Deep nesting signals
   logic we0_deep, we2_deep;
   assign io_ifc_deep.we0 = we0_deep;
   assign io_ifc_deep.we2 = we2_deep;
   assign io_ifc_deep.d = io_ifc_deep.we0 ? 16'hd0 : 16'hzzzz;

   passthru u_passthru (.*);
   passthru u_passthru_b0 (.io_ifc(io_ifc_b0));
   passthru u_passthru_b1 (.io_ifc(io_ifc_b1));
   passthru_multi_c u_passthru_mc (.io_ifc(io_ifc_mc));
   passthru u_passthru_arr0 (.io_ifc(io_arr[0]));
   passthru u_passthru_arr1 (.io_ifc(io_arr[1]));
   passthru_deep u_passthru_deep (.io_ifc(io_ifc_deep));

   initial begin
      #1;
      we0 = 1'b0;
      we2 = 1'b0;
      we2_b0 = 1'b0;
      we2_b1 = 1'b0;
      we0_mc = 1'b0;
      wea_mc = 1'b0;
      web_mc = 1'b0;
      we2_arr0 = 1'b0;
      we2_arr1 = 1'b0;
      we0_deep = 1'b0;
      we2_deep = 1'b0;
      #1;
      `checkh(io_ifc.d, 16'hzzzz);
      `checkh(io_ifc_local.d, 16'hzzzz);
      `checkh(io_ifc_b0.d, 16'hzzzz);
      `checkh(io_ifc_b1.d, 16'hzzzz);
      `checkh(io_ifc_mc.d, 16'hzzzz);
      `checkh(io_arr[0].d, 16'hzzzz);
      `checkh(io_arr[1].d, 16'hzzzz);
      `checkh(io_ifc_deep.d, 16'hzzzz);

      #1;
      we0 = 1'b1;
      we2 = 1'b0;
      #1;
      `checkh(io_ifc.d, 16'hd0);
      `checkh(io_ifc_local.d, 16'hd0);

      #1;
      we0 = 1'b0;
      we2 = 1'b0;
      #1;
      `checkh(io_ifc.d, 16'hzzzz);
      `checkh(io_ifc_local.d, 16'hzzzz);

      #1;
      we0 = 1'b0;
      we2 = 1'b1;
      #1;
      `checkh(io_ifc.d, 16'hd2);
      `checkh(io_ifc_local.d, 16'hzzzz);

      // Interface passed a->b, where b is instantiated multiple times (separate interfaces)
      #1;
      we2_b0 = 1'b1;
      we2_b1 = 1'b0;
      #1;
      `checkh(io_ifc_b0.d, 16'hd2);
      `checkh(io_ifc_b1.d, 16'hzzzz);

      #1;
      we2_b0 = 1'b0;
      we2_b1 = 1'b1;
      #1;
      `checkh(io_ifc_b0.d, 16'hzzzz);
      `checkh(io_ifc_b1.d, 16'hd2);

      #1;
      we2_b0 = 1'b0;
      we2_b1 = 1'b0;
      #1;
      `checkh(io_ifc_b0.d, 16'hzzzz);
      `checkh(io_ifc_b1.d, 16'hzzzz);

      // Interface passed a->b, where c is instantiated multiple times (same interface)
      #1;
      we0_mc = 1'b1;
      wea_mc = 1'b0;
      web_mc = 1'b0;
      #1;
      `checkh(io_ifc_mc.d, 16'hd0);

      #1;
      we0_mc = 1'b0;
      wea_mc = 1'b1;
      web_mc = 1'b0;
      #1;
      `checkh(io_ifc_mc.d, 16'hd2);

      #1;
      we0_mc = 1'b0;
      wea_mc = 1'b0;
      web_mc = 1'b1;
      #1;
      `checkh(io_ifc_mc.d, 16'hd2);

      #1;
      wea_mc = 1'b1;
      web_mc = 1'b1;
      #1;
      `checkh(io_ifc_mc.d, 16'hd2);

      #1;
      wea_mc = 1'b0;
      web_mc = 1'b0;
      #1;
      `checkh(io_ifc_mc.d, 16'hzzzz);

      // Interface array: each element is independent
      #1;
      we2_arr0 = 1'b1;
      we2_arr1 = 1'b0;
      #1;
      `checkh(io_arr[0].d, 16'hd2);
      `checkh(io_arr[1].d, 16'hzzzz);

      #1;
      we2_arr0 = 1'b0;
      we2_arr1 = 1'b1;
      #1;
      `checkh(io_arr[0].d, 16'hzzzz);
      `checkh(io_arr[1].d, 16'hd2);

      #1;
      we2_arr0 = 1'b0;
      we2_arr1 = 1'b0;
      #1;
      `checkh(io_arr[0].d, 16'hzzzz);
      `checkh(io_arr[1].d, 16'hzzzz);

      // Deep nesting: passthru_deep -> passthru -> bot (3 levels)
      #1;
      we0_deep = 1'b1;
      we2_deep = 1'b0;
      #1;
      `checkh(io_ifc_deep.d, 16'hd0);

      #1;
      we0_deep = 1'b0;
      we2_deep = 1'b1;
      #1;
      `checkh(io_ifc_deep.d, 16'hd2);

      #1;
      we0_deep = 1'b0;
      we2_deep = 1'b0;
      #1;
      `checkh(io_ifc_deep.d, 16'hzzzz);

      #1;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
