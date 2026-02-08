// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   initial begin
      automatic logic [7:0] src_1 = 8'b1010_0011; // 8 bits wide source
      automatic logic [1:0] dst_1 [3]; // 6 bits wide target
      automatic logic [1:0] exp_1 [3]; // 6 bits wide target

      automatic logic [1:0] src_2 [3] = '{2'b10, 2'b10, 2'b10}; // 6 bits wide source
      automatic logic [7:0] dst_2; // 8 bits wide target
      automatic logic [7:0] exp_2; // 8 bits wide target

      automatic logic [7:0] src_3 = 8'hA5; // 8 bits wide source
      automatic logic [27:0] dst_3; // 28 bits wide target
      automatic logic [27:0] exp_3; // 28 bits wide target

      automatic string expv;
      automatic string gotv;

      // unpack as target, StreamR
      {>>{dst_1}} = src_1;
      exp_1 = '{2'b10, 2'b10, 2'b00};
      expv = $sformatf("%p", exp_1);
      gotv = $sformatf("%p", dst_1);
      `checks(gotv, expv);

      // unpack as target, StreamL
      {<<{dst_1}} = src_1;
      exp_1 = '{2'b00, 2'b01, 2'b01};
      expv = $sformatf("%p", exp_1);
      gotv = $sformatf("%p", dst_1);
      `checks(gotv, expv);

      // unpack as source, StreamR
      dst_2 = {>>{src_2}};
      exp_2 = 8'b10101000;
      expv = $sformatf("%p", exp_2);
      gotv = $sformatf("%p", dst_2);
      `checks(gotv, expv);

      // unpack as source, StreamL
      dst_2 = {<<{src_2}};
      exp_2 = 8'b01010100;
      expv = $sformatf("%p", exp_2);
      gotv = $sformatf("%p", dst_2);
      `checks(gotv, expv);

      // unpack as source, StreamL
      // verilator lint_off WIDTHEXPAND
      dst_3 = {<<{src_3}};
      // verilator lint_on WIDTHEXPAND
      exp_3 = 28'hA500000;
      expv = $sformatf("%p", exp_3);
      gotv = $sformatf("%p", dst_3);
      `checks(gotv, expv);

      // unpack as source, StreamR
      // verilator lint_off WIDTHEXPAND
      dst_3 = {>>{src_3}};
      // verilator lint_on WIDTHEXPAND
      exp_3 = 28'hA500000;
      expv = $sformatf("%p", exp_3);
      gotv = $sformatf("%p", dst_3);
      `checks(gotv, expv);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
