// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  initial begin
    automatic logic [7:0] src_1 = 8'b1010_0011;  // 8 bits wide source
    automatic logic [1:0] dst_1[3];  // 6 bits wide target
    automatic logic [1:0] exp_1[3];  // 6 bits wide target

    automatic logic [1:0] src_2[3] = '{2'b10, 2'b10, 2'b10};  // 6 bits wide source
    automatic logic [7:0] dst_2;  // 8 bits wide target
    automatic logic [7:0] exp_2;  // 8 bits wide target

    automatic logic [7:0] src_3 = 8'hA5;  // 8 bits wide source
    automatic logic [27:0] dst_3;  // 28 bits wide target
    automatic logic [27:0] exp_3;  // 28 bits wide target

    automatic logic [31:0] src_4[2] = '{32'h11223344, 32'h55667788};  // 64 bits wide source
    automatic logic [95:0] dst_4;  // 96 bits wide target
    automatic logic [95:0] exp_4;  // 96 bits wide target

    automatic logic [31:0] src_5[3] = '{32'h11223344, 32'h55667788, 32'h99aabbcc};  // 96 bits
    automatic logic [39:0] dst_5;  // 40 bits wide target

    automatic string expv;
    automatic string gotv;

    // Unpack as target, StreamR
    {>>{dst_1}} = src_1;
    exp_1 = '{2'b10, 2'b10, 2'b00};
    expv = $sformatf("%p", exp_1);
    gotv = $sformatf("%p", dst_1);
    `checks(gotv, expv);

    // Unpack as target, StreamL
    {<<{dst_1}} = src_1;
    exp_1 = '{2'b00, 2'b01, 2'b01};
    expv = $sformatf("%p", exp_1);
    gotv = $sformatf("%p", dst_1);
    `checks(gotv, expv);

    // Unpack as source, StreamR
    dst_2 = {>>{src_2}};
    exp_2 = 8'b10101000;
    expv = $sformatf("%p", exp_2);
    gotv = $sformatf("%p", dst_2);
    `checks(gotv, expv);

    // Unpack as source, StreamL
    dst_2 = {<<{src_2}};
    exp_2 = 8'b01010100;
    expv = $sformatf("%p", exp_2);
    gotv = $sformatf("%p", dst_2);
    `checks(gotv, expv);

    // Unpack as source, StreamL
    // verilator lint_off WIDTHEXPAND
    dst_3 = {<<{src_3}};
    // verilator lint_on WIDTHEXPAND
    exp_3 = 28'hA500000;
    expv = $sformatf("%p", exp_3);
    gotv = $sformatf("%p", dst_3);
    `checks(gotv, expv);

    // Unpack as source, StreamR
    // verilator lint_off WIDTHEXPAND
    dst_3 = {>>{src_3}};
    // verilator lint_on WIDTHEXPAND
    exp_3 = 28'hA500000;
    expv = $sformatf("%p", exp_3);
    gotv = $sformatf("%p", dst_3);
    `checks(gotv, expv);

    // Unpack as source, StreamR, wider target (#8907)
    dst_4 = {>>{src_4}};
    exp_4 = 96'h112233445566778800000000;
    `checkh(dst_4, exp_4);

    // Unpack as source, StreamR, narrower target
    // verilator lint_off WIDTHTRUNC
    dst_5 = {>>{src_5}};
    // verilator lint_on WIDTHTRUNC
    `checkh(dst_5, 40'h8899aabbcc);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
