// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  byte dyn[][1:0];

  function automatic int sum3(int a[3]);
    return a[0] * 100 + a[1] * 10 + a[2];
  endfunction

  initial begin
    begin
      dyn = new[3];
      dyn[0] = '{101, 100};
      dyn[1] = '{111, 110};
      dyn[2] = '{121, 120};
      `checkh(dyn[0][0], 100);
      `checkh(dyn[0][1], 101);
      `checkh(dyn[1][0], 110);
      `checkh(dyn[1][1], 111);
      `checkh(dyn[2][0], 120);
      `checkh(dyn[2][1], 121);
    end

    begin
      // Issue #6907
      int a[2][100:1];
      int b[];
      int d[3][][];
      b = new[100];
      for (int i = 0; i < 100; ++i) b[i] = i + 1;
      a[1] = b;
      `checkd(a[1][100], 1);
      `checkd(a[1][1], 100);
      d[2] = new[2];
      d[2][0] = new[100];
      d[2][1] = b;
      a = d[2];
      `checkd(a[1][100], 1);
      `checkd(a[1][1], 100);
    end

    begin
      // Issue #6988, queue and dynamic array to a large fixed array
      byte unsigned fixed[256];
      byte unsigned q[$];
      byte unsigned dyn[];
      for (int i = 0; i < 256; ++i) q.push_back(8'(i));
      fixed = q;
      `checkd(fixed[255], 255);
      dyn = new[256];
      for (int i = 0; i < 256; ++i) dyn[i] = 8'(255 - i);
      fixed = dyn;
      `checkd(fixed[0], 255);
      `checkd(fixed[255], 0);
    end

    begin
      // Queue source, ascending and descending targets, initializer and argument
      int q[$];
      int dd[][];
      int asc[0:2];
      int desc[3:1];
      int c[2][2:1];
      q = '{1, 2, 3};
      dd = '{'{1, 2}, '{3, 4}};
      asc = q;
      desc = q;
      c = dd;
      `checkd(asc[0], 1);
      `checkd(asc[2], 3);
      `checkd(desc[3], 1);
      `checkd(desc[1], 3);
      `checkd(c[0][2], 1);
      `checkd(c[1][1], 4);
      `checkd(sum3(q), 123);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
