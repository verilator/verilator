// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Dynamic arrays and queues passed as DPI open arrays (IEEE 1800-2023 7.7)

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;

  typedef byte bytes_t[];

  import "DPI-C" function int dpii_failure();

  // Issue #5863 reproducer
  import "DPI-C" context function byte dpii_fill(
    input longint base,
    inout byte buffer[]
  );

  // Inverts each element, xored with its index, and returns the size
  import "DPI-C" function int dpii_invert(inout byte io[]);

  // As dpii_invert, of an argument named as a C++ keyword
  // verilator lint_off SYMRSVDWORD
  import "DPI-C" function int dpii_invert_kw(inout byte template[]);
  // verilator lint_on SYMRSVDWORD

  // Swaps the elements of arrays of the same size
  import "DPI-C" function void dpii_swap(
    inout int a[],
    inout int b[]
  );

  // Returns a chandle of the value
  import "DPI-C" function chandle dpii_handle(int v);

  // Sums the values of the chandles
  import "DPI-C" function longint dpii_sum_handles(input chandle h[]);

  // Sums the elements, read through svGetArrayPtr
  import "DPI-C" function int dpii_sum(input int i[]);

  // Inverts each element, xored with its indices
  import "DPI-C" function void dpii_invert2(inout int io[][]);

  // Inverts each element, xored with its index, through svBitVecVal
  import "DPI-C" function void dpii_invert_wide(inout bit [94:0] io[]);

  // Returns the size
  import "DPI-C" function int dpii_size(input string i[]);

  // Sums the elements, read through svGetArrayPtr
  import "DPI-C" function real dpii_sum_real(input real i[]);

  // Doubles each element, through svGetArrayPtr
  import "DPI-C" function void dpii_double(inout real io[]);

  // Checks the assignment that copies back a bounded queue drops elements beyond its bound, with
  // a warning (IEEE 1800-2023 7.10.5). Done from C++, as a copy back has as many elements as the
  // queue had.
  import "DPI-C" function void dpii_assign_bounded();

  initial begin
    bit [63:0] crc;
    crc = 64'h5aef0c8d_d70a4497;

    begin
      byte buffer[];
      longint base;
      base = crc;
      buffer = new[13];
      `checkd(dpii_fill(base, buffer), 13);
      foreach (buffer[i]) `checkh(buffer[i], byte'(base + longint'(i)));
    end

    // Of each size, from the same call
    begin
      int sizes[3];
      sizes = '{0, 1, 7};
      foreach (sizes[s]) begin
        automatic byte d[] = new[sizes[s]];
        automatic byte q[$];
        automatic byte bq[$:6];
        automatic byte expd[];
        automatic byte expq[$];
        automatic byte expbq[$:6];
        foreach (d[i]) begin
          d[i] = crc[7:0];
          q.push_back(crc[15:8]);
          bq.push_back(crc[23:16]);
          crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
        end
        expd = d;
        expq = q;
        expbq = bq;
        `checkd(dpii_invert(d), sizes[s]);
        `checkd(dpii_invert(q), sizes[s]);
        `checkd(dpii_invert(bq), sizes[s]);
        `checkd(d.size(), sizes[s]);
        `checkd(q.size(), sizes[s]);
        `checkd(bq.size(), sizes[s]);
        foreach (d[i]) begin
          `checkh(d[i], ~expd[i] ^ byte'(i));
          `checkh(q[i], ~expq[i] ^ byte'(i));
          `checkh(bq[i], ~expbq[i] ^ byte'(i));
        end
      end
    end

    begin
      bytes_t d;
      bytes_t expd;
      d = new[3];
      foreach (d[i]) begin
        d[i] = crc[7:0];
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      expd = d;
      `checkd(dpii_invert(d), 3);
      foreach (d[i]) `checkh(d[i], ~expd[i] ^ byte'(i));
    end

    begin
      byte d[];
      byte f[2];
      byte expd[];
      byte expf[2];
      d = new[3];
      foreach (d[i]) begin
        d[i] = crc[7:0];
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      f = '{crc[7:0], crc[15:8]};
      expd = d;
      expf = f;
      `checkd(dpii_invert_kw(d), 3);
      `checkd(dpii_invert_kw(f), 2);
      foreach (d[i]) `checkh(d[i], ~expd[i] ^ byte'(i));
      foreach (f[i]) `checkh(f[i], ~expf[i] ^ byte'(i));
    end

    // Several arguments copied back from one call
    begin
      int f[3];
      int d[];
      int q[$];
      f = '{7, 8, 9};
      d = '{1, 2, 3};
      q = '{4, 5, 6};
      dpii_swap(d, q);
      foreach (d[i]) `checkd(d[i], i + 4);
      foreach (q[i]) `checkd(q[i], i + 1);
      dpii_swap(f, d);
      foreach (f[i]) `checkd(f[i], i + 4);
      foreach (d[i]) `checkd(d[i], i + 7);
    end

    begin
      chandle q[$];
      for (int i = 1; i <= 3; ++i) q.push_back(dpii_handle(i));
      `checkd(dpii_sum_handles(q), 6);
    end

    begin
      int f[5];
      int d[];
      int q[$];
      int sumf;
      int sumd;
      int sumq;
      d = new[5];
      sumf = 0;
      sumd = 0;
      sumq = 0;
      foreach (f[i]) begin
        f[i] = crc[31:0];
        d[i] = crc[63:32];
        q.push_back(crc[47:16]);
        sumf += f[i];
        sumd += d[i];
        sumq += q[i];
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      `checkd(dpii_sum(f), sumf);
      `checkd(dpii_sum(d), sumd);
      `checkd(dpii_sum(q), sumq);
    end

    begin
      int d[][2:-1];
      int q[$][-1:1];
      int expd[][2:-1];
      int expq[$][-1:1];
      d = new[3];
      for (int a = 0; a < 2; ++a) begin
        q.push_back('{crc[31:0], crc[47:16], crc[63:32]});
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      foreach (d[a, b]) begin
        d[a][b] = crc[31:0];
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      expd = d;
      expq = q;
      dpii_invert2(d);
      dpii_invert2(q);
      foreach (d[a, b]) `checkh(d[a][b], ~expd[a][b] ^ (a << 8) ^ b);
      foreach (q[a, b]) `checkh(q[a][b], ~expq[a][b] ^ (a << 8) ^ b);
    end

    begin
      bit [94:0] q[$];
      bit [94:0] expq[$];
      for (int i = 0; i < 3; ++i) begin
        q.push_back({crc[30:0], crc});
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      expq = q;
      dpii_invert_wide(q);
      foreach (q[i]) `checkh(q[i], ~expq[i] ^ 95'(i));
    end

    begin
      string d[];
      string q[$];
      d = new[3];
      q.push_back("a");
      q.push_back("b");
      `checkd(dpii_size(d), 3);
      `checkd(dpii_size(q), 2);
    end

    begin
      real d[];
      realtime q[$];  // As real (IEEE 1800-2023 6.12)
      realtime expq[$];
      real sumd;
      d = new[3];
      sumd = 0;
      foreach (d[i]) begin
        d[i] = real'(crc[15:0]) / 8.0;
        q.push_back(-real'(crc[31:16]) / 4.0);
        sumd += d[i];
        crc = {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      end
      expq = q;
      `checkr(dpii_sum_real(d), sumd);
      dpii_double(q);
      `checkd(q.size(), 3);
      foreach (q[i]) `checkr(q[i], expq[i] * 2);
    end

    dpii_assign_bounded();

    `checkd(dpii_failure(), 0);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
