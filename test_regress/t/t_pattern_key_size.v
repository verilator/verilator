// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A keyed assignment pattern of a dynamic array or queue is sized by its largest index key

module t;

  typedef enum {
    A = 0,
    B = 1,
    C = 2
  } e_t;
  typedef int T_D[];
  typedef int T_Q[$];
  typedef struct {
    int a;
    byte b;
  } s_t;

  class Cls;
    int v;
    function new(int v);
      this.v = v;
    endfunction
  endclass

  // Declarations, with enum keys in any order
  int de[] = '{C: 30, A: 10, B: 20};
  int qe[$] = '{B: 20, A: 10};
  s_t ds[] = '{B: '{2, 8'h22}, A: '{1, 8'h11}};
  // Gaps covered by the default
  int dd[] = '{0: 5, 3: 7, default: 1};
  int qd[$] = '{3: 7, default: 2};

  function automatic int sum(T_Q q);
    sum = 0;
    foreach (q[i]) sum += q[i];
  endfunction

  initial begin
    `checkp(de, "'{'ha, 'h14, 'h1e}");
    `checkp(qe, "'{'ha, 'h14}");
    `checkp(ds, "'{'{a:'h1, b:'h11}, '{a:'h2, b:'h22}}");
    `checkp(dd, "'{'h5, 'h1, 'h1, 'h7}");
    `checkp(qd, "'{'h2, 'h2, 'h2, 'h7}");

    begin  // Procedural assignments and typed pattern expressions
      T_D d;
      T_Q q;
      d = '{2: 3, default: 4};
      `checkp(d, "'{'h4, 'h4, 'h3}");
      q = T_Q'{1: 5, 0: 6};
      `checkp(q, "'{'h6, 'h5}");
    end

    begin  // Spliced into an unpacked array concatenation
      T_D d;
      T_Q q;
      q = {T_Q'{1: 5, default: 0}, 7};
      `checkp(q, "'{'h0, 'h5, 'h7}");
      q = {T_D'{1: 4, default: 3}, 2};
      `checkp(q, "'{'h3, 'h4, 'h2}");
      d = {T_D'{1: 5, default: 0}, T_D'{0: 9}};
      `checkp(d, "'{'h0, 'h5, 'h9}");
    end

    begin  // As the initializer of new[], a queue pattern is sized, then padded
      T_D d;
      d = new[4] (T_Q'{0: 33});
      `checkp(d, "'{'h21, 'h0, 'h0, 'h0}");
    end

    // As a subroutine argument
    `checkd(sum('{2: 3, default: 1}), 5);

    begin  // Nested
      T_D qd2[$];
      qd2 = '{1: '{0: 7}, 0: '{8, 9}};
      `checkp(qd2, "'{'{'h8, 'h9}, '{'h7}}");
    end

    begin  // Values and default that are not constant, with bits above the element to clean
      logic [6:0] v;
      logic [6:0] q7[$];
      v = 7'($urandom_range(7'h55, 7'h55));
      q7 = '{2: ~v, default: v + 7'h70};
      `checkd(q7.size(), 3);
      `checkh(q7[0], 7'h45);
      `checkh(q7[1], 7'h45);
      `checkh(q7[2], 7'h2a);
    end

    begin  // Element types: wide, real, string, class handle
      bit [94:0] qw[$];
      real qr[$];
      string qs[$];
      Cls qc[$];
      automatic Cls obj = new(7);
      qw = '{1: 95'h1, default: '1};
      `checkd(qw.size(), 2);
      `checkh(qw[0], {95{1'b1}});
      `checkh(qw[1], 95'h1);
      qr = '{2: 1.5, default: 0.25};
      `checkd(qr.size(), 3);
      `checkr(qr[0], 0.25);
      `checkr(qr[2], 1.5);
      qs = '{1: "b", 0: "a"};
      `checkp(qs, "'{\"a\", \"b\"}");
      qc = '{1: obj, default: null};
      `checkd(qc.size(), 2);
      `checkd(qc[0] == null, 1);
      `checkd(qc[1].v, 7);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
