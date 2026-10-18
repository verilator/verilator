// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  integer i;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    begin
      // Type
      typedef bit [3:0] nibble_t;
      typedef string dict_t[nibble_t];
      dict_t a;
      string b[nibble_t];
      nibble_t k;
      string v;

      a[4'd3] = "fooed";
      a[4'd2] = "bared";
      i = a.num();
      `checkh(i, 2);
      i = a.size;
      `checkh(i, 2);  // Also checks no parens
      v = a[4'd3];
      `checks(v, "fooed");
      v = a[4'd2];
      `checks(v, "bared");
      i = a.exists(4'd0);
      `checkh(i, 0);
      if (a.exists(4'd0)) $stop;  // Check no width warning
      i = a.exists(4'd2);
      `checkh(i, 1);
      if (!a.exists(4'd2)) $stop;  // Check no width warning
      i = a.first(k);
      `checkh(i, 1);
      `checks(k, 4'd2);
      i = a.next(k);
      `checkh(i, 1);
      `checks(k, 4'd3);
      i = a.next(k);
      `checkh(i, 0);
      i = a.last(k);
      `checkh(i, 1);
      `checks(k, 4'd3);
      i = a.prev(k);
      `checkh(i, 1);
      `checks(k, 4'd2);
      i = a.prev(k);
      `checkh(i, 0);
      `checkp(a, "'{'h2:\"bared\", 'h3:\"fooed\"}");

      a.first(k);
      `checks(k, 4'd2);
      a.next(k);
      `checks(k, 4'd3);
      a.next(k);
      a.last(k);
      `checks(k, 4'd3);
      a.prev(k);
      `checks(k, 4'd2);

      a.delete(4'd2);
      i = a.size();
      `checkh(i, 1);

      b = a;  // Copy assignment
      i = b.size();
      `checkh(i, 1);
    end

    begin
      // Strings
      string a[string];
      string k;
      string v;

      a["foo"] = "fooed";
      a["bar"] = "bared";
      i = a.num();
      `checkh(i, 2);
      i = a.size();
      `checkh(i, 2);
      v = a["foo"];
      `checks(v, "fooed");
      v = a["bar"];
      `checks(v, "bared");
      i = a.exists("baz");
      `checkh(i, 0);
      i = a.exists("bar");
      `checkh(i, 1);
      i = a.first(k);
      `checkh(i, 1);
      `checks(k, "bar");
      i = a.next(k);
      `checkh(i, 1);
      `checks(k, "foo");
      i = a.next(k);
      `checkh(i, 0);
      i = a.last(k);
      `checkh(i, 1);
      `checks(k, "foo");
      i = a.prev(k);
      `checkh(i, 1);
      `checks(k, "bar");
      i = a.prev(k);
      `checkh(i, 0);
      `checkp(a["foo"], "\"fooed\"");
      `checkp(a, "'{\"bar\":\"bared\", \"foo\":\"fooed\"}");

      a.delete("bar");
      i = a.size();
      `checkh(i, 1);
      a.delete();
      i = a.size();
      `checkh(i, 0);
      i = a.first(k);
      `checkh(i, 0);
      i = a.last(k);
      `checkh(i, 0);

      // Patterns & default
      a = '{"f": "fooed", "b": "bared", default: "defaulted"};
      i = a.size();
      `checkh(i, 2);  // Default doesn't count
      v = a["f"];
      `checks(v, "fooed");
      v = a["b"];
      `checks(v, "bared");
      v = a["NEXISTS"];
      `checks(v, "defaulted");

      a = '{"x": "xed"};  // No default
      i = a.size();
      `checkh(i, 1);
      v = a["x"];
      `checks(v, "xed");

      a = '{};
      i = a.size();
      `checkh(i, 0);
    end

    begin
      // Wide-wides - need special array container classes, ick.
      logic [91:2] a[logic [65:1]];
      int b[bit [99:0]];
      a[~65'hfe] = ~90'hfee;
      `checkh(a[~65'hfe], ~90'hfee);
      b[100'b1] = 1;
      `checkh(b[100'b1], 1);
    end

    begin
      int a[string];
      int sum;
      sum = 0;
      a["one"] = 1;
      a["two"] = 2;
      foreach (a[i]) sum += a[i];
      `checkh(sum, 1 + 2);
    end

    begin  // Issue #5435
      int a;
      int ok;
      int dict[int];

      dict[3] = 'h13;
      dict[4] = 'h14;
      dict[5] = 'h15;

      a = 4;
      ok = dict.first(a);
      if (a != 3) $stop;
      if (ok != 1) $stop;
      a = 4;
      ok = dict.next(a);
      if (a != 5) $stop;
      if (ok != 1) $stop;
      a = 4;
      ok = dict.last(a);
      if (a != 5) $stop;
      if (ok != 1) $stop;
    end

    begin  // Non-constant values whose expression is wider than the element
      byte b;
      byte m[int];
      byte w[*];
      b = byte'($urandom_range(16, 16));
      m = '{1: b + 8'h2, default: b + 8'h1};
      `checkh(m[1], 8'h12);
      `checkh(m[5], 8'h11);
      w = '{"a": b + 8'h2, default: b + 8'h1};
      `checkh(w["a"], 8'h12);
      `checkh(w["z"], 8'h11);
    end

    begin  // The default of array elements applies to their elements
      int ua[string][2];
      int uw[*] [2];
      ua = '{"x": '{1, 2}, default: 5};
      `checkh(ua["x"][1], 2);
      `checkh(ua["y"][0], 5);
      `checkh(ua["y"][1], 5);
      uw = '{"x": '{3, 4}, default: 6};
      `checkh(uw["x"][0], 3);
      `checkh(uw["y"][1], 6);
    end

    begin  // An integral key is evaluated as if cast to the key type
      int lm[longint];
      lm = '{1 << 40: 5};
      `checkh(lm[64'h100_0000_0000], 5);
    end

    begin  // Identifier keys are converted to the key type like other keys
      localparam int P = 5;
      localparam int N = 9;
      int a2[bit [1:0]];
      int a4[longint unsigned];
      a2 = '{P: 3};
      `checkh(a2[2'd1], 3);
      a4 = '{N: 7};
      `checkh(a4[64'd9], 7);
    end

    begin  // Struct keys, typed or not
      typedef struct {
        int a;
        int b;
      } s_t;
      int sa[s_t];
      s_t s;
      sa = '{s_t'{1, 2} : 3, '{4, 5} : 6};
      `checkh(sa.size(), 2);
      s = '{1, 2};
      `checkh(sa[s], 3);
      s = '{4, 5};
      `checkh(sa[s], 6);
    end

    begin  // Unpacked array keys
      typedef int a_t[2];
      int aa[a_t];
      a_t k;
      aa = '{a_t'{1, 2} : 7, '{3, 4} : 8};
      `checkh(aa.size(), 2);
      k = '{3, 4};
      `checkh(aa[k], 8);
    end

    begin  // Enum identifier keys of an integral key type
      typedef enum {
        E0,
        E5 = 5
      } e_t;
      int ae[int];
      ae = '{E5: 1, E0: 2};
      `checkh(ae[5], 1);
      `checkh(ae[0], 2);
    end

    begin  // Wide keys, with non-constant values whose expression is wider than the element
      byte b;
      byte wm[bit [127:0]];
      b = byte'($urandom_range(16, 16));
      wm = '{128'h1: b + 8'h1};
      `checkh(wm[128'h1], 8'h11);
    end

    begin  // Values are truncated to the element width
      bit [3:0] c4;
      bit [3:0] m4[int];
      bit [3:0] w4[*];
      c4 = 4'($urandom_range(15, 15));
      m4 = '{0: c4 + 4'd2, default: c4 + 4'd3};
      `checkh(m4[0], 4'h1);
      `checkh(m4[9], 4'h2);
      w4 = '{"a": c4 + 4'd2, default: c4 + 4'd3};
      `checkh(w4["a"], 4'h1);
      `checkh(w4["z"], 4'h2);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
