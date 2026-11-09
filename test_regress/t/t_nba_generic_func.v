// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int a;
  int c;
  int f;
  int k;
  int x;
  bit [3:0] bits;
  event e;
  string str;
  class Base;
    function void set_a2(int val);
      a <= val;
    endfunction
    function void set_a(int val);
      set_a2(val);
    endfunction
    function void set_x(int val);
      x <= val;
    endfunction
    function int bump(int val);
      f <= f + 1;
      return val;
    endfunction
    function int bump_k(int val);
      k <= k + 1;
      return val;
    endfunction
    virtual function void set_c(int val);
    endfunction
    function void set_bit(int i);
      bits[i] <= 1'b1;
    endfunction
    function void fire();
      ->>e;
    endfunction
    function void set_str(string s);
      if (s == "") return;
      str <= s;
    endfunction
  endclass
  class Derived extends Base;
    virtual function void set_c(int val);
      c <= val;
    endfunction
  endclass
  Base obj;
  initial begin
    Derived derived;
    derived = new;
    obj = derived;
  end

  // NBAs in methods are committed together with the other NBAs of the same NBA region, also
  // through other methods, and through virtual calls. Each is called on a clock of its own, so
  // it is the call that makes the commit run with the NBAs of that clock.
  bit clka;
  int b;
  always @(posedge clka) begin
    obj.set_a(b + 1);
    b <= b + 1;
  end
  initial
    forever begin
      @(a or b);
      `checkd(a, b);
    end
  initial begin
    #1 clka = 1;
    #1 clka = 0;
    #1 clka = 1;
    #1 `checkd(a, 2);
  end

  bit clkc;
  int d;
  always @(posedge clkc) begin
    obj.set_c(d + 1);
    d <= d + 1;
  end
  initial
    forever begin
      @(c or d);
      `checkd(c, d);
    end
  initial begin
    #5 clkc = 1;
    #1 clkc = 0;
    #1 clkc = 1;
    #1 `checkd(c, 2);
  end

  // Also when the call is in the RHS of an NBA, in a 'with' clause
  bit clkf;
  int ones[1] = '{1};
  int g;
  always @(posedge clkf) g <= g + ones.sum() with (obj.bump(item));
  initial
    forever begin
      @(f or g);
      `checkd(f, g);
    end
  initial begin
    #2 clkf = 1;
    #1 clkf = 0;
    #1 clkf = 1;
    #1 `checkd(f, 2);
  end

  // And in its LHS, in a 'with' clause
  bit clkk;
  int kk[2];
  always @(posedge clkk) kk[ones.sum() with (obj.bump_k(item))] <= kk[1] + 1;
  initial
    forever begin
      @(k or kk[1]);
      `checkd(k, kk[1]);
    end
  initial begin
    #6 clkk = 1;
    #1 clkk = 0;
    #1 clkk = 1;
    #1 `checkd(k, 2);
  end

  // And in the order they execute with the NBAs of the process making the call
  // (IEEE 1800-2023 4.6)
  bit clkx;
  always @(posedge clkx) begin
    x <= 5;
    obj.set_x(6);
  end
  initial #9 clkx = 1;
  initial #10 `checkd(x, 6);

  // Each call updates the bits its argument selected (IEEE 1800-2023 10.4.2). The loop is not
  // unrolled, as its bound is not a constant.
  int n;
  initial n = 2;
  initial begin
    #1;
    for (int i = 0; i < n; ++i) obj.set_bit(i);
    #1 `checkh(bits, 4'h3);
  end

  // A nonblocking event trigger in a method fires in the NBA region
  initial begin
    bit fired;
    fork
      begin
        @(e);
        fired = 1;
      end
    join_none
    #1 obj.fire();
    `checkd(e.triggered, 0);
    #1 `checkd(fired, 1);
  end

  // So does one of an array element in a clocked process, selected when it executes
  event ea[2];
  int idx = 1;
  always @(posedge clka) begin
    ->>ea[idx];
    idx = 0;
  end
  initial begin
    bit fired;
    fork
      begin
        @(ea[1]);
        fired = 1;
      end
    join_none
    #2 `checkd(fired, 1);
  end

  // A return in a method can skip an NBA, and the operands it captures
  initial begin
    #1;
    obj.set_str("");
    obj.set_str("a");
    #1 `checks(str, "a");
  end

  initial begin
    #11;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
