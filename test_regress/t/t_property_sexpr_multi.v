// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"
`define TRIGGER(e) ->e; $display("[cyc=%0d, val=%0d] triggered %s", cyc, val, `STRINGIFY(e))

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%p exp='h%p\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  bit [1:0] val = 0;
  event e1;
  event e2;
  event e3;
  event e4;
  event e5;
  event e6;
  event e7;
  event e8;
  event e9;
  event e10;
  event e11;
  event e12;
  integer cyc = 1;

  typedef struct {
    bit fails;
    bit passs;
  } result_t;

  result_t results [int];
  result_t expected [int];

  localparam MAX = 66;
  always @(posedge clk) begin
    ++val;
    ++cyc;

    if (cyc == MAX + 1) begin
      expected[6] = '{1, 0};
      expected[7] = '{1, 0};
      expected[8] = '{1, 1};

      expected[11] = '{1, 0};
      expected[12] = '{1, 0};
      expected[13] = '{1, 0};
      expected[15] = '{1, 0};
      expected[16] = '{1, 1};
      expected[17] = '{1, 0};

      expected[20] = '{1, 0};
      expected[21] = '{1, 0};
      expected[23] = '{1, 0};
      expected[24] = '{1, 0};
      expected[25] = '{1, 0};
      expected[27] = '{1, 1};

      expected[29] = '{1, 0};
      expected[30] = '{1, 0};

      expected[32] = '{1, 0};
      expected[33] = '{1, 0};

      expected[35] = '{1, 0};
      expected[36] = '{1, 0};

      expected[39] = '{1, 1};
      expected[40] = '{0, 1};
      expected[41] = '{0, 1};

      expected[43] = '{1, 0};
      expected[44] = '{1, 0};
      expected[45] = '{1, 0};

      expected[48] = '{0, 1};
      expected[49] = '{0, 1};
      expected[51] = '{1, 1};

      expected[52] = '{0, 1};
      expected[54] = '{0, 1};
      expected[55] = '{1, 1};
      expected[56] = '{0, 1};

      expected[58] = '{1, 0};
      expected[59] = '{1, 1};
      expected[60] = '{1, 0};

      expected[62] = '{0, 1};
      expected[63] = '{0, 1};
      expected[64] = '{0, 1};
      expected[66] = '{0, 1};
      `checkh(results, expected);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always @(negedge clk) begin
    if (cyc >= 5 && cyc <= 9) begin
      `TRIGGER(e1);
    end
    if (cyc >= 10 && cyc <= 18) begin
      `TRIGGER(e2);
    end
    if (cyc >= 19 && cyc <= 27) begin
      `TRIGGER(e3);
    end
    if (cyc >= 28 && cyc <= 30) begin
      `TRIGGER(e4);
    end
    if (cyc >= 31 && cyc <= 33) begin
      `TRIGGER(e5);
    end
    if (cyc >= 34 && cyc <= 36) begin
      `TRIGGER(e6);
    end
    if (cyc >= 37 && cyc <= 41) begin
      `TRIGGER(e7);
    end
    if (cyc >= 42 && cyc <= 46) begin
      `TRIGGER(e8);
    end
    if (cyc >= 47 && cyc <= 51) begin
      `TRIGGER(e9);
    end
    if (cyc >= 52 && cyc <= 56) begin
      `TRIGGER(e10);
    end
    if (cyc >= 57 && cyc <= 61) begin
      `TRIGGER(e11);
    end
    if (cyc >= 62 && cyc <= MAX) begin
      `TRIGGER(e12);
    end
  end

  assert property (@(e1) ##1 1 ##1 1);

  assert property (@(e1) val == 0 ##1 val == 1 ##1 val == 2 ##1 val == 3)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e2) ##1 val == 1 ##2 val == 3)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e3) ##1 val == 1 ##2 val == 3 ##(1+2) val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  // Test failure at each step
  assert property (@(e4) cyc == 28 ##1 cyc == 0 ##1 cyc == 30)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e5) cyc == 31 ##1 cyc == 32 ##1 cyc == 0)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e6) ##1 cyc == 34 ##1 cyc == 0)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e7) not ##1 val == 1 ##1 val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e8) not not ##1 val == 1 ##1 val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e9) not not not ##1 val == 1 ##1 val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e10) not val == 0 ##1 val == 1 ##1 val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e11) not not val == 0 ##1 val == 1 ##1 val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  assert property (@(e12) not not not val == 0 ##1 val == 1 ##1 val == 2)
    results[cyc].passs = 1;
  else
    results[cyc].fails = 1;

  empty_body_tests empty_body_tests(.clk(clk));
endmodule

module empty_body_tests(input clk);
  event e;
  int cyc = 0;
  bit[7:0] hit = 0;
  always @(posedge clk) begin
    ++cyc;
    if (cyc < 5) ->e;
    else `checkd(hit, 'b1111111);
  end

  assert property (@(e) ##1 1 ##1 1);
  assert property (@(e) 1 ##1 1 ##1 1);
  assert property (@(e) 1 ##1 1);

  assert property (@(e) ##1 1 ##1 1) begin
    hit |= 'b1;
  end
  assert property (@(e) 1 ##1 1 ##1 1) begin
    hit |= 'b10;
  end
  assert property (@(e) 1 ##1 1) begin
    hit |= 'b100;
  end

  assert property (@(e) ##1 1 ##1 0) else begin
    hit |= 'b1000;
  end
  assert property (@(e) ##1 0) else begin
    hit |= 'b10000;
  end
  assert property (@(e) 1 ##1 1 ##1 0) else begin
    hit |= 'b100000;
  end
  assert property (@(e) 1 ##1 0) else begin
    hit |= 'b1000000;
  end
endmodule
