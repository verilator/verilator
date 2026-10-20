// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t;
  // IEEE 1800-2023 7.12.3: reductions return the element or with-expression type.
  localparam int REDUCTION_WIDTHS[15] = '{4, 1, 3, 5, 7, 8, 11, 15, 16, 17, 31, 32, 33, 63, 64};
  for (genvar idx = 0; idx < 15; ++idx) begin : g_reduction
    localparam int W = REDUCTION_WIDTHS[idx];
    typedef bit [W-1:0] elem_t;
    task automatic run;
      elem_t q[$];
      elem_t d[];
      elem_t a[int];
      elem_t u[3:1];
      elem_t v;
      elem_t p;
      elem_t expected_sum;
      elem_t expected_product;
      bit signed [W-1:0] sq[$];
      longint unsigned wide_sum;
      longint unsigned wide_product;

      // The first iteration includes #8827's {15, 15, 1} reproducer at W=4.
      for (int n = 0; n < 16; ++n) begin
        q = '{elem_t'('1) - elem_t'(n), elem_t'('1) - elem_t'(n), elem_t'(1)};
        d = new[3];
        foreach (q[i]) begin
          d[i] = q[i];
          a[i] = q[i];
          u[i+1] = q[i];
        end
        expected_sum = elem_t'(q[0] + q[1] + q[2]);
        expected_product = elem_t'(q[0] * q[1] * q[2]);
        v = q.sum();
        p = q.product();
        `checkh(v, expected_sum);
        `checkh(p, expected_product);
        `checkh(q.sum(), expected_sum);
        `checkh(q.product(), expected_product);
        `checkh($bits(q.sum()), W);
        `checkh($bits(q.product()), W);
        `checkh($sformatf("%0d", q.sum()) == $sformatf("%0d", expected_sum), 1'b1);
        `checkh($sformatf("%0d", q.product()) == $sformatf("%0d", expected_product), 1'b1);
        `checkh(d.sum(), expected_sum);
        `checkh(d.product(), expected_product);
        `checkh(a.sum(), expected_sum);
        `checkh(a.product(), expected_product);
        `checkh(u.sum(), expected_sum);
        `checkh(u.product(), expected_product);

        // A with clause determines the result width, independently of the element.
        `checkh(q.sum() with (elem_t'(item)), expected_sum);
        `checkh(q.product() with (elem_t'(item)), expected_product);
        `checkh(d.sum() with (elem_t'(item)), expected_sum);
        `checkh(d.product() with (elem_t'(item)), expected_product);
        `checkh(a.sum() with (elem_t'(item)), expected_sum);
        `checkh(a.product() with (elem_t'(item)), expected_product);
        `checkh(u.sum() with (elem_t'(item)), expected_sum);
        `checkh(u.product() with (elem_t'(item)), expected_product);
        wide_sum = 64'(q[0]) + 64'(q[1]) + 64'(q[2]);
        wide_product = 64'(q[0]) * 64'(q[1]) * 64'(q[2]);
        `checkh($bits(q.sum() with (1'(item))), 1);
        `checkh($bits(q.product() with (64'(item))), 64);
        `checkh(q.sum() with (1'(item)), 1'(q[0][0] + q[1][0] + q[2][0]));
        `checkh(q.product() with (1'(item)), 1'(q[0][0] * q[1][0] * q[2][0]));
        `checkh(64'(q.sum() with (64'(item))), wide_sum);
        `checkh(64'(q.product() with (64'(item))), wide_product);
        `checkh($bits(d.sum() with (1'(item))), 1);
        `checkh($bits(d.product() with (64'(item))), 64);
        `checkh(d.sum() with (1'(item)), 1'(q[0][0] + q[1][0] + q[2][0]));
        `checkh(d.product() with (1'(item)), 1'(q[0][0] * q[1][0] * q[2][0]));
        `checkh(64'(d.sum() with (64'(item))), wide_sum);
        `checkh(64'(d.product() with (64'(item))), wide_product);
        `checkh($bits(a.sum() with (1'(item))), 1);
        `checkh($bits(a.product() with (64'(item))), 64);
        `checkh(a.sum() with (1'(item)), 1'(q[0][0] + q[1][0] + q[2][0]));
        `checkh(a.product() with (1'(item)), 1'(q[0][0] * q[1][0] * q[2][0]));
        `checkh(64'(a.sum() with (64'(item))), wide_sum);
        `checkh(64'(a.product() with (64'(item))), wide_product);
        `checkh($bits(u.sum() with (1'(item))), 1);
        `checkh($bits(u.product() with (64'(item))), 64);
        `checkh(u.sum() with (1'(item)), 1'(q[0][0] + q[1][0] + q[2][0]));
        `checkh(u.product() with (1'(item)), 1'(q[0][0] * q[1][0] * q[2][0]));
        `checkh(64'(u.sum() with (64'(item))), wide_sum);
        `checkh(64'(u.product() with (64'(item))), wide_product);
      end
      sq = '{'1, '1, 1};
      `checkh(sq.sum(), W'(-1));
      `checkh(sq.product(), W'(1));
    endtask
  end
  initial begin
    int q[5];
    int qv[$];  // Value returns
    int qi[$];  // Index returns
    int i;
    string v;

    q = '{1, 2, 2, 4, 3};
    `checkp(q, "'{'h1, 'h2, 'h2, 'h4, 'h3}");

    // NOT tested: with ... selectors

    q.sort;
    `checkp(q, "'{'h1, 'h2, 'h2, 'h3, 'h4}");
    q.sort with (item == 2);
    `checkp(q, "'{'h1, 'h3, 'h4, 'h2, 'h2}");
    q.sort(x) with (x == 3);
    `checkp(q, "'{'h1, 'h4, 'h2, 'h2, 'h3}");

    q.rsort;
    `checkp(q, "'{'h4, 'h3, 'h2, 'h2, 'h1}");
    q.rsort with (item == 2);
    `checkp(q, "'{'h2, 'h2, 'h4, 'h3, 'h1}");

    qv = q.unique;
    `checkp(qv, "'{'h2, 'h4, 'h3, 'h1}");
    qi = q.unique_index;
    qi.sort;
    `checkp(qi, "'{'h0, 'h2, 'h3, 'h4}");
    q.reverse;
    `checkp(q, "'{'h1, 'h3, 'h4, 'h2, 'h2}");
    q.shuffle();
    q.sort;
    `checkp(q, "'{'h1, 'h2, 'h2, 'h3, 'h4}");

    // These require an with clause or are illegal
    // TODO add a lint check that with clause is provided
    qv = q.find with (item == 2);
    `checkp(qv, "'{'h2, 'h2}");
    qv = q.find_first with (item == 2);
    `checkp(qv, "'{'h2}");
    qv = q.find_last with (item == 2);
    `checkp(qv, "'{'h2}");

    qv = q.find with (item == 20);
    `checkp(qv, "'{}");
    qv = q.find_first with (item == 20);
    `checkp(qv, "'{}");
    qv = q.find_last with (item == 20);
    `checkp(qv, "'{}");

    qi = q.find_index with (item == 2);
    qi.sort;
    `checkp(qi, "'{'h1, 'h2}");
    qi = q.find_first_index with (item == 2);
    `checkp(qi, "'{'h1}");
    qi = q.find_last_index with (item == 2);
    `checkp(qi, "'{'h2}");

    qi = q.find_index with (item == 20);
    qi.sort;
    `checkp(qi, "'{}");
    qi = q.find_first_index with (item == 20);
    `checkp(qi, "'{}");
    qi = q.find_last_index with (item == 20);
    `checkp(qi, "'{}");

    qv = q.min;
    `checkp(qv, "'{'h1}");
    qv = q.max;
    `checkp(qv, "'{'h4}");

    // Reduction methods

    i = q.sum;
    `checkh(i, 32'hc);
    i = q.product;
    `checkh(i, 32'h30);

    q = '{32'b1100, 32'b1010, 32'b1100, 32'b1010, 32'b1010};
    i = q.and;
    `checkh(i, 32'b1000);
    i = q.or;
    `checkh(i, 32'b1110);
    i = q.xor;
    `checkh(i, 32'ha);

    q = '{1, 2, 2, 4, 3};
    // `checkp(q, "'{1, 2, 2, 4, 3}");

    i = q.sum with (item + 1);
    `checkh(i, 32'h11);
    i = q.product with (item + 1);
    `checkh(i, 32'h168);

    q = '{32'b1100, 32'b1010, 32'b1100, 32'b1010, 32'b1010};
    i = q.and with (item + 1);
    `checkh(i, 32'b1001);
    i = q.or with (item + 1);
    `checkh(i, 32'b1111);
    i = q.xor with (item + 1);
    `checkh(i, 32'hb);

    // map method
    q = '{1, 2, 3, 4, 5};
    qv = q.map() with (item * 2);
    `checkp(qv, "'{'h2, 'h4, 'h6, 'h8, 'ha}");
    qv = q.map(x) with (x + x.index);
    `checkp(qv, "'{'h1, 'h3, 'h5, 'h7, 'h9}");

    // Original reproducer for #8827.
    begin
      bit [3:0] q[$];
      bit [3:0] v;
      bit [3:0] p;
      q = '{4'hF, 4'hF, 4'h1};
      v = q.sum();
      p = q.product();
      `checkh(v, 4'd15);
      `checkh(p, 4'd1);
      `checkh(q.sum() == 4'd15, 1'b1);
      `checkh(q.product() == 4'd1, 1'b1);
      `checkh($bits(q.sum()), 32'd4);
      `checkh($bits(q.product()), 32'd4);
      `checkh($sformatf("sum=%0d v=%0d eq15=%0d bits=%0d", q.sum(), v,
                       q.sum() == 4'd15, $bits(q.sum())) == "sum=15 v=15 eq15=1 bits=4", 1'b1);
      `checkh($sformatf("product=%0d p=%0d", q.product(), p) == "product=1 p=1", 1'b1);
    end

    g_reduction[0].run();
    g_reduction[1].run();
    g_reduction[2].run();
    g_reduction[3].run();
    g_reduction[4].run();
    g_reduction[5].run();
    g_reduction[6].run();
    g_reduction[7].run();
    g_reduction[8].run();
    g_reduction[9].run();
    g_reduction[10].run();
    g_reduction[11].run();
    g_reduction[12].run();
    g_reduction[13].run();
    g_reduction[14].run();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
