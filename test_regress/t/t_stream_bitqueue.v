// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,
               expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  typedef bit bit_q_t[$];  // CData (1-bit)
  typedef byte byte_q_t[$];  // CData (8-bit)
  typedef logic [7:0] cdata_q_t[$];  // CData (8-bit)
  typedef shortint sdata_q_t[$];  // SData (16-bit)
  typedef logic [15:0] sdata_logic_q_t[$];  // SData (16-bit)
  typedef int idata_q_t[$];  // IData (32-bit)
  typedef logic [31:0] idata_logic_q_t[$];  // IData (32-bit)
  typedef longint qdata_q_t[$];  // QData (64-bit)
  typedef logic [63:0] qdata_logic_q_t[$];  // QData (64-bit)
  typedef logic [127:0] wide_q_t[$];  // VlWide (128-bit)

  input clk;
  integer cyc = 0;
  logic [7:0] d;

  initial begin
    begin
      bit_q_t bit_q, bit_qq;

      bit_q.push_back(1'b0);
      bit_q.push_back(1'b1);
      bit_q.push_back(1'b1);
      `checkh(bit_q[0], 1'b0);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b1);

      bit_q = bit_q_t'(4'he);
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b0);

      bit_q  = bit_q_t'(4'h3);
      bit_qq = bit_q;
      `checkh(bit_qq[0], 1'b0);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b1);

      bit_q  = bit_q_t'(4'h2);
      bit_qq = bit_q_t'(bit_q);
      `checkh(bit_qq[0], 1'b0);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b0);

      bit_q = bit_q_t'({>>{4'hd}});
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b0);
      `checkh(bit_q[3], 1'b1);

      bit_q = bit_q_t'({<<{4'hc}});
      `checkh(bit_q[0], 1'b0);
      `checkh(bit_q[1], 1'b0);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b1);

      bit_q = {>>{bit_q_t'(4'he)}};
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b0);

      bit_q = {<<{bit_q_t'(4'hd)}};
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b0);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b1);

      bit_qq = {>>{bit_q}};
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b1);

      bit_qq = {<<{bit_q}};
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b1);
      `checkh(bit_qq[2], 1'b0);
      `checkh(bit_qq[3], 1'b1);

      bit_q = bit_q_t'({>>{4'hd}});
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b0);
      `checkh(bit_q[3], 1'b1);

      bit_q = bit_q_t'({>>2{4'hd}});
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b0);
      `checkh(bit_q[3], 1'b1);

      bit_qq = bit_q_t'({>>{bit_q}});
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b1);
      `checkh(bit_qq[2], 1'b0);
      `checkh(bit_qq[3], 1'b1);

      bit_qq = bit_q_t'({>>2{bit_q}});
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b1);
      `checkh(bit_qq[2], 1'b0);
      `checkh(bit_qq[3], 1'b1);

      bit_qq = bit_q_t'({<<{bit_q}});
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b1);

      bit_qq = {<<2{bit_qq}};
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b1);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b0);

      bit_qq = {<<2{bit_q_t'({<<{bit_q}})}};
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b1);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b0);
    end

    begin
      cdata_q_t cdata_q, cdata_qq;

      cdata_q = cdata_q_t'(32'hdeadbeef);
      `checkh(cdata_q[0], 8'hde);
      `checkh(cdata_q[1], 8'had);
      `checkh(cdata_q[2], 8'hbe);
      `checkh(cdata_q[3], 8'hef);

      cdata_qq = cdata_q_t'({<<{cdata_q}});
      `checkh(cdata_qq[0], 8'hf7);
      `checkh(cdata_qq[1], 8'h7d);
      `checkh(cdata_qq[2], 8'hb5);
      `checkh(cdata_qq[3], 8'h7b);

      cdata_qq = {<<2{cdata_q}};
      `checkh(cdata_qq[0], 8'hfb);
      `checkh(cdata_qq[1], 8'hbe);
      `checkh(cdata_qq[2], 8'h7a);
      `checkh(cdata_qq[3], 8'hb7);
    end

    begin
      sdata_logic_q_t sdata_q, sdata_qq;

      sdata_q = sdata_logic_q_t'(64'hfeedface_deadbeef);
      `checkh(sdata_q[0], 16'hfeed);
      `checkh(sdata_q[1], 16'hface);
      `checkh(sdata_q[2], 16'hdead);
      `checkh(sdata_q[3], 16'hbeef);

      sdata_qq = sdata_logic_q_t'({<<{sdata_q}});
      `checkh(sdata_qq[0], 16'hf77d);
      `checkh(sdata_qq[1], 16'hb57b);
      `checkh(sdata_qq[2], 16'h735f);
      `checkh(sdata_qq[3], 16'hb77f);

      sdata_qq = {<<2{sdata_q}};
      `checkh(sdata_qq[0], 16'hfbbe);
      `checkh(sdata_qq[1], 16'h7ab7);
      `checkh(sdata_qq[2], 16'hb3af);
      `checkh(sdata_qq[3], 16'h7bbf);
    end

    begin
      idata_logic_q_t idata_q, idata_qq;

      idata_q = idata_logic_q_t'(64'h12345678_9abcdef0);
      `checkh(idata_q[0], 32'h12345678);
      `checkh(idata_q[1], 32'h9abcdef0);

      idata_qq = idata_logic_q_t'({<<{idata_q}});
      `checkh(idata_qq[0], 32'h0f7b3d59);
      `checkh(idata_qq[1], 32'h1e6a2c48);

      idata_q = idata_logic_q_t'(128'hfeedface_deadbeef_cafebabe_12345678);
      `checkh(idata_q[0], 32'hfeedface);
      `checkh(idata_q[1], 32'hdeadbeef);
      `checkh(idata_q[2], 32'hcafebabe);
      `checkh(idata_q[3], 32'h12345678);

      idata_qq = {<<2{idata_logic_q_t'({<<{idata_q}})}};
      `checkh(idata_qq[0], 32'hfddef5cd);
      `checkh(idata_qq[1], 32'hed5e7ddf);
      `checkh(idata_qq[2], 32'hc5fd757d);
      `checkh(idata_qq[3], 32'h2138a9b4);
    end

    begin
      qdata_logic_q_t qdata_q, qdata_qq;

      qdata_q.push_back(64'hdeadbeef_cafebabe);
      qdata_q.push_back(64'hfeedface_12345678);
      `checkh(qdata_q[0], 64'hdeadbeef_cafebabe);
      `checkh(qdata_q[1], 64'hfeedface_12345678);

      qdata_qq = qdata_logic_q_t'({<<{qdata_q}});
      `checkh(qdata_qq[0], 64'h1e6a2c48735fb77f);
      `checkh(qdata_qq[1], 64'h7d5d7f53f77db57b);

      qdata_q.push_back(64'h1111222233334444);
      qdata_q.push_back(64'h5555666677778888);
      qdata_qq = {<<2{qdata_q}};
      `checkh(qdata_qq[0], 64'h2222dddd99995555);
      `checkh(qdata_qq[1], 64'h1111cccc88884444);
      `checkh(qdata_qq[2], 64'h2d951c84b3af7bbf);
      `checkh(qdata_qq[3], 64'hbeaebfa3fbbe7ab7);
    end

    begin
      wide_q_t wide_q, wide_qq;

      wide_q.push_back(128'hdeadbeef_cafebabe_feedface_12345678);
      wide_q.push_back(128'h11112222_33334444_55556666_77778888);
      `checkh(wide_q[0], 128'hdeadbeef_cafebabe_feedface_12345678);
      `checkh(wide_q[1], 128'h11112222_33334444_55556666_77778888);

      wide_qq = wide_q_t'({<<{wide_q}});
      `checkh(wide_qq[0], 128'h1111eeee6666aaaa2222cccc44448888);
      `checkh(wide_qq[1], 128'h1e6a2c48735fb77f7d5d7f53f77db57b);

      wide_q.push_back(128'haaaabbbb_ccccdddd_eeeeffff_00001111);
      wide_q.push_back(128'h22223333_44445555_66667777_88889999);

      wide_qq = wide_q_t'({<<{wide_q}});
      wide_qq = {<<2{wide_q}};
      `checkh(wide_qq[0], 128'h66662222dddd999955551111cccc8888);
      `checkh(wide_qq[1], 128'h44440000ffffbbbb77773333eeeeaaaa);
      `checkh(wide_qq[2], 128'h2222dddd999955551111cccc88884444);
      `checkh(wide_qq[3], 128'h2d951c84b3af7bbfbeaebfa3fbbe7ab7);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
