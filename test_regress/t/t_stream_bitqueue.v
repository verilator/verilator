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
  string s;

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

    begin
      byte_q_t bytq_init;
      byte_q_t bytq;
      bit_q_t  bitq;

      bytq_init.push_back(8'h84);
      bytq_init.push_back(8'haa);
      `checkh(bytq_init[0], 8'h84);
      `checkh(bytq_init[1], 8'haa);
      s = $sformatf("bytq_init=%p", bytq_init);
      `checks(s, "bytq_init='{'h84, 'haa} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s,
              "bitq='{'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1} ");
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa} ");

      /*
        Generalized block-reversal semantics for the outer left-stream when blockSize > 1.
        This seemingly complicated approach is what is required to match commercial simulators,
        otherwise the straggler bit [1] in the padded byte might end up as 0x01 instead of 0x80.

        Starting with result of inner {<<{bitq}}: [1,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0] (17 bits),
        apply outer {<<8{...}} using generalized block-reversal like this:
          - Reverse all bits: [0,0,1,0,0,0,0,1,0,1,0,1,0,1,0,1,1]
          - Split into 8-bit blocks from left and pad incomplete blocks on the left:
              - Block 0: [0,0,1,0,0,0,0,1] (complete)
              - Block 1: [0,1,0,1,0,1,0,1] (complete)
              - Block 2: [1] -> pad on left -> [0,0,0,0,0,0,0,1]
          - Reverse bits within each 8-bit block:
              - Block 0: [0,0,1,0,0,0,0,1] -> [1,0,0,0,0,1,0,0] = 0x84
              - Block 1: [0,1,0,1,0,1,0,1] -> [1,0,1,0,1,0,1,0] = 0xaa
              - Block 2: [0,0,0,0,0,0,0,1] -> [1,0,0,0,0,0,0,0] = 0x80
      */

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s,
              "bitq='{'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h1} ");
      `checkh(bytq[0], 8'h84);
      `checkh(bytq[1], 8'haa);
      `checkh(bytq[2], 8'h80);
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'h80} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s,
              "bitq='{'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h1, 'h1} ");
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'hc0} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'he0} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'h70} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'hb8} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'h5c} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b0);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'h2e} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'h97} ");

      bytq = bytq_init;
      bitq = {<<8{bit_q_t'({<<{bytq}})}};
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bitq.push_back(1'b0);
      bitq.push_back(1'b0);
      bitq.push_back(1'b1);
      bitq.push_back(1'b1);
      bytq = {<<8{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h84, 'haa, 'h97, 'h80} ");
    end

    // Test StreamR (>>) operations - fairly simple since this should maintain left-to-right order.
    begin
      bit_q_t  bitq;
      byte_q_t bytq;

      bitq = {1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0};
      bitq = {>>4{bit_q_t'({<<{bitq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s, "bitq='{'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1} ");

      bytq = {8'h84, 8'haa};
      bitq = {>>{bit_q_t'({<<{bytq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s,
              "bitq='{'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h0, 'h1, 'h0, 'h0, 'h0, 'h0, 'h1} ");

      bitq = {
        1'b1,
        1'b0,
        1'b1,
        1'b0,
        1'b1,
        1'b0,
        1'b1,
        1'b0,
        1'b1,
        1'b1,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
        1'b1,
        1'b0
      };
      bytq = {>>2{byte_q_t'({<<{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h43, 'h55} ");

      bytq = {8'h12, 8'h34, 8'h56};
      bytq = {>>{byte_q_t'({<<{bytq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h6a, 'h2c, 'h48} ");

      bitq = {1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0, 1'b1, 1'b0};
      bitq = {>>6{bit_q_t'({>>{bitq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s, "bitq='{'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0} ");

      bytq = {8'h84, 8'haa};
      bitq = {>>{bit_q_t'({>>{bytq}})}};
      s = $sformatf("bitq=%p", bitq);
      `checks(s,
              "bitq='{'h1, 'h0, 'h0, 'h0, 'h0, 'h1, 'h0, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0, 'h1, 'h0} ");

      bitq = {
        1'b1,
        1'b0,
        1'b1,
        1'b0,
        1'b1,
        1'b0,
        1'b1,
        1'b0,
        1'b1,
        1'b1,
        1'b0,
        1'b0,
        1'b0,
        1'b0,
        1'b1,
        1'b0
      };
      bytq = {>>8{byte_q_t'({>>{bitq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'haa, 'hc2} ");

      bytq = {8'h12, 8'h34, 8'h56};
      bytq = {>>{byte_q_t'({>>{bytq}})}};
      s = $sformatf("bytq=%p", bytq);
      `checks(s, "bytq='{'h12, 'h34, 'h56} ");
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
