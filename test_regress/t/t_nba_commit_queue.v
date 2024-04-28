// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);



module t(clk);
  input clk;

  logic [31:0] cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  reg [63:0] crc = 64'h5aef0c8d_d70a4497;
  always @ (posedge clk) crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};

`define at_posedge_clk_on_cycle(n) always @(posedge clk) if (cyc == n)

  // Case 1: narrow packed variable, whole element updates only - 1D
  typedef logic [31:0] elem1_t;
  typedef elem1_t array1_t[128];
  array1_t array1;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 128; ++i) array1[i] = 0;
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], 0);
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], 0);
    for (int i = 0 ; i < 128; ++i) array1[i] <= i;
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], 0);
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], i);
    for (int i = 0 ; i < 128; ++i) array1[i] <= ~i;
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], i);
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], ~i);
    for (int i = 0 ; i < 128; ++i) array1[i] <= -1;
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], ~i);
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array1[i], -1);
  end

  // Case 2: wide packed variable, whole element updates only - 1D
  typedef logic [127:0] elem2_t;
  typedef elem2_t array2_t[128];
  array2_t array2;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 128; ++i) array2[i] = 0;
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], 0);
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], 0);
    for (int i = 0 ; i < 128; ++i) array2[i] <= {4{i}};
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], 0);
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], {4{i}});
    for (int i = 0 ; i < 128; ++i) array2[i] <= {4{~i}};
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], {4{i}});
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], {4{~i}});
    for (int i = 0 ; i < 128; ++i) array2[i] <= '1;
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], {4{~i}});
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array2[i], ~128'b0);
  end


  // Case 3: wide packed variable, whole element updates only - 2D
  typedef logic [127:0] elem3_t;
  typedef elem3_t array3sub_t[512];
  typedef array3sub_t array3_t[128];
  array3_t array3;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) array3[i][j] = 0;
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], 0);
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], 0);
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) array3[i][j] <= {4{i}};
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], 0);
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], {4{i}});
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) array3[i][j] <= {4{~i}};
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], {4{i}});
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], {4{~i}});
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) array3[i][j] <= '1;
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], {4{~i}});
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 512; ++j) `checkh(array3[i][j], ~128'b0);
  end

  // Case 4: real
  typedef real elem4_t;
  typedef elem4_t array4_t[128];
  array4_t array4;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 128; ++i) array4[i] = 1e-5;
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 1e-5);
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 1e-5);
    for (int i = 0 ; i < 128; ++i) array4[i] <= 3.14*real'(i);
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 1e-5);
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 3.14*real'(i));
    for (int i = 0 ; i < 128; ++i) array4[i] <= 2.78*real'(i);
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 3.14*real'(i));
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 2.78*real'(i));
    for (int i = 0 ; i < 128; ++i) array4[i] <= 1e50;
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 2.78*real'(i));
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 128; ++i) `checkr(array4[i], 1e50);
  end

  // Case 5: narrow packed variable, partial element updates - 1D
  typedef logic [31:0] elem5_t;
  typedef elem5_t array5_t[128];
  array5_t array5;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 128; ++i) array5[i] = -1;
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], -1);
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], -1);
    for (int i = 0 ; i < 128; ++i) array5[i][0] <= 1'b0;
    for (int i = 0 ; i < 128; ++i) array5[i][1] <= 1'b0;
    for (int i = 0 ; i < 128; ++i) array5[i][2] <= 1'b0;
    for (int i = 0 ; i < 128; ++i) array5[i][1] <= 1'b1;
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], -1);
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], 32'hffff_fffa);
    for (int i = 0 ; i < 128; ++i) array5[i][18:16] <=  i[3:1];
    for (int i = 0 ; i < 128; ++i) array5[i][19:17] <= ~i[2:0];
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], 32'hffff_fffa);
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], {12'hfff, ~i[2:0], i[1], 16'hfffa});
    for (int i = 0 ; i < 128; ++i) array5[i] <= -1;
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], {12'hfff, ~i[2:0], i[1], 16'hfffa});
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array5[i], -1);
  end

  // Case 6: wide packed variable, partial element updates - 1D
  typedef logic [99:0] elem6_t;
  typedef elem6_t array6_t[128];
  array6_t array6;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 128; ++i) array6[i] = -1;
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], -1);
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], -1);
    for (int i = 0 ; i < 128; ++i) array6[i][80] <= 1'b0;
    for (int i = 0 ; i < 128; ++i) array6[i][81] <= 1'b0;
    for (int i = 0 ; i < 128; ++i) array6[i][82] <= 1'b0;
    for (int i = 0 ; i < 128; ++i) array6[i][81] <= 1'b1;
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], -1);
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], 100'hf_fffa_ffff_ffff_ffff_ffff_ffff);
    for (int i = 0 ; i < 128; ++i) array6[i][86:84] <= ~i[3:1];
    for (int i = 0 ; i < 128; ++i) array6[i][87:85] <=  i[2:0];
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], 100'hf_fffa_ffff_ffff_ffff_ffff_ffff);
  end
  `at_posedge_clk_on_cycle(3) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], {12'hfff, i[2:0], ~i[1], 84'ha_ffff_ffff_ffff_ffff_ffff});
    for (int i = 0 ; i < 128; ++i) array6[i] <= -1;
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], {12'hfff, i[2:0], ~i[1], 84'ha_ffff_ffff_ffff_ffff_ffff});
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 128; ++i) `checkh(array6[i], -1);
  end

  // Case 7: variable partial updates
  typedef logic [99:0] elem7_t;
  typedef elem7_t array7sub_t[256];
  typedef array7sub_t array7_t[128];
  array7_t array7_nba;
  array7_t array7_ref;
  always @(posedge clk) begin
    if (cyc == 0) begin
      for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 256; ++j) array7_nba[i][j] =  100'b0;
      for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 256; ++j) array7_ref[i][j] = ~100'b0;
    end else begin
      for (int i = 0 ; i < 128; ++i) for (int j = 0 ; j < 256; ++j) `checkh(array7_nba[i][j], ~array7_ref[i][j]);
      for (int i = 0 ; i < 128; ++i) begin
        for (int j = 0 ; j < 256; ++j) begin
            array7_nba[i[6:0] ^ crc[30+:7]][j[7:0] ^ crc[10+:8]][7'((crc % 10) * 5) +: 5] <= ~crc[4+:5];
            array7_ref[i[6:0] ^ crc[30+:7]][j[7:0] ^ crc[10+:8]][7'((crc % 10) * 5) +: 5]  =  crc[4+:5];
        end
      end
    end
  end

  // Case 8: Mixed dynamic/non-dynamic
  typedef longint elem8_t;
  typedef elem8_t array8_t[4];
  array8_t array8;
  `at_posedge_clk_on_cycle(0) begin
      array8[0] <= 0;
      array8[1] <= 0;
      array8[2] <= 0;
      array8[3] <= 0;
  end
  `at_posedge_clk_on_cycle(1) begin
      `checkh(array8[0], 0);
      `checkh(array8[1], 0);
      `checkh(array8[2], 0);
      `checkh(array8[3], 0);
      array8[1] <= 42;
      array8[3] <= 63;
      for (int i = 1 ; i < 3 ; ++i) array8[i] <= 2*i + 7;
      array8[1] <= 74;
  end
  `at_posedge_clk_on_cycle(3) begin
      `checkh(array8[0], 0);
      `checkh(array8[1], 74);
      `checkh(array8[2], 11);
      `checkh(array8[3], 63);
  end

  // Case 9: string
  typedef string elem9_t;
  typedef elem9_t array9_t[10];
  array9_t array9;
  `at_posedge_clk_on_cycle(0) begin
    for (int i = 0 ; i < 10; ++i) array9[i] = "squid";
    for (int i = 0 ; i < 10; ++i) `checks(array9[i], "squid");
  end
  `at_posedge_clk_on_cycle(1) begin
    for (int i = 0 ; i < 10; ++i) `checks(array9[i], "squid");
    for (int i = 0 ; i < 10; ++i) array9[i] <= "octopus";
    for (int i = 0 ; i < 10; ++i) `checks(array9[i], "squid");
  end
  `at_posedge_clk_on_cycle(2) begin
    for (int i = 0 ; i < 10; ++i) `checks(array9[i], "octopus");
    for (int i = 1 ; i < 9; ++i) begin
      string tmp;
      $sformat(tmp, "%0d-legged-cephalopod", i);
      array9[i] <= tmp;
    end
    for (int i = 0 ; i < 10; ++i) `checks(array9[i], "octopus");
  end
  `at_posedge_clk_on_cycle(3) begin
    `checks(array9[0], "octopus");
    `checks(array9[1], "1-legged-cephalopod");
    `checks(array9[2], "2-legged-cephalopod");
    `checks(array9[3], "3-legged-cephalopod");
    `checks(array9[4], "4-legged-cephalopod");
    `checks(array9[5], "5-legged-cephalopod");
    `checks(array9[6], "6-legged-cephalopod");
    `checks(array9[7], "7-legged-cephalopod");
    `checks(array9[8], "8-legged-cephalopod");
    `checks(array9[9], "octopus");
    for (int i = 0 ; i < 10; ++i) array9[i] <= "cuttlefish";
    `checks(array9[0], "octopus");
    `checks(array9[1], "1-legged-cephalopod");
    `checks(array9[2], "2-legged-cephalopod");
    `checks(array9[3], "3-legged-cephalopod");
    `checks(array9[4], "4-legged-cephalopod");
    `checks(array9[5], "5-legged-cephalopod");
    `checks(array9[6], "6-legged-cephalopod");
    `checks(array9[7], "7-legged-cephalopod");
    `checks(array9[8], "8-legged-cephalopod");
    `checks(array9[9], "octopus");
  end
  `at_posedge_clk_on_cycle(4) begin
    for (int i = 0 ; i < 10; ++i) `checks(array9[i], "cuttlefish");
  end

endmodule
