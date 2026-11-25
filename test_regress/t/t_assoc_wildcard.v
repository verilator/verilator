// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  integer i;

  localparam string KEY_S = "PPP";
  localparam bit [23:0] KEY_I = 24'h515151;  // "QQQ"
  typedef enum bit [23:0] {
    KEY_E = 24'h525252  // "RRR"
  } key_e;

  task automatic set_out(output int o[*]);
    o["out"] = 7;
  endtask

  task automatic set_out_wide(output bit [94:0] o[*]);
    o["out"] = {32'h7, 63'h1};
  endtask

  function automatic int bump(ref int n);
    ++n;
    return 0;
  endfunction

  // Element writes and reads keep their effects, once
  initial begin
    begin
      typedef int arr_t[4];
      arr_t ws[*];
      ws["x"][0] = 0;
      ws["x"][1:1] = '{6};
      `checkh(ws["x"][1], 6);
    end
    begin
      logic [127:0] wa[*];
      wa[wa.num()][80:20] = 61'h1;
      `checkh(wa.num(), 1);
    end
    begin
      int wi[*];
      if (wi.num() == 0) wi[1] = 1;
      else wi[1] = 2;
      `checkh(wi[1], 1);
    end
    begin
      int wi[*];
      int n;
      int x;
      wi[0] = 5;
      n = 0;
      x = wi[bump(n)] * 0;
      `checkh(n, 1);
    end
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;
    begin
      // Wildcard
      typedef string dict_t [*];
      static string a [*] = '{default: "nope", "BBBBB": "fooing", 23'h434343: "baring"};
      static dict_t b = '{default: "nope", "BBBBB": "fooing", 23'h434343: "baring"};
      int k;
      string v;

      v = b["CCC"];
      `checks(v, "baring");
      v = b["BBBBB"];
      `checks(v, "fooing");

      v = a["CCC"];
      `checks(v, "baring");
      v = a["BBBBB"];
      `checks(v, "fooing");

      a[32'd1234] = "fooed";
      a[4'd3] = "bared";
      a[79'h4141] = "bazed";
      i = a.num();
      `checkh(i, 5);
      i = a.size();
      `checkh(i, 5);
      v = a[39'd1234];
      `checks(v, "fooed");
      v = a["AA"];
      `checks(v, "bazed");
      v = a[4'd3];
      `checks(v, "bared");
      i = a.exists("baz");
      `checkh(i, 0);
      i = a.exists(4'd3);
      `checkh(i, 1);
      a.delete(4'd3);
      i = a.size();
      `checkh(i, 4);
    end
    begin
      // Wildcard with parameter and enum keys
      static string p [*] = '{default: "nope", KEY_S: "sparam", KEY_I: "iparam", KEY_E: "enum"};
      string v;

      v = p["PPP"];
      `checks(v, "sparam");
      v = p["QQQ"];
      `checks(v, "iparam");
      v = p["RRR"];
      `checks(v, "enum");
      v = p["KEY_S"];  // Keyed by the value, not the name
      `checks(v, "nope");

      // Without a default, and empty
      p = '{"x": "xed"};
      v = p["x"];
      `checks(v, "xed");
      i = p.size();
      `checkh(i, 1);
      p = '{};
      i = p.size();
      `checkh(i, 0);
    end
    begin
      int wa [*];
      int wb [*];
      int na [*] [3];
      int nb [*] [3];

      wb["k"] = 5;
      wa = wb;
      `checkh(wa["k"], 5);
      `checkh(wa.num(), 1);
      nb["k"][2] = 6;
      na = nb;
      `checkh(na["k"][2], 6);
      set_out(wa);
      `checkh(wa["out"], 7);
      `checkh(wa.num(), 1);
    end
    begin
      bit [30:0] w31a [*];
      bit [30:0] w31b [*];
      bit [62:0] w63a [*];
      bit [62:0] w63b [*];
      bit [94:0] w95a [*];
      bit [94:0] w95b [*];

      w31b["k"] = 31'h4000_0001;
      w31a = w31b;
      `checkh(w31a["k"], 31'h4000_0001);
      w63b["k"] = 63'h4000_0000_0000_0001;
      w63a = w63b;
      `checkh(w63a["k"], 63'h4000_0000_0000_0001);
      w95b[96'h8000_0000_0000_0000_0000_0001] = 95'h4000_0000_0000_0000_0000_0001;
      w95a = w95b;
      `checkh(w95a[96'h8000_0000_0000_0000_0000_0001], 95'h4000_0000_0000_0000_0000_0001);
      `checkh(w95a.num(), 1);
      set_out_wide(w95a);
      `checkh(w95a["out"], {32'h7, 63'h1});
      `checkh(w95a.num(), 1);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
