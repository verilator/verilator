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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
