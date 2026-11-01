// DESCRIPTION: Verilator: Assigning unpacked arrays to queues
// (initializers and assignment statements, module and class scope)
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Francesco Urbani
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop()
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  localparam byte unsigned ARR[3] = '{8'h11, 8'h22, 8'h33};
  byte unsigned member[3] = '{8'h44, 8'h55, 8'h66};

  task automatic run();
    begin
      byte unsigned q_init[$] = ARR;  // localparam -> queue initializer
      byte unsigned q_assign[$];
      byte unsigned q_member[$] = member;
      q_assign = ARR;  // assignment statement
      `checkh(q_init.size(), 3)
      `checkh(q_init[0], 8'h11)
      `checkh(q_init[2], 8'h33)
      `checkh(q_assign.size(), 3)
      `checkh(q_assign[1], 8'h22)
      `checkh(q_member.size(), 3)
      `checkh(q_member[2], 8'h66)
    end
  endtask
endclass

module t;
  byte unsigned arr8[3] = '{8'h01, 8'h02, 8'h03};
  logic [95:0] arr96[2] = '{96'h1, {32'hdead, 64'hbeef}};
  string arrs[2] = '{"ab", "cd"};

  initial begin
    Cls c;
    automatic byte unsigned q8_init[$] = arr8;
    byte unsigned q8[$];
    byte unsigned q8_bounded[$:4];
    logic [95:0] q96[$];
    string qs[$];

    `checkh(q8_init.size(), 3)
    `checkh(q8_init[2], 8'h03)

    q8 = arr8;
    `checkh(q8.size(), 3)
    `checkh(q8[0], 8'h01)

    q8_bounded = arr8;
    `checkh(q8_bounded.size(), 3)
    `checkh(q8_bounded[1], 8'h02)

    q96 = arr96;
    `checkh(q96.size(), 2)
    `checkh(q96[1], {32'hdead, 64'hbeef})

    qs = arrs;
    `checkh(qs.size(), 2)
    `checks(qs[1], "cd")

    c = new;
    c.run();

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
