// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0)
// verilog_format: on

module t;
  // kill() in pre_randomize()/post_randomize(), of other processes and of the caller
  class killer;
    process pre_victim;
    process post_victim;
    function void pre_randomize();
      if (pre_victim != null) pre_victim.kill();
    endfunction
    function void post_randomize();
      if (post_victim != null) post_victim.kill();
    endfunction
  endclass

  killer others = new;
  killer pre_self = new;
  killer post_self = new;
  int others_value = -1;
  int pre_self_value = -1;
  int post_self_value = -1;
  bit self_after;

  initial begin
    fork
      begin
        others.pre_victim = process::self();
        #10;
      end
      begin
        others.post_victim = process::self();
        #10;
      end
      begin
        pre_self.pre_victim = process::self();
        pre_self_value = pre_self.randomize();
        self_after = 1'b1;
      end
      begin
        post_self.post_victim = process::self();
        post_self_value = post_self.randomize();
        self_after = 1'b1;
      end
    join_none
    #1;
    others_value = others.randomize();
    `checkd(others_value, 1);
    `checkd(others.pre_victim.status(), process::KILLED);
    `checkd(others.post_victim.status(), process::KILLED);
    `checkd(pre_self.pre_victim.status(), process::KILLED);
    `checkd(post_self.post_victim.status(), process::KILLED);
    `checkd(pre_self_value, -1);
    `checkd(post_self_value, -1);
    `checkd(self_after, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
