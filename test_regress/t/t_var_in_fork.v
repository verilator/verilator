// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

int static_var;

module t();
  event evt;
  task send_event();
    ->evt;
  endtask


  class Foo;
    function void do_something(int captured_var);
      fork
        begin
          int my_var;
          int my_other_var;
          my_var = captured_var;
          my_other_var = captured_var; /* Capture the same value "twice" */
          my_var++;
          static_var++; /* Write to a value with static lifetime (valid) */
          $display("Vars in forked process: %d %d", my_var, my_other_var);
          if (my_var != 2)
            $stop;
          if (my_other_var != 1)
            $stop;
          send_event();
        end
      join_none
      $display("Leaving fork's parent");
    endfunction
  endclass

  initial begin
    Foo foo;
    foo = new;
    static_var = 0;
    foo.do_something(1);

  end

  always @(evt) begin
    $display("Static variable: %d", static_var);
    if (static_var != 1)
      $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
