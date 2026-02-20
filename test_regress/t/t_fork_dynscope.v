// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Foo;
  task do_something(int arg_v);
    int dynscope_var;
    int x;
    if (dynscope_var != 0) $stop;
    dynscope_var = 10;
    if (dynscope_var != 10) $stop;

    fork
      #10 begin
        x = 0;
        // Test capturing a variable that needs to be modified
        if (dynscope_var != 10) $stop;
        $display("Incremented dynscope_var: %0d", ++dynscope_var);
        if (dynscope_var != 11) $stop;

        // Check nested access
        fork
          #10 begin
            $display("Incremented x: %0d", ++x);
            $display("Incremented dynscope_var: %0d", ++dynscope_var);
            if (dynscope_var != 12) $stop;
          end
        join_none
      end
      #10 begin
        // Same as the first check, but with an argument
        // (so it needs to be copied to the dynamic scope instead of being moved there)
        if (arg_v != 1) $stop;
        $display("Incremented arg_v: %0d", ++arg_v);
        if (arg_v != 2) $stop;
      end
    join_none

    // Check if regular access to arg_v has been substituted with access to its copy from
    // a dynamic scope
    $display("Incremented arg_v: %0d", ++arg_v);
    if (arg_v != 1) $stop;
  endtask
endclass

module t;
  initial begin
    Foo foo;
    foo = new;
    foo.do_something(0);

    #99 begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
