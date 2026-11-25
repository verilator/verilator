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

    begin
      // Writes to elements of captured dynamically sized arrays
      int aa[int];
      int wa[*];
      int da[];
      int q[$];
      da = new[2];
      q.push_back(0);
      fork
        #10 begin
          aa[3] = 5;
          wa["x"] = 6;
          da[1] = 7;
          q[0] = 8;
          q[1] = 9;
          if (aa[3] != 5) $stop;
          if (wa["x"] != 6) $stop;
          if (da[1] != 7) $stop;
          if (q[0] != 8) $stop;
          if (q.size() != 2) $stop;
          if (q[1] != 9) $stop;
        end
      join_none
    end
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
