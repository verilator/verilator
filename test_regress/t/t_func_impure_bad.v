// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   int sig;

   task foo;
      // verilator no_inline_task
      sig = '1;
   endtask

   task bar;
      sig = '1;
   endtask

   task baz;
     // verilator no_inline_task
     bar();
   endtask

   initial begin
      foo();
      baz();
   end

endmodule
