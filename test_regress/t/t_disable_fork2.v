// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

// USING THIS FOR DEBUGGING PROCESS PROPAGATION:
//
// The example contains most cases that were problematic during the
// works on support of 'disable fork' statement, including:
//
// - indirect use of disable fork (through a task),
// - indirect use of forks that are to be disabled,
// - forks in forks,
// - a function taking VlProcess argument shared between a process that
//   allocates VlProcess, and one that doesnt,
// - a function that has a delay and obtains VlProcess argument,
// - a function that has a delay and doesn't obtain it.
//
// Blocks below contain info on whether they should (YES) or shouldn't (NO)
// be emitted as functions with a VlProcess argument.
//
// To check if that corresponds to reality, see blue nodes in proc_deps.dot

class Cls;
   task print; /*NO*/
      $write("*-* All ");
   endtask
   task disable_fork_func; /*YES*/
      disable fork;
   endtask
   task common_func; /*YES*/
      fork /*YES*/ #1; join_none
   endtask
   task fork_func; /*YES*/
      fork /*YES*/ #1 $stop; join_none
   endtask
   task delay_func; /*NO*/
      fork /*NO*/ #1 $write("Finished *-*\n"); join_none
   endtask
endclass

module t;
   Cls cls = new;

   initial begin /*YES*/
      fork /*YES*/ cls.common_func(); join_none
      cls.fork_func();
      cls.disable_fork_func();
      cls.print();
   end

   initial begin /*NO*/
      cls.delay_func();
      cls.common_func();
      fork /*YES*/ disable fork; join_none
   end
endmodule
