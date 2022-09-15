// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Methods defined by IEEE:
//  class process;
//     enum state { FINISHED, RUNNING, WAITING, SUSPENDED, KILLED };  // UVM uses KILLED, FINISHED
//     static function process self();
//     function state status();
//     function void kill();
//     task await();  // Warn as unsupported (no UVM library use)
//     function void suspend();  // Warn as unsupported (no UVM library use)
//     function void resume();  // Warn as unsupported (no UVM library use)
//     function void srandom( int seed );  // Operate on all proceses for now?
//     function string get_randstate();  // Operate on all proceses for now?
//     function void set_randstate( string state );  // Operate on all proceses for now?
//   endclass

module t(/*AUTOARG*/);
   process p;

   initial begin
      if (p != null) $stop;
      p = process::self();
      if (p.status() != process::RUNNING) $stop;
      if (p.status() == process::WAITING) $stop;
      if (p.status() == process::SUSPENDED) $stop;
      if (p.status() == process::KILLED) $stop;
      if (p.status() == process::FINISHED) $stop;

      if (0) p.kill();
      if (0) p.await();
      if (0) p.suspend();
      if (0) p.resume();
      // See also t_urandom.pl
      p.srandom(0);
      p.set_randstate(p.get_randstate());

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
