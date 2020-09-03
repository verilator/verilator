// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef TEST_VERBOSE
 `define WRITE_VERBOSE(args) $write args
`else
 `define WRITE_VERBOSE(args)
`endif

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   event e1;
   event e2;
   event e3;
   event e4;
`ifndef IVERILOG
   event ev [3:0];
`endif

   int   cyc;

   int last_event;
   always @(e1) begin
      `WRITE_VERBOSE(("[%0t] e1\n", $time));
`ifndef IVERILOG
      if (!e1.triggered) $stop;
`endif
      last_event[1] = 1;
   end

   always @(e2) begin
      `WRITE_VERBOSE(("[%0t] e2\n", $time));
      last_event[2] = 1;
   end

   always @(e3) begin
      `WRITE_VERBOSE(("[%0t] e3\n", $time));
      last_event[3] = 1;
   end

   always @(e4) begin
      `WRITE_VERBOSE(("[%0t] e4\n", $time));
      last_event[4] = 1;
   end

   always @(posedge clk) begin
      `WRITE_VERBOSE(("[%0t] cyc=%0d last_event=%5b\n", $time, cyc, last_event));
      cyc <= cyc + 1;
      if (cyc == 1) begin
         // Check no initial trigger
         if (last_event != 0) $stop;
      end
      //
      else if (cyc == 10) begin
         last_event = 0;
         -> e1;
      end
      else if (cyc == 12) begin
         if (last_event != 32'b10) $stop;
         last_event = 0;
      end
      else if (cyc == 13) begin
         // Check not still triggering
         if (last_event != 0) $stop;
         last_event = 0;
      end
      //
      else if (cyc == 20) begin
         last_event = 0;
`ifdef IVERILOG
         -> e2;
`else
         // Events are both references and events themselves.  I.e. 'event e'
         // declaration means 'event e = new'.  Then e is a reference to that
         // created event.
         //
         // Always having indirection is bad for performance, so Verilator
         // should have 'event e' as an "EVENTVALUE" stored as a char, or
         // ideally a one bit field reference (not vector as that can't be
         // V3Ordered).
         //
         // Then events once copied become EVENTREFs, much like a ClassRef which
         // points to an EVENTVALUE.  Thus a Verilog "event" starts as an
         // EVENTVALUE, and if an assignment is made it becomes an EVENTVALUE
         // and an EVENTREF initing to that EVENTVALUE.
         //
         // All static scheduling for events would go out the window once an
         // event can be pointed to by an EVENTREF, as basically any EVENTREF
         // activation could be activating any event.  A graph algorithm could
         // determine what events/eventrefs are associated and only
         // pessamistically schedule those events (users of EVENTVALUES) that
         // are ever pointed to by an EVENTREF.
         e4 = e3;  // Old handle to e4
         e3 = e2;  // Same event, also triggers e2
         // IEEE 2017 15.5.5.1 says that this causes a merge, and the below
         // should also activate the "old e3".  However we could not find any
         // simulator that actually does this.  Instead the "old e3" becomes
         // unreachable (via old handle), but is reachable by "e4" as assigned
         // earlier.
         ->> e3;  // Delayed
`endif
      end
      else if (cyc == 22) begin
         if (last_event != 32'b100) $stop;
         last_event = 0;
         -> e2;  // IEEE says triggers e3, but does not
      end
      else if (cyc == 24) begin
         if (last_event != 32'b100) $stop;
         last_event = 0;
         -> e4;  // Triggers old e3
      end
      else if (cyc == 26) begin
         if (last_event != 32'b1000) $stop;
         last_event = 0;
      end
      //
      else if (cyc == 30) begin
         last_event = 0;
`ifndef IVERILOG
         e3 = null;
         -> e3;  // Triggers nothing
`endif
      end
      else if (cyc == 32) begin
         if (last_event != 0) $stop;
         last_event = 0;
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
