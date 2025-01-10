// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module Child;
   int ch_value;
endmodule

module Parent;
   for (genvar i = 0; i < 10; i++) begin : gen_child
      Child child();
   end
endmodule

module t;
   Parent parent();

   virtual class ChildAgentBase;
      pure virtual task preload(int value);
      pure virtual function string name();
   endclass

   ChildAgentBase child_agents[10];

   for (genvar i = 0; i < 10; i++) begin : gfor
      class ChildAgent extends ChildAgentBase;
         task automatic preload(int value);
            parent.gen_child[i].child.ch_value = value;
         endtask
         function string name();
            return $sformatf("%m");
         endfunction
      endclass

      ChildAgent agent = new();

      initial child_agents[i] = agent;
   end

   task automatic preload_children;
      for (int i = 0; i < 10; i++) begin
         child_agents[i].preload(i);
      end
   endtask

   string s;

   initial begin
      #1;  // Ensure all class instances are initialized
      preload_children();
      `checkh(parent.gen_child[3].child.ch_value, 3);
      `checkh(parent.gen_child[8].child.ch_value, 8);
`ifdef VERILATOR
      // Some legal examples "t.gfor[4].\ChildAgent::name", "t.gfor[4].ChildAgent.name"
      `checks(child_agents[4].name(), "t.gfor[4].ChildAgent.name");
`endif
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
