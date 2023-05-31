// DESCRIPTION: Verilator: Verilog Test module

module top;
   string scope;
   initial begin
      scope = $sformatf("%m");
      $write("[%0t] In %s\n", $time, scope);
      `ifdef MAIN_TOP_NAME_EMPTY
         if (scope != "top") $stop;
      `else
         if (scope != "ALTOP.top") $stop;
      `endif
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
