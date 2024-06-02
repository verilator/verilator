// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  function do_stuff();
    static int some_int;
    begin: block0
      static int some_int;
    end
    begin: block1
      static int some_int;
    end
    begin
      static int some_int;
    end
    begin: block2
      begin: block3
        static int some_int;
      end
      begin
        static int some_int;
      end
    end
  endfunction

  initial begin
    $write("*-* All Finished *-*\n");
    $finish();
  end

endmodule
