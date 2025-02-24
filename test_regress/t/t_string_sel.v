// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef struct {
   string str;
} str_s;

class c;
   string str;
   function new();
      str = "foo";
   endfunction
   function string get_str();
      return str;
   endfunction
endclass

module t (/*AUTOARG*/);
   string str = "bar";

   function string get_str();
      return str;
   endfunction

   initial begin
      c o = new;
      str_s st = '{"qux"};
      string sc = {"foo", "bar"};

      // read
      if (str[0] != "b") $stop;
      if (get_str()[1] != "a") $stop;
      if (str[3] != "\0") $stop;
      if (st.str[2] != "x") $stop;
      if (st.str[99] != "\0") $stop;
      if (o.str[0] != "f") $stop;
      if (o.get_str()[1] != "o") $stop;
      if (o.str[-1] != "\0") $stop;
      if (sc[2] != "o") $stop;
      if ($sformatf("foo%s", "bar")[3] != "b") $stop;
      if (sc[-1] != "\0") $stop;
      if (sc[6] != "\0") $stop;
      if (sc[99] != "\0") $stop;

      // write
      sc[5] = "z";
      if (sc != "foobaz") $stop;
      o.str[0] = "b";
      if (o.str != "boo") $stop;
      st.str[2] = "z";
      if (st.str != "quz") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
