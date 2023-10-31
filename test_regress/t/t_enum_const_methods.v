// DESCRIPTION: Verilator: constant enum methods
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2022 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

module t ();

   typedef enum [1:0] {E0, E1, E2} enm_t;

   function automatic enm_t get_first();
      enm_t enm;
      return enm.first;
   endfunction

   localparam enm_t enum_first = get_first();

   function automatic enm_t get_last();
      enm_t enm;
      return enm.last;
   endfunction

   localparam enm_t enum_last = get_last();

   function automatic enm_t get_second();
      enm_t enm;
      enm = enm.first;
      return enm.next;
   endfunction

   localparam enm_t enum_second = get_second();

   function automatic string get_name(enm_t enm);
      return enm.name;
   endfunction

   localparam string e0_name = get_name(E0);

   function automatic enm_t get_2();
      enm_t enm;
      enm = E0;
      return enm.next.next;
   endfunction

   localparam enm_t enum_2 = get_2();

   initial begin
      if (enum_first != E0) $stop;
      if (enum_last != E2) $stop;
      if (enum_second != E1) $stop;
      if (e0_name != "E0") $stop;
      if (enum_2 != E2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
