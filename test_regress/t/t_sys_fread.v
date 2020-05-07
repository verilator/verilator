// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

//======================================================================

module t;
   integer file;
   integer r_i;
   byte    r_upb[20:10];
   byte    r_dnb[20:10];
   reg [13:0] r_ups[20:10];
   reg [13:0] r_dns[10:20];
   reg [30:0] r_upi[20:10];
   reg [30:0] r_dni[10:20];
   reg [61:0] r_upq[20:10];
   reg [61:0] r_dnq[10:20];
   reg [71:0] r_upw[20:10];
   reg [71:0] r_dnw[10:20];

   task clear;
      // Initialize memories to zero,
      // avoid differences between 2-state and 4-state.
      r_i = ~0;
      foreach (r_upb[i]) r_upb[i] = ~0;
      foreach (r_dnb[i]) r_dnb[i] = ~0;
      foreach (r_ups[i]) r_ups[i] = ~0;
      foreach (r_dns[i]) r_dns[i] = ~0;
      foreach (r_upi[i]) r_upi[i] = ~0;
      foreach (r_dni[i]) r_dni[i] = ~0;
      foreach (r_upq[i]) r_upq[i] = ~0;
      foreach (r_dnq[i]) r_dnq[i] = ~0;
      foreach (r_upw[i]) r_upw[i] = ~0;
      foreach (r_dnw[i]) r_dnw[i] = ~0;

      // Open file
      $fclose(file);
      file = $fopen({`STRINGIFY(`TEST_OBJ_DIR),"/t_sys_fread.mem"}, "r");
      if ($feof(file)) $stop;
   endtask

   task dump;
      $write("Dump:");
      $write("\n  r_i:");   $write(" %x",r_i);
      $write("\n  r_upb:"); foreach (r_upb[i]) $write(" %x", r_upb[i]);
      $write("\n  r_dnb:"); foreach (r_dnb[i]) $write(" %x", r_dnb[i]);
      $write("\n  r_ups:"); foreach (r_ups[i]) $write(" %x", r_ups[i]);
      $write("\n  r_dns:"); foreach (r_dns[i]) $write(" %x", r_dns[i]);
      $write("\n  r_upi:"); foreach (r_upi[i]) $write(" %x", r_upi[i]);
      $write("\n  r_dni:"); foreach (r_dni[i]) $write(" %x", r_dni[i]);
      $write("\n  r_upq:"); foreach (r_upq[i]) $write(" %x", r_upq[i]);
      $write("\n  r_dnq:"); foreach (r_dnq[i]) $write(" %x", r_dnq[i]);
      $write("\n  r_upw:"); foreach (r_upw[i]) $write(" %x", r_upw[i]);
      $write("\n  r_dnw:"); foreach (r_dnw[i]) $write(" %x", r_dnw[i]);
      $write("\n\n");
   endtask

   integer code;

   initial begin
      clear;
      code = $fread(r_i, file);   `checkd(code, 4);
      code = $fread(r_upb, file); `checkd(code, 11);
      code = $fread(r_dnb, file); `checkd(code, 11);
      code = $fread(r_ups, file); `checkd(code, 22);
      code = $fread(r_dns, file); `checkd(code, 22);
      code = $fread(r_upi, file); `checkd(code, 44);
      code = $fread(r_dni, file); `checkd(code, 44);
      code = $fread(r_upq, file); `checkd(code, 88);
      code = $fread(r_dnq, file); `checkd(code, 88);
      code = $fread(r_upw, file); `checkd(code, 99);
      code = $fread(r_dnw, file); `checkd(code, 99);
      dump;

      clear;
      code = $fread(r_upb, file, 15); `checkd(code, 6);
      code = $fread(r_ups, file, 15, 2); `checkd(code, 4);
      dump;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
