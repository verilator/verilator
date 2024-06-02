// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Driss Hafdi.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   initial begin
      if (getUnpacked($c("0")) != "0") $stop;
      if (getUnpacked($c("1")) != "1") $stop;
      if (getUnpacked($c("2")) != "2") $stop;
      if (getUnpacked($c("3")) != "3") $stop;
      if (getUnpacked($c("4")) != "4") $stop;
      if (getUnpacked($c("5")) != "5") $stop;
      if (getUnpacked($c("6")) != "6") $stop;
      if (getUnpacked($c("7")) != "7") $stop;
      if (getUnpacked($c("8")) != "8") $stop;
      if (getUnpacked($c("9")) != "9") $stop;

      if (getPacked($c("0")) != "0") $stop;
      if (getPacked($c("1")) != "1") $stop;
      if (getPacked($c("2")) != "2") $stop;
      if (getPacked($c("3")) != "3") $stop;
      if (getPacked($c("4")) != "4") $stop;
      if (getPacked($c("5")) != "5") $stop;
      if (getPacked($c("6")) != "6") $stop;
      if (getPacked($c("7")) != "7") $stop;
      if (getPacked($c("8")) != "8") $stop;
      if (getPacked($c("9")) != "9") $stop;

      if (getString($c("0")) != "0") $stop;
      if (getString($c("1")) != "1") $stop;
      if (getString($c("2")) != "2") $stop;
      if (getString($c("3")) != "3") $stop;
      if (getString($c("4")) != "4") $stop;
      if (getString($c("5")) != "5") $stop;
      if (getString($c("6")) != "6") $stop;
      if (getString($c("7")) != "7") $stop;
      if (getString($c("8")) != "8") $stop;
      if (getString($c("9")) != "9") $stop;

      if (getStruct($c("0")) != "0") $stop;
      if (getStruct($c("1")) != "1") $stop;
      if (getStruct($c("2")) != "2") $stop;
      if (getStruct($c("3")) != "3") $stop;
      if (getStruct($c("4")) != "4") $stop;
      if (getStruct($c("5")) != "5") $stop;
      if (getStruct($c("6")) != "6") $stop;
      if (getStruct($c("7")) != "7") $stop;
      if (getStruct($c("8")) != "8") $stop;
      if (getStruct($c("9")) != "9") $stop;

      if (getType($c("0")) != "0") $stop;
      if (getType($c("1")) != "1") $stop;
      if (getType($c("2")) != "2") $stop;
      if (getType($c("3")) != "3") $stop;
      if (getType($c("4")) != "4") $stop;
      if (getType($c("5")) != "5") $stop;
      if (getType($c("6")) != "6") $stop;
      if (getType($c("7")) != "7") $stop;
      if (getType($c("8")) != "8") $stop;
      if (getType($c("9")) != "9") $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

function automatic logic [7:0] getUnpacked(logic[3:0] d);
`ifdef NO_INLINE
   /* verilator no_inline_task */
`endif
   localparam logic [7:0] digits [10] =
                          '{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"};
   return digits[d];
endfunction

function automatic logic [7:0] getPacked(logic[3:0] d);
`ifdef NO_INLINE
   /* verilator no_inline_task */
`endif
   localparam logic [9:0][7:0] digits =
                         {"9", "8", "7", "6", "5", "4", "3", "2", "1", "0"};
   return digits[d];
endfunction

function automatic string getString(logic[3:0] d);
`ifdef NO_INLINE
   /* verilator no_inline_task */
`endif
   localparam string           digits [10] =
                               '{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"};
   return digits[d];
endfunction

function automatic logic [7:0] getStruct(logic[3:0] d);
`ifdef NO_INLINE
   /* verilator no_inline_task */
`endif
   // Silly indirect lookup table because we want to use a struct
   typedef struct              packed {
      logic [7:0]              result;
      longint                  index;
   } lut_t;
   localparam lut_t digits [10] =
                                 '{
                                   '{result: "1", index: 9},
                                   '{result: "2", index: 0},
                                   '{result: "3", index: 1},
                                   '{result: "4", index: 2},
                                   '{result: "5", index: 3},
                                   '{result: "6", index: 4},
                                   '{result: "7", index: 5},
                                   '{result: "8", index: 6},
                                   '{result: "9", index: 7},
                                   '{result: "0", index: 8}
                                   };
   return digits[4'(digits[d].index)].result;
endfunction

function automatic logic [7:0] getType(logic[3:0] d);
`ifdef NO_INLINE
   /* verilator no_inline_task */
`endif
   localparam type octet_t = logic [7:0];
   localparam octet_t [9:0] digits =
                         {"9", "8", "7", "6", "5", "4", "3", "2", "1", "0"};
   return digits[d];
endfunction
