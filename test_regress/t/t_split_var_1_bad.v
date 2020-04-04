// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

logic [7:0] should_show_warning_global0 /* verilator split_var */;
logic [7:0] should_show_warning_global1 [1:0] /* verilator split_var */;

interface ifs;
   logic [7:0] should_show_warning_ifs0 /* verilator split_var */;
   logic [7:0] should_show_warning_ifs1 [1:0] /* verilator split_var */;
endinterface

module t();
   // The following variables can not be splitted. will see warnings.
   real should_show_warning0                  /*verilator split_var*/;
   string should_show_warning1                /*verilator split_var*/;
   wire   should_show_warning2                /*verilator split_var*/;

   logic [3:0] addr;
   logic [7:0] rd_data0, rd_data1, rd_data2;

   sub0 i_sub0(.addr(addr), .rd_data(rd_data0));
   sub1 i_sub1(.addr(addr), .rd_data(rd_data2));
   sub2 i_sub2;
   sub3 i_sub3;
   ifs i_ifs();

   function int bad_func(inout logic [3:0] inout_port /*verilator split_var*/,
                         ref logic [7:0] ref_port /*verilator split_var*/);
      return 0;
   endfunction

   initial begin
      addr = 0;
      addr = 1;
      i_sub0.cannot_split1[0] = 0;
      i_sub0.cannot_split1[1] = bad_func(addr, rd_data0);
      $finish;
   end

endmodule


module sub0(input [3:0]addr, output logic [7:0] rd_data);

   logic [7:0] cannot_split0[0:15]  /*verilator split_var*/;
   logic [7:0] cannot_split1[0:15]  /*verilator split_var*/;
   always_comb
      rd_data = cannot_split0[addr];

endmodule


module sub1(input [3:0]addr, output logic [7:0] rd_data);
   genvar cannot_split_genvar /*verilator split_var*/;
   logic [15:0] [7:0] cannot_split  /*verilator split_var*/;
   always_comb
      rd_data = cannot_split[addr];

endmodule


module sub2;  // from t_bitsel_wire_array_bad.v

   // a and b are arrays of length 1.
   wire  a[0:0] /* verilator split_var */ ;  // Array of nets
   wire  b[0:0] /* verilator split_var */ ;

   assign a = 1'b0;  // Only net assignment allowed
   assign b = a[0];  // Only net assignment allowed

endmodule

module sub3;  // from t_select_bad_range3.v

   logic [7:0] inwires [12:10] /* verilator split_var */;
   wire [7:0] outwires [12:10] /* verilator split_var */;

   assign outwires[10] = inwires[11];
   assign outwires[11] = inwires[12];
   assign outwires[12] = inwires[13];  // must be an error here

endmodule
