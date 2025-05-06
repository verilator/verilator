// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    logic [7:0] data = 0;
    // Test loop
    always @ (posedge clk) begin
       if (data != 15) begin
          data <= data + 8'd1;
       end else begin
          $write("*-* All Finished *-*\n");
          $finish;
       end
    end


    bug5782 u_bug5782(.data_out());
    bug5984 u_bug5984(.in(data));

endmodule

// #5782 internal error with --trace. Bit range is not properly handled.
module bug5782 (
    output logic [31:0][15:0] data_out
);
    logic [31:0][15:0] data [8] /*verilator split_var*/;
    always begin
        data_out = data[7];
    end
endmodule

// #5984 inconsistent assignment due to wrong bit range calculation.
module bug5984 (
   input logic [1:0][3:0] in
   );

   logic [1:0][5:2] internal;

   for (genvar dim1 = 0; dim1 < 2; dim1++) begin
      for (genvar dim2 = 0; dim2 < 4; dim2++) begin
         assign internal[dim1][dim2+2] = in[dim1][dim2];
      end
   end

   for (genvar dim1 = 0; dim1 < 2; dim1++) begin
      for (genvar dim2 = 0; dim2 < 4; dim2++) begin
         always_ff @(negedge internal[dim1][dim2+2]) begin
            $display("%0b", internal[dim1][dim2+2]);
         end
      end
   end
endmodule
