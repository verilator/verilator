// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc;
  initial cyc = 1;

  Test test (
    /*AUTOINST*/
    // Inputs
    .clk(clk),
    .cyc(cyc)
  );

  always @(posedge clk) begin
    if (cyc != 0) begin
      cyc <= cyc + 1;
`ifdef TEST_VERBOSE
      $display("cyc=%0d", cyc);
`endif
      if (cyc == 10) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end

endmodule

// Interface for data validation with coverage
interface data_valid_if (
    input logic clk
);
  logic enable_invalid_data_checks;
  logic valid;
  logic [7:0] data;

  property dataIsKnownWhenValid;
    @(posedge clk) enable_invalid_data_checks & valid |-> !$isunknown(data);
  endproperty

  assert_dataIsKnownWhenValid: assert property (dataIsKnownWhenValid)
    else $error("Data contains unknown values when valid is asserted");

endinterface

module Test (
    input clk,
    input integer cyc
);

  logic rst_n;

  // Instantiate the interface
  data_valid_if dv_if (clk);

  // Reset logic
  initial begin
    rst_n = 0;
    dv_if.enable_invalid_data_checks = 0;
  end

  always @(posedge clk) begin
    if (cyc == 1) begin
      rst_n <= 1'b1;
    end
  end

  // Stimulus: Enable checks after reset
  always @(posedge clk) begin
    if (cyc == 2) begin
      dv_if.enable_invalid_data_checks <= 1'b1;
    end
  end

  // Simulate data transactions
  always @(posedge clk) begin
    case (cyc)
      3: begin
        dv_if.valid <= 1'b0;
        dv_if.data <= 8'h00;
      end
      4: begin
        dv_if.valid <= 1'b1;
        dv_if.data <= 8'hAA;  // Valid data
      end
      5: begin
        dv_if.valid <= 1'b1;
        dv_if.data <= 8'h55;  // Valid data
      end
      6: begin
        dv_if.valid <= 1'b0;
        dv_if.data <= 8'hxx;  // Unknown OK when valid=0
      end
      7: begin
        dv_if.valid <= 1'b1;
        dv_if.data <= 8'hFF;  // Valid data
      end
      8: begin
        dv_if.valid <= 1'b0;
        dv_if.data <= 8'h00;
      end
      default: begin
        dv_if.valid <= 1'b0;
        dv_if.data <= 8'h00;
      end
    endcase
  end

endmodule
