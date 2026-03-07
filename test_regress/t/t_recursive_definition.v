// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
    class uvm_built_in_comp #(
        type T = int
    );
    endclass

    class uvm_in_order_comparator #(
        type T = int,
        type comp_type = uvm_built_in_comp#(T)
    );
    endclass

    class uvm_in_order_built_in_comparator #(
        type T = int
    ) extends uvm_in_order_comparator #(T);
    endclass

    initial begin
        uvm_in_order_built_in_comparator #(int) sb;
        $finish;
  end
endmodule
