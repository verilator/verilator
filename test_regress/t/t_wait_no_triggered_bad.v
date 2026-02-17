// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  event e_my_event;

  initial begin
    #(1us);
    wait (e_my_event.triggered);  // Ok
    #(1us);
    wait (e_my_event);  // Bad

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
