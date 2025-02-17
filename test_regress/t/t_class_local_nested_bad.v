// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class NodeList;
    class Node;
        static local string name;
    endclass

    string name;
    function new();
        name = Node::name;
    endfunction
endclass

module t(/*AUTOARG*/);
    initial begin
        NodeList n = new;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
