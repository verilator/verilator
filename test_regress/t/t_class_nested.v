// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class NodeList;
    class Node;
        string name;
        Node link;

        function new();
            name = "node";
        endfunction
    endclass

    Node head;
endclass

class NodeTree;
    class Node;
        int id;
        Node link;
    endclass

    Node root;
endclass

// Based on IEEE 1800-2017 section 8.23 Nested classes
class Outer;
    int outerProp;
    local int outerLocalProp;
    static int outerStaticProp;
    static local int outerLocalStaticProp;

    class Inner;
        function void innerMethod(Outer h);
            outerStaticProp = 1;
            outerLocalStaticProp = 1;
            h.outerProp = 1;
            h.outerLocalProp = 1;
        endfunction
    endclass
endclass


module t(/*AUTOARG*/);
    initial begin
        NodeList n = new;
        NodeList::Node n1 = new;
        NodeList::Node n2 = new;
        NodeTree tr = new;
        NodeTree::Node t1 = new;
        NodeTree::Node t2 = new;
        Outer o = new;
        Outer::Inner i = new;

        i.innerMethod(o);

        if(o.outerProp != 1) $stop;
        if(Outer::outerStaticProp != 1) $stop;

        if (n1.name != "node") $stop;

        n1.name = "n1";
        if (n1.name != "n1") $stop;

        n2.name = "n2";
        if (n2.name != "n2") $stop;

        n.head = n1;
        n1.link = n2;
        if (n.head.name != "n1") $stop;
        if (n.head.link.name != "n2") $stop;

        t1.id = 1;
        if (t1.id != 1) $stop;

        t2.id = 2;
        if (t2.id != 2) $stop;

        tr.root = t1;
        t1.link = t2;
        if (tr.root.id != 1) $stop;
        if (tr.root.link.id != 2) $stop;

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
