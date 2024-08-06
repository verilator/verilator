// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Varun Koyyalagunta, Tenstorrent.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

    localparam W = 23;

    localparam [W-1:0] R0 = W'('h200000 + 0);
    localparam [W-1:0] R1 = W'('h200000 + 1);
    localparam [W-1:0] R2 = W'('h200000 + 2);
    localparam [W-1:0] R3 = W'('h200000 + 3);
    localparam [W-1:0] R4 = W'('h200000 + 4);
    localparam [W-1:0] R5 = W'('h200000 + 5);
    localparam [W-1:0] R6 = W'('h200000 + 6);
    localparam [W-1:0] R7 = W'('h200000 + 7);
    localparam [W-1:0] R8 = W'('h200000 + 8);
    localparam [W-1:0] R9 = W'('h200000 + 9);
    localparam [W-1:0] R10 = W'('h200000 + 10);
    localparam [W-1:0] R11 = W'('h200000 + 11);
    localparam [W-1:0] R12 = W'('h200000 + 12);
    localparam [W-1:0] R13 = W'('h200000 + 13);
    localparam [W-1:0] R14 = W'('h200000 + 14);
    localparam [W-1:0] R15 = W'('h200000 + 15);
    localparam [W-1:0] R16 = W'('h200000 + 16);
    localparam [W-1:0] R17 = W'('h200000 + 17);
    localparam [W-1:0] R18 = W'('h200000 + 18);
    localparam [W-1:0] R19 = W'('h200000 + 19);
    localparam [W-1:0] R20 = W'('h200000 + 20);
    localparam [W-1:0] R21 = W'('h200000 + 21);
    localparam [W-1:0] R22 = W'('h200000 + 22);
    localparam [W-1:0] R23 = W'('h200000 + 23);
    localparam [W-1:0] R24 = W'('h200000 + 24);
    localparam [W-1:0] R25 = W'('h200000 + 25);
    localparam [W-1:0] R26 = W'('h200000 + 26);
    localparam [W-1:0] R27 = W'('h200000 + 27);
    localparam [W-1:0] R28 = W'('h200000 + 28);
    localparam [W-1:0] R29 = W'('h200000 + 29);
    localparam [W-1:0] R30 = W'('h200000 + 30);
    localparam [W-1:0] R31 = W'('h200000 + 31);
    localparam [W-1:0] R32 = W'('h200000 + 32);
    localparam [W-1:0] R33 = W'('h200000 + 33);
    localparam [W-1:0] R34 = W'('h200000 + 34);
    localparam [W-1:0] R35 = W'('h200000 + 35);
    localparam [W-1:0] R36 = W'('h200000 + 36);
    localparam [W-1:0] R37 = W'('h200000 + 37);
    localparam [W-1:0] R38 = W'('h200000 + 38);
    localparam [W-1:0] R39 = W'('h200000 + 39);
    localparam [W-1:0] R40 = W'('h200000 + 40);
    localparam [W-1:0] R41 = W'('h200000 + 41);
    localparam [W-1:0] R42 = W'('h200000 + 42);
    localparam [W-1:0] R43 = W'('h200000 + 43);
    localparam [W-1:0] R44 = W'('h200000 + 44);
    localparam [W-1:0] R45 = W'('h200000 + 45);
    localparam [W-1:0] R46 = W'('h200000 + 46);
    localparam [W-1:0] R47 = W'('h200000 + 47);
    localparam [W-1:0] R48 = W'('h200000 + 48);
    localparam [W-1:0] R49 = W'('h200000 + 49);
    localparam [W-1:0] R50 = W'('h200000 + 50);
    localparam [W-1:0] R51 = W'('h200000 + 51);
    localparam [W-1:0] R52 = W'('h200000 + 52);
    localparam [W-1:0] R53 = W'('h200000 + 53);
    localparam [W-1:0] R54 = W'('h200000 + 54);
    localparam [W-1:0] R55 = W'('h200000 + 55);
    localparam [W-1:0] R56 = W'('h200000 + 56);
    localparam [W-1:0] R57 = W'('h200000 + 57);
    localparam [W-1:0] R58 = W'('h200000 + 58);
    localparam [W-1:0] R59 = W'('h200000 + 59);
    localparam [W-1:0] R60 = W'('h200000 + 60);
    localparam [W-1:0] R61 = W'('h200000 + 61);
    localparam [W-1:0] R62 = W'('h200000 + 62);
    localparam [W-1:0] R63 = W'('h200000 + 63);
    localparam [W-1:0] R64 = W'('h200000 + 64);
    localparam [W-1:0] R65 = W'('h200000 + 65);
    localparam [W-1:0] R66 = W'('h200000 + 66);
    localparam [W-1:0] R67 = W'('h200000 + 67);
    localparam [W-1:0] R68 = W'('h200000 + 68);
    localparam [W-1:0] R69 = W'('h200000 + 69);
    localparam [W-1:0] R70 = W'('h200000 + 70);
    localparam [W-1:0] R71 = W'('h200000 + 71);
    localparam [W-1:0] R72 = W'('h200000 + 72);
    localparam [W-1:0] R73 = W'('h200000 + 73);
    localparam [W-1:0] R74 = W'('h200000 + 74);
    localparam [W-1:0] R75 = W'('h200000 + 75);
    localparam [W-1:0] R76 = W'('h200000 + 76);
    localparam [W-1:0] R77 = W'('h200000 + 77);
    localparam [W-1:0] R78 = W'('h200000 + 78);
    localparam [W-1:0] R79 = W'('h200000 + 79);
    localparam [W-1:0] R80 = W'('h200000 + 80);
    localparam [W-1:0] R81 = W'('h200000 + 81);
    localparam [W-1:0] R82 = W'('h200000 + 82);
    localparam [W-1:0] R83 = W'('h200000 + 83);
    localparam [W-1:0] R84 = W'('h200000 + 84);
    localparam [W-1:0] R85 = W'('h200000 + 85);
    localparam [W-1:0] R86 = W'('h200000 + 86);
    localparam [W-1:0] R87 = W'('h200000 + 87);
    localparam [W-1:0] R88 = W'('h200000 + 88);
    localparam [W-1:0] R89 = W'('h200000 + 89);
    localparam [W-1:0] R90 = W'('h200000 + 90);
    localparam [W-1:0] R91 = W'('h200000 + 91);
    localparam [W-1:0] R92 = W'('h200000 + 92);
    localparam [W-1:0] R93 = W'('h200000 + 93);
    localparam [W-1:0] R94 = W'('h200000 + 94);
    localparam [W-1:0] R95 = W'('h200000 + 95);
    localparam [W-1:0] R96 = W'('h200000 + 96);
    localparam [W-1:0] R97 = W'('h200000 + 97);
    localparam [W-1:0] R98 = W'('h200000 + 98);
    localparam [W-1:0] R99 = W'('h200000 + 99);
    typedef struct packed {
        logic  r0;
        logic  r1;
        logic  r2;
        logic  r3;
        logic  r4;
        logic  r5;
        logic  r6;
        logic  r7;
        logic  r8;
        logic  r9;
        logic  r10;
        logic  r11;
        logic  r12;
        logic  r13;
        logic  r14;
        logic  r15;
        logic  r16;
        logic  r17;
        logic  r18;
        logic  r19;
        logic  r20;
        logic  r21;
        logic  r22;
        logic  r23;
        logic  r24;
        logic  r25;
        logic  r26;
        logic  r27;
        logic  r28;
        logic  r29;
        logic  r30;
        logic  r31;
        logic  r32;
        logic  r33;
        logic  r34;
        logic  r35;
        logic  r36;
        logic  r37;
        logic  r38;
        logic  r39;
        logic  r40;
        logic  r41;
        logic  r42;
        logic  r43;
        logic  r44;
        logic  r45;
        logic  r46;
        logic  r47;
        logic  r48;
        logic  r49;
        logic  r50;
        logic  r51;
        logic  r52;
        logic  r53;
        logic  r54;
        logic  r55;
        logic  r56;
        logic  r57;
        logic  r58;
        logic  r59;
        logic  r60;
        logic  r61;
        logic  r62;
        logic  r63;
        logic  r64;
        logic  r65;
        logic  r66;
        logic  r67;
        logic  r68;
        logic  r69;
        logic  r70;
        logic  r71;
        logic  r72;
        logic  r73;
        logic  r74;
        logic  r75;
        logic  r76;
        logic  r77;
        logic  r78;
        logic  r79;
        logic  r80;
        logic  r81;
        logic  r82;
        logic  r83;
        logic  r84;
        logic  r85;
        logic  r86;
        logic  r87;
        logic  r88;
        logic  r89;
        logic  r90;
        logic  r91;
        logic  r92;
        logic  r93;
        logic  r94;
        logic  r95;
        logic  r96;
        logic  r97;
        logic  r98;
        logic  r99;
    } hit_t;
    function automatic hit_t get_hit(input logic [22:0] a);
        hit_t hit = '0;
        unique case (a)
            R0 : begin hit.r0 = 1'b1; end
            R1 : begin hit.r1 = 1'b1; end
            R2 : begin hit.r2 = 1'b1; end
            R3 : begin hit.r3 = 1'b1; end
            R4 : begin hit.r4 = 1'b1; end
            R5 : begin hit.r5 = 1'b1; end
            R6 : begin hit.r6 = 1'b1; end
            R7 : begin hit.r7 = 1'b1; end
            R8 : begin hit.r8 = 1'b1; end
            R9 : begin hit.r9 = 1'b1; end
            R10 : begin hit.r10 = 1'b1; end
            R11 : begin hit.r11 = 1'b1; end
            R12 : begin hit.r12 = 1'b1; end
            R13 : begin hit.r13 = 1'b1; end
            R14 : begin hit.r14 = 1'b1; end
            R15 : begin hit.r15 = 1'b1; end
            R16 : begin hit.r16 = 1'b1; end
            R17 : begin hit.r17 = 1'b1; end
            R18 : begin hit.r18 = 1'b1; end
            R19 : begin hit.r19 = 1'b1; end
            R20 : begin hit.r20 = 1'b1; end
            R21 : begin hit.r21 = 1'b1; end
            R22 : begin hit.r22 = 1'b1; end
            R23 : begin hit.r23 = 1'b1; end
            R24 : begin hit.r24 = 1'b1; end
            R25 : begin hit.r25 = 1'b1; end
            R26 : begin hit.r26 = 1'b1; end
            R27 : begin hit.r27 = 1'b1; end
            R28 : begin hit.r28 = 1'b1; end
            R29 : begin hit.r29 = 1'b1; end
            R30 : begin hit.r30 = 1'b1; end
            R31 : begin hit.r31 = 1'b1; end
            R32 : begin hit.r32 = 1'b1; end
            R33 : begin hit.r33 = 1'b1; end
            R34 : begin hit.r34 = 1'b1; end
            R35 : begin hit.r35 = 1'b1; end
            R36 : begin hit.r36 = 1'b1; end
            R37 : begin hit.r37 = 1'b1; end
            R38 : begin hit.r38 = 1'b1; end
            R39 : begin hit.r39 = 1'b1; end
            R40 : begin hit.r40 = 1'b1; end
            R41 : begin hit.r41 = 1'b1; end
            R42 : begin hit.r42 = 1'b1; end
            R43 : begin hit.r43 = 1'b1; end
            R44 : begin hit.r44 = 1'b1; end
            R45 : begin hit.r45 = 1'b1; end
            R46 : begin hit.r46 = 1'b1; end
            R47 : begin hit.r47 = 1'b1; end
            R48 : begin hit.r48 = 1'b1; end
            R49 : begin hit.r49 = 1'b1; end
            R50 : begin hit.r50 = 1'b1; end
            R51 : begin hit.r51 = 1'b1; end
            R52 : begin hit.r52 = 1'b1; end
            R53 : begin hit.r53 = 1'b1; end
            R54 : begin hit.r54 = 1'b1; end
            R55 : begin hit.r55 = 1'b1; end
            R56 : begin hit.r56 = 1'b1; end
            R57 : begin hit.r57 = 1'b1; end
            R58 : begin hit.r58 = 1'b1; end
            R59 : begin hit.r59 = 1'b1; end
            R60 : begin hit.r60 = 1'b1; end
            R61 : begin hit.r61 = 1'b1; end
            R62 : begin hit.r62 = 1'b1; end
            R63 : begin hit.r63 = 1'b1; end
            R64 : begin hit.r64 = 1'b1; end
            R65 : begin hit.r65 = 1'b1; end
            R66 : begin hit.r66 = 1'b1; end
            R67 : begin hit.r67 = 1'b1; end
            R68 : begin hit.r68 = 1'b1; end
            R69 : begin hit.r69 = 1'b1; end
            R70 : begin hit.r70 = 1'b1; end
            R71 : begin hit.r71 = 1'b1; end
            R72 : begin hit.r72 = 1'b1; end
            R73 : begin hit.r73 = 1'b1; end
            R74 : begin hit.r74 = 1'b1; end
            R75 : begin hit.r75 = 1'b1; end
            R76 : begin hit.r76 = 1'b1; end
            R77 : begin hit.r77 = 1'b1; end
            R78 : begin hit.r78 = 1'b1; end
            R79 : begin hit.r79 = 1'b1; end
            R80 : begin hit.r80 = 1'b1; end
            R81 : begin hit.r81 = 1'b1; end
            R82 : begin hit.r82 = 1'b1; end
            R83 : begin hit.r83 = 1'b1; end
            R84 : begin hit.r84 = 1'b1; end
            R85 : begin hit.r85 = 1'b1; end
            R86 : begin hit.r86 = 1'b1; end
            R87 : begin hit.r87 = 1'b1; end
            R88 : begin hit.r88 = 1'b1; end
            R89 : begin hit.r89 = 1'b1; end
            R90 : begin hit.r90 = 1'b1; end
            R91 : begin hit.r91 = 1'b1; end
            R92 : begin hit.r92 = 1'b1; end
            R93 : begin hit.r93 = 1'b1; end
            R94 : begin hit.r94 = 1'b1; end
            R95 : begin hit.r95 = 1'b1; end
            R96 : begin hit.r96 = 1'b1; end
            R97 : begin hit.r97 = 1'b1; end
            R98 : begin hit.r98 = 1'b1; end
            R99 : begin hit.r99 = 1'b1; end
           default: begin hit = '0; end
       endcase
       return hit;
    endfunction

   initial begin
      if (get_hit(R30) !== hit_t'{r30: 1'b1, default: '0}) $stop;
      if (get_hit('1) !== '0) $stop;
      if (get_hit('0) !== '0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
