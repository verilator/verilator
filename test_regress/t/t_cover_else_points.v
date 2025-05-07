// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
module t_cover_else_points  ;
    logic        is_su_mode;
    logic        is_em_emul;
    logic        is_ata_emul;
/* verilator lint_off UNUSEDSIGNAL */
    logic [3:0]  user_word_cnt;
/* verilator lint_on UNUSEDSIGNAL */
    logic        page;
    logic [6:0]  cfg;
    initial begin
       is_su_mode    =1'b1;
       is_em_emul    =1'b0;
       is_ata_emul   =1'b0;
       page          =1'b0;
       cfg           =7'h05;
       #100;
       is_su_mode    =1'b0;
       is_em_emul    =1'b1;
       is_ata_emul   =1'b0;
       page          =1'b0;
       cfg           =7'h06;
       #100;
       is_su_mode    =1'b0;
       is_em_emul    =1'b0;
       is_ata_emul   =1'b1;
       page          =1'b0;
       cfg           =7'h10;
       #100;
       is_su_mode    =1'b0;
       is_em_emul    =1'b0;
       is_ata_emul   =1'b1;
       page          =1'b1;
       cfg           =7'h60;
       #100;
       is_su_mode    =1'b0;
       is_em_emul    =1'b0;
       is_ata_emul   =1'b1;
       page          =1'b1;
       cfg           =7'h60;
       #100;
       is_su_mode    =1'b0;
       is_em_emul    =1'b0;
       is_ata_emul   =1'b1;
       page          =1'b1;
       cfg           =7'h40;
       #100;
       is_su_mode    =1'b0;
       is_em_emul    =1'b0;
       is_ata_emul   =1'b1;
       page          =1'b0;
       cfg           =7'h50;
       #100;
       $write("*-* All Finished *-*\n");
       $finish;
    end
    a a_inst(
         .i_is_su_mode     ( is_su_mode   ),
         .i_page           ( page         ),
         .i_cfg            ( cfg          ),
         .i_is_em_emul     ( is_em_emul   ),
         .i_is_ata_emul    ( is_ata_emul  ),
         .o_user_word_count( user_word_cnt)
    );
endmodule
/* verilator lint_off DECLFILENAME */
module a (
/* verilator lint_on DECLFILENAME */
    input logic        i_is_su_mode ,
    input logic        i_page ,
    input logic [6:0]  i_cfg        ,
    input logic        i_is_em_emul ,
    input logic        i_is_ata_emul,
    output logic [3:0] o_user_word_count
);
    always_comb begin
        o_user_word_count='0;
        if (i_is_su_mode == 1'b1) begin
                o_user_word_count    =  4'b0000;
        end
        else if (i_is_em_emul == 1'b1 ) begin
                case(i_cfg[3:0])
                  4'b0101: begin
                        o_user_word_count    =  4'b0000;
                  end
                  4'b0110: begin
                        o_user_word_count    =  4'b0001;
                  end
                  4'b0111: begin
                        o_user_word_count    =  4'b0010;
                  end
                  4'b1000: begin
                        o_user_word_count    =  4'b0011;
                  end
                  4'b1001: begin
                        o_user_word_count    =  4'b0100;
                  end
                  4'b1010: begin
                        o_user_word_count    =  4'b0101;
                  end
                  4'b1011: begin
                        o_user_word_count    =  4'b0110;
                  end
                  4'b1100: begin
                        o_user_word_count    =  4'b0111;
                  end
                  4'b1101: begin
                        o_user_word_count    =  4'b1000;
                  end
                  default: begin
                        o_user_word_count    =  4'b0011;
                  end
                endcase
        end
        else if (i_is_ata_emul == 1'b1) begin
                case(i_cfg[6:4])
                  3'b000: begin
                        o_user_word_count    =  4'b0000;
                  end
                  3'b001: begin
                        o_user_word_count    =  4'b0000;
                  end
                  3'b010: begin
                        o_user_word_count    =  4'b0001;
                  end
                  3'b011: begin
                        o_user_word_count    =  4'b0010;
                  end
                  3'b100: begin
                      if (i_page == 1'b1) begin
                        o_user_word_count    =  4'b0010;
                      end else begin
                        o_user_word_count    =  4'b0011;
                      end
                  end
                  3'b101: begin
                      if (i_page == 1'b1) begin
                        o_user_word_count    =  4'b0010;
                      end else begin
                        o_user_word_count    =  4'b0100;
                      end
                  end
                  3'b110: begin
                      if (i_page == 1'b1) begin
                        o_user_word_count    =  4'b0010;
                      end else begin
                        o_user_word_count    =  4'b0101;
                      end
                  end
                  3'b111: begin
                      if (i_page == 1'b1) begin
                        o_user_word_count    =  4'b0010;
                      end else begin
                        o_user_word_count    =  4'b0110;
                      end
                  end
                  default: begin
                        o_user_word_count    =  4'b0010;
                  end
                endcase
        end
        else begin       // default
                        o_user_word_count    =  4'b0000;
        end
    end
endmodule
