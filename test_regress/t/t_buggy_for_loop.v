// DESCRIPTION: Verilator: SystemVerilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
`define BIT_PERIOD_CC 32
`define SYS_CLK_PERIOD 8000 
parameter shortint unsigned              W_DATA             = 32; 
parameter int unsigned                   X_WORD_ADDR        = 4; 
parameter                  [5:0]         C_RX_DATA_LEN      = 44; 
logic i2tag;
logic sys_clk;
task sendZero;
    begin
       i2tag =0;
       repeat (`BIT_PERIOD_CC/2) @(posedge sys_clk); //
       i2tag =1;
       repeat (`BIT_PERIOD_CC/2) @(posedge sys_clk); //
       i2tag =0;
    end
endtask:sendZero 


task sendOne;
    begin
       repeat (`BIT_PERIOD_CC) @(posedge sys_clk); 
    end
endtask:sendOne 
//------------------------------------------
// Calc Parity
//------------------------------------------
function logic [44:0] calc_parity ( input [W_DATA-1:0] i_data );
    logic [44:0] o_data;
    int one_cnt; 
    int offset;
        one_cnt =0;
        offset=0;
       $write("<<<<<<<----- start calculating parity on data %0h ----->>>>>\n", i_data);
        for (int i =0 ; i < W_DATA ; i++) begin
            if (i_data[i] == 1'b1 ) begin
                one_cnt = one_cnt+1;
                o_data[i+offset] =1'b1;
            end else begin
                o_data[i+offset] =1'b0;
            end
            if ( ((i+1) % 8) == 0 ) begin // entire byte so far, now send the bit parity
                offset = (i+1)/8;
                if ( (one_cnt % 2) == 1) begin
                    o_data[i+offset] =1'b1;
                end else begin
                    o_data[i+offset] =1'b0;
                end
                one_cnt =0;
            end
        end
        // send 8 column parity bits
        if ((i_data[24] ^ i_data[16] ^ i_data[8]  ^ i_data[0] ) == 1'b1) begin o_data[36] =1'b1;; end else begin o_data[36] =1'b0;; end
        if ((i_data[25] ^ i_data[17] ^ i_data[9]  ^ i_data[1] ) == 1'b1) begin o_data[37] =1'b1;; end else begin o_data[37] =1'b0;; end
        if ((i_data[26] ^ i_data[18] ^ i_data[10] ^ i_data[2] ) == 1'b1) begin o_data[38] =1'b1;; end else begin o_data[38] =1'b0;; end
        if ((i_data[27] ^ i_data[19] ^ i_data[11] ^ i_data[3] ) == 1'b1) begin o_data[39] =1'b1;; end else begin o_data[39] =1'b0;; end
        if ((i_data[28] ^ i_data[20] ^ i_data[12] ^ i_data[4] ) == 1'b1) begin o_data[40] =1'b1;; end else begin o_data[40] =1'b0;; end
        if ((i_data[29] ^ i_data[21] ^ i_data[13] ^ i_data[5] ) == 1'b1) begin o_data[41] =1'b1;; end else begin o_data[41] =1'b0;; end
        if ((i_data[30] ^ i_data[22] ^ i_data[14] ^ i_data[6] ) == 1'b1) begin o_data[42] =1'b1;; end else begin o_data[42] =1'b0;; end
        if ((i_data[31] ^ i_data[23] ^ i_data[15] ^ i_data[7] ) == 1'b1) begin o_data[43] =1'b1;; end else begin o_data[43] =1'b0;; end
        //sendZero();
        o_data[44] =1'b0;
        $write("<<<<<<<----- computed parity word data %0h completed ----->>>>>\n", o_data);
        return o_data;
endfunction :calc_parity 
//------------------------------------------
// Calc sendData 
//------------------------------------------

task sendData( input [W_DATA-1:0] i_data );
    logic [C_RX_DATA_LEN:0] em_data_and_parity;
    begin
       em_data_and_parity=calc_parity(i_data);
       $write("<<<<<<<----- start sending data %0h with computed parity %0h ----->>>>>\n", i_data, em_data_and_parity);
       for (int i =0 ; i <= C_RX_DATA_LEN  ; i++) begin // Send MSB first
           if (em_data_and_parity[i] == 1'b1 ) begin
               sendOne();
           end else begin
               sendZero();
           end
       end
        $write("<<<<<<<----- sending data %0h completed ----->>>>>\n", i_data);
    end
endtask :sendData 

//------------------------------------------
// Calc sendAddr
//------------------------------------------
task sendAddr( input [X_WORD_ADDR-1:0] i_addr );
    begin
       logic  parity;
       $write("<<<<<<<----- sending addr %0h transaction ----->>>>>\n", i_addr);
       parity =^i_addr; 
       for (int i =0 ; i < X_WORD_ADDR  ; i++) begin // Send MSB first
           if (i_addr[i] == 1'b1 ) begin
               sendOne();
           end else begin
               sendZero();
           end
       end
       sendZero();
       sendZero();
       if (parity == 1'b1 ) begin
           sendOne();
       end else begin
           sendZero();
       end
       $write("<<<<<<<----- sending addr %0h transaction completed ----->>>>>\n", i_addr);
    end
endtask :sendAddr 
always begin
 #((`SYS_CLK_PERIOD * 1ns)/2) sys_clk = !sys_clk;
end

   initial begin
    sys_clk          = 0;
    i2tag            = 0;
    sendAddr(4'h8);
    sendData(32'hDEADC0C0);
    $write("*-* All Finished *-*\n");
    $finish;

   end
endmodule
