// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Ted Campbell.
// SPDX-License-Identifier: CC0-1.0

//With MULTI_CLK defined shows bug, without it is hidden
`define MULTI_CLK

//bug634

module t (
    input                   i_clk_wr,
    input                   i_clk_rd
    );

    wire                    wr$wen;
    wire    [7:0]           wr$addr;
    wire    [7:0]           wr$wdata;
    wire    [7:0]           wr$rdata;

    wire                    rd$wen;
    wire    [7:0]           rd$addr;
    wire    [7:0]           rd$wdata;
    wire    [7:0]           rd$rdata;

    wire                    clk_wr;
    wire                    clk_rd;

    `ifdef MULTI_CLK
        assign clk_wr = i_clk_wr;
        assign clk_rd = i_clk_rd;
    `else
        assign clk_wr = i_clk_wr;
        assign clk_rd = i_clk_wr;
    `endif

    FooWr u_wr (
        .i_clk      ( clk_wr   ),

        .o_wen      ( wr$wen   ),
        .o_addr     ( wr$addr  ),
        .o_wdata    ( wr$wdata ),
        .i_rdata    ( wr$rdata )
        );

    FooRd u_rd (
        .i_clk      ( clk_rd   ),

        .o_wen      ( rd$wen   ),
        .o_addr     ( rd$addr  ),
        .o_wdata    ( rd$wdata ),
        .i_rdata    ( rd$rdata )
        );

    FooMem u_mem (
        .iv_clk     ( {clk_wr,  clk_rd  } ),
        .iv_wen     ( {wr$wen,  rd$wen  } ),
        .iv_addr    ( {wr$addr, rd$addr } ),
        .iv_wdata   ( {wr$wdata,rd$wdata} ),
        .ov_rdata   ( {wr$rdata,rd$rdata} )
        );

endmodule


// Memory Writer
module FooWr(
    input                   i_clk,

    output                  o_wen,
    output  [7:0]           o_addr,
    output  [7:0]           o_wdata,
    input   [7:0]           i_rdata
    );

    reg     [7:0]           cnt = 0;

    // Count [0,200]
    always @( posedge i_clk )
        if ( cnt < 8'd50 )
            cnt     <= cnt + 8'd1;

    // Write addr in (10,30) if even
    assign o_wen    = ( cnt > 8'd10 ) && ( cnt < 8'd30 ) && ( cnt[0] == 1'b0 );
    assign o_addr   = cnt;
    assign o_wdata  = cnt;

endmodule


// Memory Reader
module FooRd(
    input                   i_clk,

    output                  o_wen,
    output  [7:0]           o_addr,
    output  [7:0]           o_wdata,
    input   [7:0]           i_rdata
    );

    reg     [7:0]           cnt = 0;
    reg     [7:0]           addr_r;
    reg                     en_r;

    // Count [0,200]
    always @( posedge i_clk )
        if ( cnt < 8'd200 )
            cnt     <= cnt + 8'd1;

    // Read data
    assign o_wen    = 0;
    assign o_addr   = cnt - 8'd100;

    // Track issued read
    always @( posedge i_clk )
    begin
        addr_r <= o_addr;
        en_r   <= ( cnt > 8'd110 ) && ( cnt < 8'd130 ) && ( cnt[0] == 1'b0 );
    end

    // Display to console 100 cycles after writer
    always @( negedge i_clk )
        if ( en_r ) begin
`ifdef TEST_VERBOSE
           $display( "MEM[%x] == %x", addr_r, i_rdata );
`endif
           if (addr_r != i_rdata) $stop;
        end

endmodule


// Multi-port memory abstraction
module FooMem(
    input   [2  -1:0]       iv_clk,
    input   [2  -1:0]       iv_wen,
    input   [2*8-1:0]       iv_addr,
    input   [2*8-1:0]       iv_wdata,
    output  [2*8-1:0]       ov_rdata
    );

    FooMemImpl u_impl (
        .a_clk      ( iv_clk  [0*1+:1] ),
        .a_wen      ( iv_wen  [0*1+:1] ),
        .a_addr     ( iv_addr [0*8+:8] ),
        .a_wdata    ( iv_wdata[0*8+:8] ),
        .a_rdata    ( ov_rdata[0*8+:8] ),

        .b_clk      ( iv_clk  [1*1+:1] ),
        .b_wen      ( iv_wen  [1*1+:1] ),
        .b_addr     ( iv_addr [1*8+:8] ),
        .b_wdata    ( iv_wdata[1*8+:8] ),
        .b_rdata    ( ov_rdata[1*8+:8] )
        );

endmodule


// Dual-Port L1 Memory Implementation
module FooMemImpl(
    input                   a_clk,
    input                   a_wen,
    input   [7:0]           a_addr,
    input   [7:0]           a_wdata,
    output reg [7:0]        a_rdata,

    input                   b_clk,
    input                   b_wen,
    input   [7:0]           b_addr,
    input   [7:0]           b_wdata,
    output reg [7:0]        b_rdata
    );

    /* verilator lint_off MULTIDRIVEN */
    reg     [7:0]           mem[0:255];
    /* verilator lint_on  MULTIDRIVEN */

    always @( posedge a_clk )
        if ( a_wen )
            mem[a_addr] <= a_wdata;

    always @( posedge b_clk )
        if ( b_wen )
            mem[b_addr] <= b_wdata;

    always @( posedge a_clk )
        a_rdata <= mem[a_addr];

    always @( posedge b_clk )
        b_rdata <= mem[b_addr];

endmodule
