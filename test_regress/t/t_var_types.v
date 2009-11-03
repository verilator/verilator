// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2009 by Wilson Snyder.

module t (/*AUTOARG*/);

   // IEEE: integer_atom_type
   byte		d_byte;
   shortint	d_shortint;
   int		d_int;
   longint	d_longint;
   integer	d_integer;
   //UNSUP time		d_time;

   // IEEE: integer_atom_type
   bit		d_bit;
   logic	d_logic;
   reg		d_reg;

   bit	  [1:0]	d_bit2;
   logic  [1:0]	d_logic2;
   reg	  [1:0]	d_reg2;

   // IEEE: non_integer_type
   //UNSUP shortreal	d_shortreal;
   //UNSUP real		d_real;
   //UNSUP realtime	d_realtime;

   // verilator lint_off WIDTH
   localparam 		p_implicit = {96{1'b1}};
   localparam [89:0]	p_explicit = {96{1'b1}};
   localparam byte 	p_byte	= {96{1'b1}};
   localparam shortint 	p_shortint = {96{1'b1}};
   localparam int 	p_int	= {96{1'b1}};
   localparam longint 	p_longint = {96{1'b1}};
   localparam integer 	p_integer = {96{1'b1}};
   localparam reg 	p_reg	= {96{1'b1}};
   localparam bit 	p_bit	= {96{1'b1}};
   localparam logic 	p_logic	= {96{1'b1}};
   localparam reg [1:0]	p_reg2	= {96{1'b1}};
   localparam bit [1:0]	p_bit2	= {96{1'b1}};
   localparam logic [1:0] p_logic2= {96{1'b1}};
   // verilator lint_on WIDTH

   // verilator lint_off WIDTH
   function 		f_implicit;	f_implicit	= {96{1'b1}}; endfunction
   function [89:0]	f_explicit;	f_explicit	= {96{1'b1}}; endfunction
   function byte 	f_byte;		f_byte	 	= {96{1'b1}}; endfunction
   function shortint 	f_shortint;	f_shortint	= {96{1'b1}}; endfunction
   function int 	f_int;		f_int	 	= {96{1'b1}}; endfunction
   function longint 	f_longint;	f_longint	= {96{1'b1}}; endfunction
   function integer 	f_integer;	f_integer	= {96{1'b1}}; endfunction
   function reg 	f_reg;		f_reg	 	= {96{1'b1}}; endfunction
   function bit 	f_bit;		f_bit	 	= {96{1'b1}}; endfunction
   function logic 	f_logic;	f_logic		= {96{1'b1}}; endfunction
   function reg [1:0]	f_reg2;		f_reg2	 	= {96{1'b1}}; endfunction
   function bit [1:0]	f_bit2;		f_bit2	 	= {96{1'b1}}; endfunction
   function logic [1:0] f_logic2;	f_logic2	= {96{1'b1}}; endfunction
   // verilator lint_on WIDTH

`define CHECK_ALL(name,bits,issigned,twostate) \
   name = {96{1'b1}}; \
   if (name !== {(bits){1'b1}}) begin $display("%%Error: Bad size for %s",`"name`"); $stop; end \
   if (issigned ? (name > 0) : (name < 0)) begin $display("%%Error: Bad signed for %s",`"name`"); $stop; end \
   name = {96{1'bx}}; \

//Everything is twostate in Verilator
//   if (name !== {(bits){twostate ? 1'b0 : 1'bx}}) begin $display("%%Error: Bad twostate for %s",`"name`"); $stop; end \

   initial begin
      // verilator lint_off WIDTH
      // verilator lint_off UNSIGNED
      //         name           b  sign twost
      `CHECK_ALL(d_byte		,8 ,1'b1,1'b1);
      `CHECK_ALL(d_shortint	,16,1'b1,1'b1);
      `CHECK_ALL(d_int		,32,1'b1,1'b1);
      `CHECK_ALL(d_longint	,64,1'b1,1'b1);
      `CHECK_ALL(d_integer	,32,1'b1,1'b0);
      `CHECK_ALL(d_bit		,1 ,1'b0,1'b1);
      `CHECK_ALL(d_logic	,1 ,1'b0,1'b0);
      `CHECK_ALL(d_reg		,1 ,1'b0,1'b0);
      `CHECK_ALL(d_bit2		,2 ,1'b0,1'b1);
      `CHECK_ALL(d_logic2	,2 ,1'b0,1'b0);
      `CHECK_ALL(d_reg2		,2 ,1'b0,1'b0);
      // verilator lint_on WIDTH
      // verilator lint_on UNSIGNED

`define CHECK_P(name,bits) \
   if (name !== {(bits){1'b1}}) begin $display("%%Error: Bad size for %s",`"name`"); $stop; end \

      `CHECK_P(p_implicit	,96);
      `CHECK_P(p_explicit	,90);
      `CHECK_P(p_byte		,8 );
      `CHECK_P(p_shortint	,16);
      `CHECK_P(p_int		,32);
      `CHECK_P(p_longint	,64);
      `CHECK_P(p_integer	,32);
      `CHECK_P(p_bit		,1 );
      `CHECK_P(p_logic		,1 );
      `CHECK_P(p_reg		,1 );
      `CHECK_P(p_bit2		,2 );
      `CHECK_P(p_logic2		,2 );
      `CHECK_P(p_reg2		,2 );

`define CHECK_F(name,bits) \
   if (name() !== {(bits){1'b1}}) begin $display("%%Error: Bad size for %s",`"name`"); $stop; end \

      `CHECK_F(f_implicit	,1 );  // Note 1 bit, not 96
      `CHECK_F(f_explicit	,90);
      `CHECK_F(f_byte		,8 );
      `CHECK_F(f_shortint	,16);
      `CHECK_F(f_int		,32);
      `CHECK_F(f_longint	,64);
      `CHECK_F(f_integer	,32);
      `CHECK_F(f_bit		,1 );
      `CHECK_F(f_logic		,1 );
      `CHECK_F(f_reg		,1 );
      `CHECK_F(f_bit2		,2 );
      `CHECK_F(f_logic2		,2 );
      `CHECK_F(f_reg2		,2 );

      // For unpacked types we don't want width warnings for unsized numbers that fit
      d_byte	= 2;
      d_shortint= 2;
      d_int	= 2;
      d_longint	= 2;
      d_integer	= 2;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
