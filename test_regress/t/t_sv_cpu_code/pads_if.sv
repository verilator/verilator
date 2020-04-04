// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.


interface pads_if();

  // ***************************************************************************
  // Local Parameters
  // ***************************************************************************

  localparam
    NUMPADS = $size( pinout );


  // ***************************************************************************
  // Interface Variables
  // ***************************************************************************

  // - PADS Digital Interface -
  logic     pullup_en     [1:NUMPADS];// Pull-up/down/bus-keeper enable.
  logic     pulldown_en   [1:NUMPADS];// Pull direction (0:Pull-up; 1:Pull-down).
  logic     output_en     [1:NUMPADS];// Digital output buffer enable.
  logic     output_val    [1:NUMPADS];// Digital output value.
  logic     input_en      [1:NUMPADS];// Digital input buffer enable.
  logic     slew_limit_en [1:NUMPADS];// Slew rate limiter enable.
  logic     input_val     [1:NUMPADS];// Digital input value.

  // - PADS Analog Interface -
  logic     ana_override  [1:NUMPADS];// Disables digital output when driving analog output.
  wire      ana           [1:NUMPADS];



  // ***************************************************************************
  // Modports
  // ***************************************************************************

  modport mp_pads(
   input         pullup_en,
   input         pulldown_en,
   input         output_en,
   input         output_val,
   input         slew_limit_en,
   input         input_en,
   output        input_val,
   input         ana_override,
   inout         ana );

  modport mp_dig(
   import        IsPad,
   import        IsPort,
   import        Init,
   output        pullup_en,
   output        pulldown_en,
   output        output_en,
   output        output_val,
   output        slew_limit_en,
   output        input_en,
   input         input_val );

  modport mp_ana(
   import        IsPad,
   output        ana_override,
   inout         ana );



  // ***************************************************************************
  // Check for which pins exists
  // ***************************************************************************

  bit [PINID_D7:PINID_A0] exists;

  function automatic void Init( );
     exists = {(PINID_D7+1){1'b0}};
     for ( int i = 1; i <= $size( pinout ); i++ )
       if ( PINID_D7 >= pinout[i].id )
         exists[pinout[i].id] = 1'b1;
  endfunction


  // ***************************************************************************
  // Functions and Tasks
  // ***************************************************************************

  function automatic bit IsPad( integer i );
     IsPad = exists[i];
  endfunction

  function automatic bit IsPort( integer i );
     IsPort = |exists[8*i+:8];
  endfunction



endinterface // pads_if
