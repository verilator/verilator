// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

module pads
 #( parameter
    NUMPADS = $size( pinout )
  )
 (
  // ***************************************************************************
  // Module Interface
  // ***************************************************************************

  // **** Interfaces ****
  pads_if.mp_pads padsif,


  // **** Pinout ****
`ifdef VERILATOR  // see t_tri_array
  inout wire [NUMPADS:1] pad,
`else
  inout wire pad [1:NUMPADS],
`endif

  // **** Inputs ****
  input logic       clk,
  input logic       rst
 );


  // ***************************************************************************
  // Code Section
  // ***************************************************************************

`ifdef VERILATOR  // see t_tri_array
   tri [NUMPADS:1] _anahack;
`endif


  genvar i;
  for ( i = 1; i <= NUMPADS; i++ )
    begin
`ifdef VCS
      localparam t_padtype p_type = t_padtype'(pinout_wa[i][pinout_wa_padtype]);
      localparam t_pinid   p_id   = t_pinid'(pinout_wa[i][pinout_wa_id]);
`else
      localparam t_padtype p_type = pinout[i].padtype;
      localparam t_pinid   p_id   = pinout[i].id;
`endif

      case ( p_type )
        PADTYPE_GPIO:
          pad_gpio #( .ID( i ) )
            i_pad_gpio(
                       .pad             (pad                 [i]),
                       // Outputs
                       .input_val       (padsif.input_val    [i]),
                       // Inouts
`ifdef VERILATOR  // see t_tri_array
                       .ana             (_anahack            [i]),
`else
                       .ana             (padsif.ana          [i]),
`endif
                       // Inputs
                       .pullup_en       (padsif.pullup_en    [i]),
                       .pulldown_en     (padsif.pulldown_en  [i]),
                       .output_en       (padsif.output_en    [i]),
                       .output_val      (padsif.output_val   [i]),
                       .slew_limit_en   (padsif.slew_limit_en[i]),
                       .input_en        (padsif.input_en     [i])
                       /*AUTOINST*/);

        PADTYPE_VDD:
          begin
            pad_vdd #( .ID( i ) )
              i_pad_vdd(
                        .pad            (pad[i])
                        /*AUTOINST*/);
// Not SV standard, yet...           assign padsif.input_val[i] = ();
          end

        PADTYPE_GND:
          begin
            pad_gnd #( .ID( i ) )
              i_pad_gnd(.pad            (pad[i])
                        /*AUTOINST*/);
          end
      endcase
    end

endmodule // pads
