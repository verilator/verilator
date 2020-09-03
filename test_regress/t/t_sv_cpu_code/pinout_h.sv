// DESCRIPTION: Verilator: Large test for SystemVerilog

// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012.
// SPDX-License-Identifier: CC0-1.0

// Contributed by M W Lund, Atmel Corporation.

`ifndef _PINOUT_H_SV_
 `define _PINOUT_H_SV_

// *****************************************************************************
// Structs/Unions
// *****************************************************************************

// **** Pin Descriptor ****

// - Pin Descriptor -
typedef struct packed
{
 t_pinid   id;
 t_padtype padtype;
 int       aux;
} t_pin_descriptor;



// *****************************************************************************
// Pinout
// *****************************************************************************

// **** Preferred Solution !!!! ****
localparam t_pin_descriptor
  pinout[ 1: 6]
  = '{
      '{default:0, id:PINID_A0,   padtype:PADTYPE_GPIO, aux:1},
      '{default:0, id:PINID_A1,   padtype:PADTYPE_GPIO},
      '{default:0, id:PINID_A2,   padtype:PADTYPE_GPIO},
      '{default:0, id:PINID_D0,   padtype:PADTYPE_GPIO},
      '{default:0, id:PINID_VDD0, padtype:PADTYPE_VDD},
      '{default:0, id:PINID_GND0, padtype:PADTYPE_GND}
      };


// **** Workaround !!!! ****
typedef enum int
{
 pinout_wa_id = 1,
 pinout_wa_padtype,
 pinout_wa_aux
 } t_pinout_wa;

localparam int pinout_size = 6;
localparam int pinout_wa[1:pinout_size][pinout_wa_id:pinout_wa_aux] =
'{
  '{PINID_A0,   PADTYPE_GPIO, 0},
  '{PINID_A1,   PADTYPE_GPIO, 0},
  '{PINID_A2,   PADTYPE_GPIO, 0},
  '{PINID_D0,   PADTYPE_GPIO, 0},
  '{PINID_VDD0, PADTYPE_VDD,  0},
  '{PINID_GND0, PADTYPE_GND , 0}
  };



`endif //  `ifndef _PINOUT_H_SV_

// **** End of File ****
