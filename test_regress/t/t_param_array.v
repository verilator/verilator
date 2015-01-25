// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Jeremy Bennett.

module t (/*AUTOARG*/);

   typedef enum int {
		     PADTYPE_DEFAULT = 32'd0,
		     PADTYPE_GPIO,
		     PADTYPE_VDD,
		     PADTYPE_GND
		     } t_padtype;

   localparam int STR_PINID [0:15]
		  = '{
		      "DEF", "ERR", "ERR", "ERR", "ERR", "ERR", "ERR", "ERR",
		      "PA0", "PA1", "PA2", "PA3", "PA4", "PA5", "PA6", "PA7"
		      };

   typedef struct packed {
     t_padtype padtype;
     int 	 aux;
   } t_pin_descriptor;

   localparam t_pin_descriptor
     PINOUT[ 1: 6]
     = '{
	 '{default:0, padtype:PADTYPE_GPIO, aux:1},
	 '{default:0, padtype:PADTYPE_GPIO},
	 '{default:0, padtype:PADTYPE_GPIO},
	 '{default:0, padtype:PADTYPE_GPIO},
	 '{default:0, padtype:PADTYPE_VDD},
	 '{default:0, padtype:PADTYPE_GND}
	 };

   localparam int PINOUT_SIZE = 6;
   localparam int PINOUT_WA[1:PINOUT_SIZE][3]
		  = '{
		      '{0, PADTYPE_GPIO, 0},
		      '{1, PADTYPE_GPIO, 0},
		      '{2, PADTYPE_GPIO, 0},
		      '{5, PADTYPE_GPIO, 0},
		      '{6, PADTYPE_VDD,  0},
		      '{8, PADTYPE_GND , 0}
		      };

   const int pinout_static_const[1:PINOUT_SIZE][3]
		  = '{
		      '{0, PADTYPE_GPIO, 0},
		      '{1, PADTYPE_GPIO, 0},
		      '{2, PADTYPE_GPIO, 0},
		      '{5, PADTYPE_GPIO, 0},
		      '{6, PADTYPE_VDD,  0},
		      '{8, PADTYPE_GND , 0}
		      };

   // Make sure consants propagate
   checkstr #(.PINID(STR_PINID[1]),
	      .EXP("ERR"))
       substr1 ();
   checkstr #(.PINID(STR_PINID[8]),
	      .EXP("PA0"))
       substr8 ();

   initial begin
      $display("PINID1 %s", STR_PINID[1]);
      $display("PINID8 %s", STR_PINID[8]);
      if (STR_PINID[1] != "ERR") $stop;
      if (STR_PINID[8] != "PA0") $stop;
      if (pinout_static_const[1][0] != 0) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module checkstr;
   parameter int PINID = " ";
   parameter int EXP   = " ";
   initial begin
      $display("PID %s  EXP %s", PINID, EXP);
      if (EXP != "ERR" && EXP != "PA0") $stop;
      if (PINID != EXP) $stop;
   end
endmodule
