// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Jeremy Bennett
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef enum int {
    PADTYPE_DEFAULT = 32'd0,
    PADTYPE_GPIO,
    PADTYPE_VDD,
    PADTYPE_GND
  } t_padtype;

  // verilog_format: off
  localparam int STR_PINID [0:15] = '{
                      "DEF", "ERR", "ERR", "ERR", "ERR", "ERR", "ERR", "ERR",
                      "PA0", "PA1", "PA2", "PA3", "PA4", "PA5", "PA6", "PA7"
                      };
  // verilog_format: on

  typedef struct packed {
    t_padtype padtype;
    int aux;
  } t_pin_descriptor;

  localparam t_pin_descriptor PINOUT[1:6] = '{
      '{default: 0, padtype: PADTYPE_GPIO, aux: 1},
      '{default: 0, padtype: PADTYPE_GPIO},
      '{default: 0, padtype: PADTYPE_GPIO},
      '{default: 0, padtype: PADTYPE_GPIO},
      '{default: 0, padtype: PADTYPE_VDD},
      '{default: 0, padtype: PADTYPE_GND}
  };

  localparam int PINOUT_SIZE = 6;
  localparam int PINOUT_WA[1:PINOUT_SIZE][3] = '{
      '{0, PADTYPE_GPIO, 0},
      '{1, PADTYPE_GPIO, 0},
      '{2, PADTYPE_GPIO, 0},
      '{5, PADTYPE_GPIO, 0},
      '{6, PADTYPE_VDD, 0},
      '{8, PADTYPE_GND, 0}
  };

  const
  int
  pinout_static_const[1:PINOUT_SIZE][3] = '{
      '{0, PADTYPE_GPIO, 0},
      '{1, PADTYPE_GPIO, 0},
      '{2, PADTYPE_GPIO, 0},
      '{5, PADTYPE_GPIO, 0},
      '{6, PADTYPE_VDD, 0},
      '{8, PADTYPE_GND, 0}
  };

  // Make sure consants propagate
  checkstr #(
      .PINID(STR_PINID[1]),
      .EXP("ERR")
  ) substr1 ();
  checkstr #(
      .PINID(STR_PINID[8]),
      .EXP("PA0")
  ) substr8 ();

  // Dynamically sized localparams
  localparam int DYN[] = '{1, 2, 3};
  localparam int QUE[$] = '{4, 5};
  localparam int BQUE[$:1] = '{4, 5, 6};
  localparam int ASC[string] = '{"a": 6, "b": 7};
  localparam int WLD[*] = '{1: 8, 2: 9};

  // Dynamically sized parameters
  dynparams dflt ();
  dynparams #(
      .DYN('{8, 9}),
      .QUE('{10}),
      .BQUE('{10, 11, 12}),
      .ASC('{"c": 11}),
      .WLD('{5: 12, 6: 13, 7: 14})
  ) ovrd ();
  dynparams #(
      .DYN(DYN),
      .QUE(QUE),
      .BQUE(BQUE),
      .ASC(ASC),
      .WLD(WLD)
  ) lovrd ();

  initial begin
    $display("PINID1 %s", STR_PINID[1]);
    $display("PINID8 %s", STR_PINID[8]);
    if (STR_PINID[1] != "ERR") $stop;
    if (STR_PINID[8] != "PA0") $stop;
    if (pinout_static_const[1][0] != 0) $stop;
    if (DYN.size() != 3) $stop;
    if (DYN[2] != 3) $stop;
    if (QUE.size() != 2) $stop;
    if (QUE[1] != 5) $stop;
    if (BQUE.size() != 2) $stop;
    if (BQUE[1] != 5) $stop;
    if (ASC.num() != 2) $stop;
    if (ASC["b"] != 7) $stop;
    if (WLD.num() != 2) $stop;
    if (WLD[2] != 9) $stop;
    if (dflt.DYN.size() != 4) $stop;
    if (dflt.DYN[3] != 24) $stop;
    if (dflt.QUE.size() != 1) $stop;
    if (dflt.QUE[0] != 25) $stop;
    if (dflt.BQUE.size() != 2) $stop;
    if (dflt.BQUE[1] != 27) $stop;
    if (dflt.ASC.num() != 1) $stop;
    if (dflt.ASC["d"] != 29) $stop;
    if (dflt.WLD.num() != 1) $stop;
    if (dflt.WLD[3] != 30) $stop;
    if (ovrd.DYN.size() != 2) $stop;
    if (ovrd.DYN[1] != 9) $stop;
    if (ovrd.QUE.size() != 1) $stop;
    if (ovrd.QUE[0] != 10) $stop;
    if (ovrd.BQUE.size() != 2) $stop;
    if (ovrd.BQUE[1] != 11) $stop;
    if (ovrd.ASC.num() != 1) $stop;
    if (ovrd.ASC["c"] != 11) $stop;
    if (ovrd.WLD.num() != 3) $stop;
    if (ovrd.WLD[6] != 13) $stop;
    if (lovrd.DYN.size() != 3) $stop;
    if (lovrd.DYN[2] != 3) $stop;
    if (lovrd.QUE.size() != 2) $stop;
    if (lovrd.QUE[1] != 5) $stop;
    if (lovrd.BQUE.size() != 2) $stop;
    if (lovrd.BQUE[1] != 5) $stop;
    if (lovrd.ASC.num() != 2) $stop;
    if (lovrd.ASC["b"] != 7) $stop;
    if (lovrd.WLD.num() != 2) $stop;
    if (lovrd.WLD[2] != 9) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module checkstr;
  parameter int PINID = " ";
  parameter int EXP = " ";
  initial begin
    $display("PID %s  EXP %s", PINID, EXP);
    if (EXP != "ERR" && EXP != "PA0") $stop;
    if (PINID != EXP) $stop;
  end
endmodule

module dynparams #(
    parameter int DYN[] = '{21, 22, 23, 24},
    parameter int QUE[$] = '{25},
    parameter int BQUE[$:1] = '{26, 27, 28},
    parameter int ASC[string] = '{"d": 29},
    parameter int WLD[*] = '{3: 30}
);
endmodule
