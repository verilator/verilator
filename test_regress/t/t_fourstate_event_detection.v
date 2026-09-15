// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit   posedgeTriggered = 0;
  bit   negedgeTriggered = 0;
  bit   bothedgeTriggered = 0;
  bit   changeTriggered = 0;
  bit   initialized = 0;
  logic val = 0;

  typedef enum bit [1:0] {
    POS,
    NEG,
    CHANGE,
    NONE
  } expected_event_t;

  task assertTriggered(expected_event_t eventType);
    if (eventType == POS) begin
      if (!posedgeTriggered) $stop;
      if (negedgeTriggered) $stop;
      if (!bothedgeTriggered) $stop;
      if (!changeTriggered) $stop;
    end else if (eventType == NEG) begin
      if (posedgeTriggered) $stop;
      if (!negedgeTriggered) $stop;
      if (!bothedgeTriggered) $stop;
      if (!changeTriggered) $stop;
    end else if (eventType == CHANGE) begin
      if (posedgeTriggered) $stop;
      if (negedgeTriggered) $stop;
      if (bothedgeTriggered) $stop;
      if (!changeTriggered) $stop;
    end else if (eventType == NONE) begin
      if (posedgeTriggered) $stop;
      if (negedgeTriggered) $stop;
      if (bothedgeTriggered) $stop;
      if (changeTriggered) $stop;
    end
    posedgeTriggered  = 0;
    negedgeTriggered  = 0;
    bothedgeTriggered = 0;
    changeTriggered   = 0;
  endtask

  always @(val) begin
    if (initialized & changeTriggered) $stop;
    changeTriggered = 1;
  end

  always @(edge val) begin
    if (bothedgeTriggered) $stop;
    bothedgeTriggered = 1;
  end

  always @(posedge val) begin
    if (posedgeTriggered) $stop;
    posedgeTriggered = 1;
  end

  always @(negedge val) begin
    if (negedgeTriggered) $stop;
    negedgeTriggered = 1;
  end

  initial begin
    #1 changeTriggered = 0;
    initialized = 1;
    #1 val = 1;
    #1 assertTriggered(POS);
    #1 val = 1;
    #1 assertTriggered(NONE);
    #1 val = 'x;
    #1 assertTriggered(NEG);
    #1 val = 'z;
    #1 assertTriggered(CHANGE);
    #1 val = 0;
    #1 assertTriggered(NEG);
    #1 val = 'z;
    #1 assertTriggered(POS);
    #1 val = 'z;
    #1 assertTriggered(NONE);
    #1 val = 'x;
    #1 assertTriggered(CHANGE);
    #1 val = 'x;
    #1 assertTriggered(NONE);
    #1 val = 'z;
    #1 assertTriggered(CHANGE);
    #1 val = 'x;
    #1 assertTriggered(CHANGE);
    #1 val = 0;
    #1 assertTriggered(NEG);
    #1 val = 1;
    #1 assertTriggered(POS);
    #1 val = 0;
    #1 assertTriggered(NEG);
    #1 val = 'x;
    #1 assertTriggered(POS);
    #1 val = 1;
    #1 assertTriggered(POS);
    #1 val = 'z;
    #1 assertTriggered(NEG);
    #1 val = 1;
    #1 assertTriggered(POS);
    #1 val = 0;
    #1 assertTriggered(NEG);
    #1 val = 0;
    #1 assertTriggered(NONE);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
