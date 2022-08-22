// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class EventClass;
    event e;

    task sleep; @e; endtask
    task wake; ->e; endtask
endclass
