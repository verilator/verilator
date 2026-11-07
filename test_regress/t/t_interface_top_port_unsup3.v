// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

interface other_if;
endinterface

interface inner_if(other_if childs_port);
endinterface

interface outer_if(inner_if child);
endinterface

module t(outer_if outer);
endmodule
