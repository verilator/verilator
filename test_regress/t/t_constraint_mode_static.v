// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// Test static constraint_mode() support per IEEE 1800-2017 Section 18.4, 18.8
// Static constraint mode should be shared across all instances.

class StaticConstraintTest;
    rand bit [7:0] value;

    // Static constraint - shared across all instances
    static constraint static_con {
        value inside {[10:50]};
    }

    // Non-static constraint for comparison
    constraint instance_con {
        value > 5;
    }
endclass

module t;
    StaticConstraintTest obj1, obj2;

    initial begin
        obj1 = new();
        obj2 = new();

        // Test 1: Verify static constraint_mode getter works
        if (obj1.static_con.constraint_mode() != 1) $stop;
        if (obj2.static_con.constraint_mode() != 1) $stop;

        // Test 2: Disable static constraint on one instance
        obj1.static_con.constraint_mode(0);

        // Verify the state is shared across all instances
        if (obj1.static_con.constraint_mode() != 0) $stop;
        if (obj2.static_con.constraint_mode() != 0) $stop;

        // Test 3: Re-enable static constraint via different instance
        obj2.static_con.constraint_mode(1);

        // Verify state is updated for all instances
        if (obj1.static_con.constraint_mode() != 1) $stop;
        if (obj2.static_con.constraint_mode() != 1) $stop;

        // Test 4: Verify randomization respects constraint mode when enabled
        obj1.static_con.constraint_mode(1);
        obj1.instance_con.constraint_mode(1);
        for (int i = 0; i < 10; i++) begin
            void'(obj1.randomize());
            if (!(obj1.value inside {[10:50]})) $stop;
            if (!(obj1.value > 5)) $stop;
        end

        // Test 5: Disable static constraint and verify randomization changes
        obj1.static_con.constraint_mode(0);
        // With static_con disabled, value only needs to be > 5
        for (int i = 0; i < 10; i++) begin
            obj1.value = 1;  // Reset to low value
            void'(obj1.randomize());
            if (!(obj1.value > 5)) $stop;
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule
