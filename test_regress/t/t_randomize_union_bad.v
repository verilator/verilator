typedef union {
    int int_value;
    bit [31:0] bits;
} UnpackedUnion;

class UnpackedUnionErrorTest;
    rand UnpackedUnion union_instance;

    function new();
        union_instance.bits = 32'b0;
    endfunction

endclass

module t_randomize_union_bad;

    UnpackedUnionErrorTest test_unpacked_union;

    initial begin
        test_unpacked_union = new();
        repeat(10) begin
            int success;
            success = test_unpacked_union.randomize();
            if (success != 1) $stop;
            $display("UnpackedUnion: int_value: %b, bits: %b", test_unpacked_union.union_instance.int_value, test_unpacked_union.union_instance.bits);
        end
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule