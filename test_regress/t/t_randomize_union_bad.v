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
            if (!test_unpacked_union.randomize()) $error("Randomization failed");
            $display("UnpackedUnion: int_value: %d, bits: %b", test_unpacked_union.union_instance.int_value, test_unpacked_union.union_instance.bits);
        end

        $finish;
    end
endmodule