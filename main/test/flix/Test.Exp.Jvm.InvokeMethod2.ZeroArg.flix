mod Test.Exp.Jvm.InvokeMethod.ZeroArg {

    @test
    def testInvokeMethod_01(): Bool \ IO =
        let obj = "HELLO WORLD";
        obj.toLowerCase() == "hello world"

    @test
    def testInvokeMethod_02(): Bool \ IO =
        let obj = "hello world";
        obj.toUpperCase() == "HELLO WORLD"

    @test
    def testInvokeMethod_03(): Bool \ IO =
        let obj = "hello world";
        obj.length() == 11

    @test
    def testInvokeMethod_04(): Bool \ IO =
        let obj = "   hello world    ";
        obj.trim() == "hello world"

    @test
    def testInvokeMethod_05(): Bool \ IO =
        let obj = "hello world";
        obj.intern() == obj

    @test
    def testInvokeMethod_6(): Bool \ IO =
        let val = 12093ii;
        val.intValueExact() == 12093

    @test
    def testInvokeMethod_7(): Bool \ IO =
        let val = -20938ii;
        val.floatValue() == -20938f32

    @test
    def testInvokeMethod_8(): Bool \ IO =
        let val = 34882ii;
        val.getLowestSetBit() == 1

    @test
    def testInvokeMethod_9(): Bool \ IO =
        let val = 2384721ii;
        val.bitCount() == 9

    @test
    def testInvokeMethod_10(): Bool \ IO =
        let val = -32ii;
        val.abs() == 32ii

    @test
    def testInvokeMethod_11(): Bool \ IO =
        let val = -123.45ff;
        val.abs() == 123.45ff

    @test
    def testInvokeMethod_12(): Bool \ IO =
        let val = 12443.1489ff;
        val.precision() == 9

    @test
    def testInvokeMethod_13(): Bool \ IO =
        let val = -50.000001ff;
        val.plus() == -50.000001ff

    @test
    def testInvokeMethod_14(): Bool \ IO =
        let val = 23984.1119ff;
        val.doubleValue() == 23984.1119f64

    @test
    def testInvokeMethod_15(): Bool \ IO =
        let val = 57842.0109ff;
        val.floatValue() == 57842.0109f32
}
