mod Test.Handler.Spawn {

    eff Ask {
        def ask(x: Int32): Unit
    }

    eff Gen {
        def gen(): Int32
    }

    def runAsk(tx: Sender[Int32]): Unit \ Chan =
        run {
            Ask.ask(42)
        } with handler Ask {
            def ask(x, _) = Channel.send(x, tx)
        }

    def runGen(tx: Sender[Int32]): Unit \ Chan =
        run {
            Channel.send(Gen.gen(), tx)
        } with handler Gen {
            def gen(k) = k(42)
        }

    def runGenAsk(tx: Sender[Int32]): Unit \ Chan =
        run {
            Ask.ask(
                run {
                    Gen.gen()
                } with handler Gen {
                    def gen(k) = k(42)
                }
            )
        } with handler Ask {
            def ask(x, _) = Channel.send(x + x, tx)
        }

    @Test
    def testSpawn01(): Bool \ {Chan, NonDet} =
        let result = region rc {
            let (tx, rx) = Channel.unbuffered();
            spawn runGen(tx) @ rc;
            Channel.recv(rx)
        };
        Assert.eq(42, result)

    @Test
    def testSpawn02(): Bool \ {Chan, NonDet} =
        let result = region rc {
            let (tx, rx) = Channel.unbuffered();
            spawn runAsk(tx) @ rc;
            Channel.recv(rx)
        };
        Assert.eq(42, result)

    @Test
    def testSpawn03(): Bool \ {Chan, NonDet} =
        let result = region rc {
            let (tx, rx) = Channel.unbuffered();
            spawn runGenAsk(tx) @ rc;
            Channel.recv(rx)
        };
        Assert.eq(84, result)

}
