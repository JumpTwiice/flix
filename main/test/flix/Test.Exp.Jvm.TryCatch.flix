/*
 *  Copyright 2021 Jonathan Lindegaard Starup
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

mod Test.Exp.Jvm.TryCatch {

    import java.lang.Math
    import java.lang.ArithmeticException
    import java.lang.IllegalArgumentException
    import java.lang.Exception

    def exception(): Unit \ IO =
        discard Math.floorDiv(1, 0);
        ()

    @test
    def testNoException01(): Bool =
        try {
            true
        } catch {
            case _: Exception => false
        }

    @test
    def testSimpleException01(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case _: Exception => true
        }

    @test
    def testMultipleExceptions01(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case _: ArithmeticException => true
            case _: IllegalArgumentException => false
        }

    @test
    def testMultipleExceptions02(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case _: IllegalArgumentException => false
            case _: ArithmeticException => true
        }

    @test
    def testMultipleExceptions03(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case _: IllegalArgumentException => false
        } catch {
            case _: ArithmeticException => true
        }

    @test
    def testBinding01(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case e: ArithmeticException => if (e.toString().isEmpty()) false else true
            case _: Exception => false
        }

    @test
    def testBinding02(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case e: ArithmeticException => if (e.getMessage().isEmpty()) false else true
            case _: Exception => false
        }

    @test
    def testPriority01(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case _: Exception => true
            case _: ArithmeticException => false
        }

    @test
    def testPriority02(): Bool \ IO =
        try {
            exception();
            false
        } catch {
            case _: ArithmeticException => true
            case _: Exception => false
        }

    @test
    def testNesting01(): Bool \ IO = {
        try {
            try {
                exception();
                false
            } catch {
                case _: ArithmeticException => true
            }
        } catch {
            case _: Exception => false
        }
    }

    @test
    def testNesting02(): Bool \ IO = {
        try {
            try {
                exception();
                false
            } catch {
                case _: IllegalArgumentException => false
            }
        } catch {
            case _: ArithmeticException => true
        }
    }

    @test
    def testNesting03(): Bool \ IO = {
        try {
            try {
                exception();
                false
            } catch {
                case _: ArithmeticException =>
                    exception();
                    false
            }
        } catch {
            case _: Exception => true
            case _: ArithmeticException => false
        }
    }

    @test
    def testNesting04(): Bool \ IO = {
        try {
            try {
                exception();
                false
            } catch {
                case _: ArithmeticException =>
                    exception();
                    false
            }
        } catch {
            case _: ArithmeticException => true
            case _: Exception => false
        }
    }

    @test
    def testNesting05(): Bool \ IO = {
        try {
            try {
                exception();
                false
            } catch {
                case _: ArithmeticException =>
                    exception();
                    false
                case _: Exception => false
            }
        } catch {
            case _: ArithmeticException => true
            case _: Exception => false
        }
    }


}
