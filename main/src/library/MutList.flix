/*
 * Copyright 2019 Magnus Madsen, Esben Bjerre
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

///
/// Represents a mutable list.
///
/// Invariant
///   - The length is always higher than the total capacity of the array.
///   - The capacity of the array is always 8 or more.
///
pub struct MutList[a: Type, r: Region] {
    r: Region[r],
    mut values: Array[a, r],
    mut length: Int32
}

instance Iterable[MutList[a, r]] {
    type Elm = a
    type Aef = r
    pub def iterator(rc: Region[r1], l: MutList[a, r]): Iterator[a, r + r1, r1] \ (r + r1) = MutList.iterator(rc, l)
}

instance Indexable[MutList[a, r]] {
    type Idx = Int32
    type Elm = a
    type Aef = r + OutOfBounds
    pub def get(t: MutList[a, r], i: Int32): a \ r + OutOfBounds =
        MutList.get(i, t)
}

instance IndexableMut[MutList[a, r]] {
    type Aef = r + OutOfBounds
    pub def put(t: MutList[a, r], i: Int32, v: a): Unit \ r + OutOfBounds =
        MutList.put(v, i, t)
}

instance MutCollectable[MutList[a, r]] {
    type Elm = a
    type Aef = r
    type Reg = r
    pub def collect(rc: Region[r], iter: Iterator[a, ef, r1]): MutList[a, r] \ (ef + r + r1) =
        Iterator.toMutList(rc, iter)

}

mod MutList {

    ///
    /// Constant which stores the minimum capacity of a MutList.
    ///
    @Internal
    pub def minCapacity(): Int32 = 8

    ///
    /// Returns a string representation of the given MutList `l`.
    ///
    pub def toString(l: MutList[a, r]): String \ r with ToString[a] = region rc {
        "MutList#{" + (MutList.iterator(rc, l) |> Iterator.join(", ")) + "}"
    }

    ///
    /// Returns an empty mutable list with a default capacity.
    ///
    pub def empty(rc: Region[r]): MutList[a, r] \ r =
        emptyWithCapacity(rc, minCapacity())

    ///
    /// Returns an empty mutable list with the given capacity rounded up to the
    /// default capacity.
    ///
    pub def emptyWithCapacity(rc: Region[r], capacity: Int32): MutList[a, r] \ r = {
        let flooredCapacity = Int32.max(capacity, minCapacity());
        new MutList @ rc {r = rc, values = Array.empty(rc, flooredCapacity), length = 0}
    }

    ///
    /// Returns a mutable list of all integers between `b` (inclusive) and `e` (exclusive).
    ///
    /// Returns an empty mutable list if `b >= e`.
    ///
    pub def range(rc: Region[r], b: Int32, e: Int32): MutList[Int32, r] \ r =
        let minCap = minCapacity();
        let d = e - b;
        let c = Order.max(d, minCap);
        let f = i -> { let x = b + i; if (x < e) x else Reflect.default() };
        new MutList @ rc {r = rc, values = Array.init(rc, f, c), length = d}

    ///
    /// Retrieves the value at position `i` in the mutable list `v`.
    ///
    pub def get(i: Int32, v: MutList[a, r]): a \ r + OutOfBounds =
        if (0 <= i and i < v->length)
            Array.get(i, v->values)
        else
            OutOfBounds.outOfBounds("index ${i} is out of bounds for MutList of length ${v->length}")

    ///
    /// Stores the value `x` at position `i` in the mutable list `v`.
    ///
    pub def put(x: a, i: Int32, v: MutList[a, r]): Unit \ r + OutOfBounds =
        if (0 <= i and i < v->length)
            Array.put(x, i, v->values)
        else
            OutOfBounds.outOfBounds("index ${i} is out of bounds for MutList of length ${v->length}")

    ///
    /// Optionally returns the element at position `i` in the mutable list `v`.
    ///
    pub def nth(i: Int32, v: MutList[a, r]): Option[a] \ r =
        if (0 <= i and i < v->length)
            Array.nth(i, v->values)
        else
            None

    ///
    /// Returns the number of elements in the given mutable list `v`.
    ///
    pub def length(v: MutList[a, r]): Int32 \ r =
        v->length

    ///
    /// Returns the number of elements in the given mutable list `v`.
    ///
    pub def size(v: MutList[a, r]): Int32 \ r = v->length

    ///
    /// Returns `true` if the given mutable list `v` is empty.
    ///
    pub def isEmpty(v: MutList[a, r]): Bool \ r =
        v->length == 0

    ///
    /// Returns `true` if the given mutable list `v` is non-empty.
    ///
    pub def nonEmpty(v: MutList[a, r]): Bool \ r = not isEmpty(v)

    ///
    /// Returns `true` if the given element `x` is a member of the given mutable list `v`.
    ///
    pub def memberOf(x: a, v: MutList[a, r]): Bool \ r with Eq[a] =
        exists(y -> y == x, v)

    ///
    /// Optionally finds the smallest element of `v` according to the `Order` on `a`.
    ///
    /// Returns `None` if `v` is empty.
    ///
    pub def minimum(v: MutList[a, r]): Option[a] \ r with Order[a] =
        reduceLeft(Order.min, v)

    ///
    /// Optionally finds the smallest element of `v` according to the given comparator `cmp`.
    ///
    /// Returns `None` if `v` is empty.
    ///
    pub def minimumBy(cmp: (a, a) -> Comparison, v: MutList[a, r]): Option[a] \ r =
        reduceLeft(Order.minBy(cmp), v)

    ///
    /// Optionally finds the largest element of `v` according to the `Order` on `a`.
    ///
    /// Returns `None` if `v` is empty.
    ///
    pub def maximum(v: MutList[a, r]): Option[a] \ r with Order[a] =
        reduceLeft(Order.max, v)

    ///
    /// Optionally finds the largest element of `v` according to the given comparator `cmp`.
    ///
    /// Returns `None` if `v` is empty.
    ///
    pub def maximumBy(cmp: (a, a) -> Comparison, v: MutList[a, r]): Option[a] \ r =
        reduceLeft(Order.maxBy(cmp), v)

    ///
    /// Returns the number of elements in the given mutable list `v` that satisfies the given predicate `f`.
    ///
    /// Returns `0` if the given mutable list `v` is empty.
    ///
    pub def count(f: a -> Bool \ ef, v: MutList[a, r]): Int32 \ { ef, r } =
        foldLeft((acc, x) -> if (f(x)) acc + 1 else acc, 0, v)

    ///
    /// Returns the sum of all elements in the MutList `v`.
    ///
    pub def sum(v: MutList[Int32, r]): Int32 \ r =
        foldLeft((acc, x) -> acc + x, 0, v)

    ///
    /// Returns the sum of all elements in the MutList `v` according to the function `f`.
    ///
    pub def sumWith(f: a -> Int32 \ ef, v: MutList[a, r]): Int32 \ { ef, r } =
        foldLeft((acc, x) -> acc + f(x), 0, v)

    ///
    /// Returns `true` if the given predicate `f` holds for at least one element of the given mutable list `v`.
    ///
    /// Returns `false` if the given mutable list `v` is empty.
    ///
    pub def exists(f: a -> Bool \ ef, v: MutList[a, r]): Bool \ { ef, r } =
        def loop(i) = {
            if (i >= v->length)
                false
            else
                if (f(Array.get(i, v->values))) true else loop(i + 1)
        };
        loop(0)

    ///
    /// Returns `true` if the given predicate `f` holds for all elements of the given mutable list `v`.
    ///
    /// Returns `true` if the given mutable list `v` is empty.
    ///
    pub def forAll(f: a -> Bool \ ef, v: MutList[a, r]): Bool \ { ef, r } =
        def loop(i) = {
            if (i >= v->length)
                true
            else
                if (f(Array.get(i, v->values))) loop(i + 1) else false
        };
        loop(0)

    ///
    /// Optionally returns the first element of the given mutable list `v`.
    ///
    /// Returns `None` if the given mutable list `v` is empty.
    ///
    pub def head(v: MutList[a, r]): Option[a] \ r =
        if (isEmpty(v))
            None
        else
            Array.head(v->values)

    ///
    /// Optionally returns the last element of the given mutable list `v`.
    ///
    /// Returns `None` if the given mutable list `v` is empty.
    ///
    pub def last(v: MutList[a, r]): Option[a] \ r =
        if (v->length > 0) Some(Array.get(v->length - 1, v->values)) else None

    ///
    /// Alias for `IndexOfLeft`
    ///
    pub def indexOf(x: a, v: MutList[a, r]): Option[Int32] \ r with Eq[a] =
        indexOfLeft(x, v)

    ///
    /// Optionally returns the position of the first occurrence of `x` in `v`
    /// searching from left to right.
    ///
    pub def indexOfLeft(x: a, v: MutList[a, r]): Option[Int32] \ r with Eq[a] =
        def loop(i) = {
            if (i >= v->length)
                None
            else
                if (x == Array.get(i, v->values)) Some(i) else loop(i + 1)
        };
        loop(0)

    ///
    /// Optionally returns the position of the first occurrence of `x` in `v`
    /// searching from right to left.
    ///
    pub def indexOfRight(x: a, v: MutList[a, r]): Option[Int32] \ r with Eq[a] =
        def loop(i) = {
            if (i < 0)
                None
            else
                if (x == Array.get(i, v->values)) Some(i) else loop(i - 1)
        };
        loop(v->length - 1)

    ///
    /// Alias for `findLeft`.
    ///
    pub def find(f: a -> Bool, v: MutList[a, r]): Option[a] \ r =
        findLeft(f, v)

    ///
    /// Optionally returns the left-most element in the given mutable list `v` that satisfies the given predicate `f`.
    ///
    /// Returns `None` if no element satisfies the given predicate `f`.
    /// Returns `None` if the given mutable list `v` is empty.
    ///
    pub def findLeft(f: a -> Bool, v: MutList[a, r]): Option[a] \ r =
        def loop(i) = {
            if (i >= v->length)
                None
            else {
                let val = Array.get(i, v->values);
                if (f(val)) Some(val) else loop(i + 1)
            }
        };
        loop(0)

    ///
    /// Optionally returns the right-most element in the given mutable list `v` that satisfies the given predicate `f`.
    ///
    /// Returns `None` if no element satisfies the given predicate `f`.
    /// Returns `None` if the given mutable list `v` is empty.
    ///
    pub def findRight(f: a -> Bool, v: MutList[a, r]): Option[a] \ r =
        def loop(i) = {
            if (i < 0)
                None
            else {
                let val = Array.get(i, v->values);
                if (f(val)) Some(val) else loop(i - 1)
            }
        };
        loop(v->length - 1)

    ///
    /// Alias for `scanLeft`.
    ///
    pub def scan(rc1: Region[r1], f: (b, a) -> b \ ef, s: b, v: MutList[a, r2]): MutList[b, r1] \ { ef, r2, r1 } =
        scanLeft(rc1, f, s, v)

    ///
    /// Accumulates the result of applying `f` to `v` going left to right.
    ///
    pub def scanLeft(rc1: Region[r1], f: (b, a) -> b \ ef, s: b, v: MutList[a, r2]): MutList[b, r1] \ { ef, r2, r1 } =
        let n = v->length + 1;
        let b = Array.repeat(rc1, n, s);
        def loop(i, acc) = {
            if (i >= n)
                ()
            else {
                let s1 = f(acc, Array.get(i - 1, v->values));
                Array.put(s1, i, b);
                loop(i + 1, s1)
            }
        };
        loop(1, s);
        new MutList @ rc1 {r = rc1, values = b, length = n}

    ///
    /// Accumulates the result of applying `f` to `v` going right to left.
    ///
    pub def scanRight(rc1: Region[r1], f: (a, b) -> b \ ef, s: b, v: MutList[a, r2]): MutList[b, r1] \ { ef, r2, r1 } =
        let n = v->length + 1;
        let b = Array.repeat(rc1, n, s);
        def loop(i, acc) = {
            if (i < 0)
                ()
            else {
                let s1 = f(Array.get(i, v->values), acc);
                Array.put(s1, i, b);
                loop(i - 1, s1)
            }
        };
        loop(v->length - 1, s);
        new MutList @ rc1 {r = rc1, values = b, length = n}

    ///
    /// Apply `f` to every element in `v`.
    ///
    /// The result is an empty mutable list.
    ///
    pub def map(rc1: Region[r1], f: a -> b \ ef, v: MutList[a, r]): MutList[b, r1] \ { ef, r, r1 } =
        if (isEmpty(v))
            MutList.empty(rc1)
        else {
            let x = f(Array.get(0, v->values));
            let b = Array.repeat(rc1, Array.length(v->values), x);
            def loop(i) = {
                if (i >= v->length)
                    ()
                else {
                    Array.put(f(Array.get(i, v->values)), i, b);
                    loop(i + 1)
                }
            };
            loop(1);
            new MutList @ rc1 {r = rc1, values = b, length = v->length}
        }

    ///
    /// Concatenates all the contained MutLists.
    ///
    pub def flatten(rc1: Region[r1], v: MutList[MutList[a, r], r]): MutList[a, r1] \ {r, r1}=
        let rdestIndex = Ref.fresh(rc1, 0);
        let size = MutList.sumWith(MutList.length, v);
        let destArray = Array.empty(rc1, Int32.max(size, minCapacity()));
        v |> MutList.forEach(bs -> {
            let destIndex = Ref.get(rdestIndex);
            Array.patch(destIndex, length(bs), bs->values, destArray);
            Ref.put(destIndex + length(bs), rdestIndex)
        });
        new MutList @ rc1 {r = rc1, values = destArray, length = size}


    ///
    /// Apply `f` to every element in `v` and concatenate the results.
    ///
    /// The result is a new mutable list.
    ///
    pub def flatMap(rc1: Region[r1], f: a -> MutList[b, r1] \ ef, v: MutList[a, r]): MutList[b, r1] \ { ef, r, r1 } =
        map(rc1, f, v) |> flatten(rc1)

    ///
    /// Returns the result of applying `f` to every element in `v` along with that element's index.
    ///
    pub def mapWithIndex(rc1: Region[r1], f: (Int32, a) -> b \ ef, v: MutList[a, r]): MutList[b, r1] \ { ef, r, r1 } =
        if (isEmpty(v))
            MutList.empty(rc1)
        else {
            let x = f(0, Array.get(0, v->values));
            let b = Array.repeat(rc1, Array.length(v->values), x);
            def loop(i) = {
                if (i >= v->length)
                    ()
                else {
                    Array.put(f(i, Array.get(i, v->values)), i, b);
                    loop(i + 1)
                }
            };
            loop(1);
            new MutList @ rc1 {r = rc1, values = b, length = v->length}
        }

    ///
    /// Apply `f` to every element in `v`.
    ///
    pub def transform(f: a -> a, v: MutList[a, r]): Unit \ r =
        def loop(i) = {
            if (i >= v->length)
                ()
            else {
                Array.put(f(Array.get(i, v->values)), i, v->values);
                loop(i + 1)
            }
        };
        loop(0)

    ///
    /// Apply `f` to every element in `v` along with that element's index.
    ///
    pub def transformWithIndex(f: (Int32, a) -> a, v: MutList[a, r]): Unit \ r =
        def loop(i) = {
            if (i >= v->length)
                ()
            else {
                Array.put(f(i, Array.get(i, v->values)), i, v->values);
                loop(i + 1)
            }
        };
        loop(0)

    ///
    /// Applies `f` to a start value `s` and all elements in `a` going from left to right.
    ///
    /// That is, the result is of the form: `f(...f(f(s, a[0]), a[1])..., xn)`.
    ///
    pub def foldLeft(f: (b, a) -> b \ ef, s: b, v: MutList[a, r]): b \ { ef, r } =
        def loop(i, acc) = {
            if (i >= v->length)
                acc
            else {
                let s1 = f(acc, Array.get(i, v->values));
                loop(i + 1, s1)
            }
        };
        loop(0, s)

    ///
    /// Applies `f` to a start value `s` and all elements in `a` going from left to right.
    ///
    /// That is, the result is of the form: `f(...f(f(s, a[0]), a[1])..., xn)`.
    ///
    /// The implementation is tail recursive.
    ///
    pub def foldRight(f: (a, b) -> b \ ef, s: b, v: MutList[a, r]): b \ { ef, r } =
        def loop(i, acc) = {
            if (i < 0)
                acc
            else {
                let s1 = f(Array.get(i, v->values), acc);
                loop(i - 1, s1)
            }
        };
        loop(v->length - 1, s)

    ///
    /// Applies `f` to a start value `z` and all elements in `a` going from left to right.
    ///
    /// That is, the result is of the form: `f(x1, ...f(xn-1, f(xn, z))...)`.
    /// A `foldRightWithCont` allows early termination by not calling the continuation.
    ///
    pub def foldRightWithCont(f: (a, Unit -> b \ {ef, r}) -> b \ {ef, r}, z: b, v: MutList[a, r]): b \ { ef, r } =
        def loop(i) = {
            if (i >= v->length)
                z
            else {
                f(Array.get(i, v->values), _ -> loop(i + 1))
            }
        };
        loop(0)

    ///
    /// Returns the result of mapping each element and combining the results.
    ///
    pub def foldMap(f: a -> b \ ef, v: MutList[a, r]): b \ {ef, r} with Monoid[b] =
        foldLeft((acc, x) -> Monoid.combine(acc, f(x)), Monoid.empty(), v)

    ///
    /// Applies `f` to all elements in `v` going from left to right until a single value `v` is obtained. Returns `Some(v)`.
    ///
    /// Returns `None` if `v` is empty.
    ///
    pub def reduceLeft(f: (a, a) -> a \ ef, v: MutList[a, r]): Option[a] \ { ef, r } =
        foldLeft((acc, x) -> match acc {
            case Some(y) => Some(f(y, x))
            case None => Some(x)
        }, None, v)

    ///
    /// Applies `f` to all elements in `v` going from right to left until a single value `v` is obtained. Returns `Some(v)`.
    ///
    /// Returns `None` if `v` is empty.
    ///
    pub def reduceRight(f: (a, a) -> a \ ef, v: MutList[a, r]): Option[a] \ { ef, r } =
        foldRight((x, acc) -> match acc {
            case Some(y) => Some(f(x, y))
            case None => Some(x)
        }, None, v)

    ///
    /// Removes all elements from the given mutable list `v`.
    ///
    pub def clear(v: MutList[a, r]): Unit \ r =
        v->values = Array.empty(v->r, Array.length(v->values));
        v->length = 0;
        ()

    ///
    /// Returns a shallow copy of the given mutable list `v`.
    /// The capacity of the copy is equal to the length of the list.
    ///
    pub def copy(rc1: Region[r1], v: MutList[a, r]): MutList[a, r1] \ { r, r1 } =
        if (v->length > minCapacity())
            new MutList @ rc1 {r = rc1, values = Array.copyOfRange(rc1, 0, v->length, v->values), length = v->length}
        else
            new MutList @ rc1 {r = rc1, values = Array.copyOfRange(rc1, 0, capacity(v), v->values), length = v->length}

    ///
    /// Optionally removes and returns the last element in the given mutable list `v`.
    ///
    pub def pop(v: MutList[a, r]): Option[a] \ r =
        let len = v->length;
        if (len > 0)
            let last = Array.get(len - 1, v->values);
            v->length = len - 1;
            Array.put(Reflect.default(), len - 1, v->values);
            compress(v);
            Some(last)
        else
            None

    ///
    /// Inserts the given element `x` at the end of the given mutable list `v`.
    ///
    pub def push(x: a, v: MutList[a, r]): Unit \ r =
        if (capacity(v) - v->length == 0)
            reserve(v->length, v)
        else ();
        Array.put(x, v->length, v->values);
        v->length = v->length + 1

    ///
    /// Inserts the given element `x` at the given position `i` in the given mutable list `v`.
    ///
    /// Shifts elements as necessary. Possibly expensive operation.
    ///
    /// If the given index `i` exceeds the length of the mutable list, the element is inserted at the last position.
    ///
    pub def insert(x: a, i: Int32, v: MutList[a, r]): Unit \ r =
        if (capacity(v) - v->length == 0)
            reserve(v->length, v)
        else ();
        let sub = Array.copyOfRange(v->r, i, v->length, v->values);
        Array.updateSequence(i + 1, sub, v->values);
        Array.put(x, i, v->values);
        v->length = v->length + 1

    ///
    /// Removes the element at the given position `i` in the given mutable list `v`.
    ///
    /// Shifts elements as necessary. Possibly expensive operation.
    ///
    /// If the given index `i` exceeds the length of the mutable list, no element is removed.
    ///
    pub def remove(i: Int32, v: MutList[a, r]): Unit \ r =
        let n = v->length - 1;
        def loop(i1) = {
            if (i1 < n) {
                Array.put(Array.get(i1 + 1, v->values), i1, v->values);
                loop(i1 + 1)
            }
            else if (i1 == n) {
                Array.put(Reflect.default(), i1, v->values)
            }
            else
                ()
        };
        if (i < v->length) {
            loop(i);
            v->length = n;
            compress(v)
        }
        else
            ()

    ///
    /// Appends `m` to `v` i.e. inserts all elements from `m` into the end of `v`.
    ///
    pub def pushAll(m: m[a], v: MutList[a, r]): Unit \ (r + Foldable.Aef[m]) with Foldable[m] =
        Foldable.forEach(x -> MutList.push(x, v), m)

    ///
    /// Appends `m` to `v` i.e. inserts all elements from `m` into the end of `v`.
    ///
    pub def append(m: m[a], v: MutList[a, r]): Unit \ (r + Foldable.Aef[m]) with Foldable[m] =
        pushAll(m, v)

    ///
    /// Removes all elements from the given mutable list `v` that do not satisfy the given predicate `f`.
    ///
    pub def retain(f: a -> Bool, v: MutList[a, r]): Unit \ r =
        let l = MutList.empty(v->r);
        forEach(e -> if (f(e)) push(e, l) else (), v);
        v->values = l->values;
        v->length = length(l);
        ()

    ///
    /// Replaces all occurrences of the `src` with `dst` in the given mutable list `v`.
    ///
    pub def replace(src: {src = a}, dst: {dst = a}, v: MutList[a, r]): Unit \ r with Eq[a] =
        transform(e -> if (e == src#src) dst#dst else e, v)

    ///
    /// Reverses the order of the elements in the given mutable list `v`.
    ///
    pub def reverse(v: MutList[a, r]): Unit \ r =
        let halflen = v->length / 2;
        def loop(i, j) = {
            if (i >= halflen)
                ()
            else {
                let x = Array.get(i, v->values);
                let y = Array.get(j, v->values);
                Array.put(y, i, v->values);
                Array.put(x, j, v->values);
                loop(i + 1, j - 1)
            }
        };
        loop(0, v->length - 1)

    ///
    /// Shrinks the given mutable list `v` down to a capacity of `n` elements but no less than 8.
    ///
    /// Truncates the mutable list as needed.
    ///
    def shrinkTo(n: Int32, v: MutList[a, r]): Unit \ r =
        let minCap = minCapacity();
        let capv = capacity(v);
        if (n < capv and capv != minCap) {
            let newCap = Order.max(n, minCap);
            v->values = Array.copyOfRange(v->r, 0, newCap, v->values);
            v->length = Order.min(v->length, newCap)
        }
        else
            ()

    ///
    /// Shrinks the given mutable list `v` to its actual size.
    ///
    pub def shrink(v: MutList[a, r]): Unit \ r =
        shrinkTo(v->length, v)

    ///
    /// Truncates the given mutable list `v` to the given length `l`.
    ///
    /// That is, after the operation, the mutable list has length at most `l`.
    ///
    /// If the given length `l` is negative, all elements are removed.
    ///
    pub def truncate(l: Int32, v: MutList[a, r]): Unit \ r =
        if (l < 0)
            clear(v)
        else if (l < v->length) {
            let minCap = minCapacity();
            let c = Order.max(l, minCap);
            v->length = l;
            Array.updateSequence(0, v->values, Array.empty(v->r, c))
        }
        else
            ()

    ///
    /// Increases the capacity of the given mutable list `v` by at least `n`.
    ///
    /// That is, after the call, the mutable list is guaranteed to have space for at least `n` additional elements.
    ///
    /// The content of the mutable list is unchanged.
    ///
    pub def reserve(n: Int32, v: MutList[a, r]): Unit \ r =
        v->values = Array.copyOfRange(v->r, 0, v->length + n, v->values)

    ///
    /// Returns `v` as an immutable list.
    ///
    pub def toList(v: MutList[a, r]): List[a] \ r =
        foldRight((x, acc) -> x :: acc, Nil, v)

    ///
    /// Returns `v` as an array.
    ///
    pub def toArray(rc1: Region[r1], v: MutList[a, r2]): Array[a, r1] \ { r2, r1 } =
        Array.copyOfRange(rc1, 0, v->length, v->values)

    ///
    /// Returns `xs` as a vector.
    ///
    pub def toVector(xs: MutList[a, r]): Vector[a] \ r = region rc {
        let arr = Array.empty(rc, length(xs));
        forEachWithIndex((i, x) -> Array.put(x, i, arr), xs);
        Array.toVector(arr)
    }

    ///
    /// Returns the mutable list `xs` as a chain.
    ///
    pub def toChain(xs: MutList[a, r]): Chain[a] \ r =
        foldLeft((ac, x) -> Chain.snoc(ac, x), Chain.empty(), xs)

    ///
    /// Returns `v` as a MutDeque.
    ///
    pub def toMutDeque(rc1: Region[r1], v: MutList[a, r2]): MutDeque[a, r1] \ { r2, r1 } =
        let d = MutDeque.empty(rc1);
        forEach(x -> MutDeque.pushBack(x, d), v);
        d

    ///
    /// Returns `true` if the mutable lists `v1` and `v2` have the same elements in the same order, i.e. are structurally equal.
    ///
    pub def sameElements(v1: MutList[a, r1], v2: MutList[a, r2]): Bool \ { r1, r2 } with Eq[a] =
        def loop(i) = {
            if (i >= length(v1))
                true
            else if (Array.get(i, v1->values) == Array.get(i, v2->values))
                loop(i + 1)
            else
                false
        };
        if (length(v1) == length(v2)) loop(0) else false

    ///
    /// Returns the concatenation of the string representation
    /// of each element in `v` with `sep` inserted between each element.
    ///
    pub def join(sep: String, v: MutList[a, r]): String \ r with ToString[a] = region rc {
        MutList.iterator(rc, v) |> Iterator.join(sep)
    }

    ///
    /// Returns the concatenation of the string representation
    /// of each element in `v` according to `f` with `sep` inserted between each element.
    ///
    pub def joinWith(f: a -> String \ ef, sep: String, v: MutList[a, r]): String \ { ef, r } = region rc {
        MutList.iterator(rc, v) |> Iterator.joinWith(f, sep)
    }

    ///
    /// Returns an iterator over `l`.
    ///
    /// Modifying `l` while using an iterator has undefined behavior and is dangerous.
    ///
    pub def iterator(rc: Region[r1], l: MutList[a, r2]): Iterator[a, r1 + r2, r1] \ { r1, r2 } =
        let ix = Ref.fresh(rc, 0);
        let len = length(l);
        let next = () -> {
            let i = Ref.get(ix);
            if (i < len) {
                let x = Array.get(i, l->values);
                Ref.put(i + 1, ix);
                Some(x)
            } else {
                None
            }
        };
        Iterator.iterate(rc, next)

    ///
    /// Applies `f` to all the elements in `v`.
    ///
    pub def forEach(f: a -> Unit \ ef, v: MutList[a, r]): Unit \ { ef, r } =
        def loop(i) = {
            if (i >= v->length)
                ()
            else {
                f(Array.get(i, v->values));
                loop(i + 1)
            }
        };
        loop(0)

    ///
    /// Applies `f` to all the elements in `v` along with that element's index.
    ///
    pub def forEachWithIndex(f: (Int32, a) -> Unit \ ef, v: MutList[a, r]): Unit \ { ef, r } =
        def loop(i) = {
            if (i >= v->length)
                ()
            else {
                f(i, Array.get(i, v->values));
                loop(i + 1)
            }
        };
        loop(0)

    ///
    /// Compresses the given mutable list `v` if needed.
    ///
    /// The mutable list will be shrunk to 1/2 of its size if the load factor is less than 1/4.
    ///
    pub def compress(v: MutList[a, r]): Unit \ r =
        let c = capacity(v);
        let len = v->length;
        let loadFactor = Int32.toFloat32(len) / Int32.toFloat32(c);
        if (loadFactor < 1.0f32/4.0f32 and len > 0) {
            if (len == 1)
                shrinkTo(1, v)
            else
                shrinkTo(c / 2, v)
        }
        else
            ()

    ///
    /// Returns the capacity of `v`.
    ///
    def capacity(v: MutList[a, r]): Int32 \ r =
        Array.length(v->values)

    ///
    /// Sort MutList `v` so that elements are ordered from low to high according to their `Order` instance.
    /// The MutList is mutated in-place.
    ///
    /// The sort is not stable, i.e., equal elements may appear in a different order than in the input `v`.
    ///
    /// The sort implementation is a Quicksort.
    ///
    pub def sort(v: MutList[a, r]): Unit \ r with Order[a] =
        sortWith(Order.compare, v)

    ///
    /// Sort MutList `v` so that elements are ordered from low to high according to the `Order` instance for
    /// the values obtained by applying `f` to each element. The MutList is mutated in-place.
    ///
    /// The sort is not stable, i.e., equal elements may appear in a different order than in the input `v`.
    ///
    /// The sort implementation is a Quicksort.
    ///
    pub def sortBy(f: a -> b, v: MutList[a, r]): Unit \ r with Order[b] =
        sortWith(Order.compare `on` f, v)

    ///
    /// Sort MutList `v` so that elements are ordered from low to high according to the comparison function `cmp`.
    /// The MutList is mutated in-place.
    ///
    /// The sort is not stable, i.e., equal elements may appear in a different order than in the input `v`.
    ///
    /// The sort implementation is a Quicksort.
    ///
    pub def sortWith(cmp: (a,a) -> Comparison, v: MutList[a, r]): Unit \ r =
        Array.sortWithin(cmp, 0, v->length - 1, v->values)

    ///
    /// Shuffles `v` using the Fisher–Yates shuffle.
    ///
    pub def shuffle(rc1: Region[r1], v: MutList[a, r1]): MutList[a, r1] \ { r1, NonDet } = region rc2 {
        toArray(rc2, v) !> Array.shuffle |> Array.toMutList(rc1)
    }

}
