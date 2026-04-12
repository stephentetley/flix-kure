/*
 * Copyright 2026 Stephen Tetley
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


mod KIR.Congruence {

    use KIR.Base.{Transform, Rewrite}
    use KIR.Base.{transform, rewrite, applyR, applyT}

    // Ugh ... In Haskell the machinery for AnyR amd OneR changes the monad but we have fixed it to Answer

    ///////////////////////////////////////////////////////////////////////////
    // AnyR


    def anyRewriteStep(r: Rewrite[cx, a]): Transform[cx, a, (Bool, a)] = 
        transform((cx, a) -> 
            match applyR(r, cx, a) {
                case Ok(a1) => Ok((true, a1))
                case Err(_) => Ok((false, a))
            }
        )


    // At least one success - try all
    pub def makeAnyR2(r1: Rewrite[cx, a], r2: Rewrite[cx, b]): Rewrite[cx, (a, b)] = 
        rewrite((cx, ab) -> 
            let (a, b) = ab;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b)
            ) yield (s1 or s2, a1, b1);
            match ans {
                case Ok((true, a1, b1)) => Ok((a1, b1))
                case _                  => Err("anyR2 failed")
            }
        )

    // At least one success - try all
    pub def makeAnyR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c]): Rewrite[cx, (a, b, c)] = 
        rewrite((cx, abc) -> 
            let (a, b, c) = abc;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b);
                (s3, c1) <- applyT(anyRewriteStep(r3), cx, c)
            ) yield (s1 or s2 or s3, a1, b1, c1);
            match ans {
                case Ok((true, a1, b1, c1)) => Ok((a1, b1, c1))
                case _                      => Err("anyR3 failed")
            }
        )
    
    pub def makeAnyR4(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d]): Rewrite[cx, (a, b, c, d)] = 
        rewrite((cx, abcd) -> 
            let (a, b, c, d) = abcd;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b);
                (s3, c1) <- applyT(anyRewriteStep(r3), cx, c);
                (s4, d1) <- applyT(anyRewriteStep(r4), cx, d)
            ) yield (s1 or s2 or s3 or s4, a1, b1, c1, d1);
            match ans {
                case Ok((true, a1, b1, c1, d1)) => Ok((a1, b1, c1, d1))
                case _                          => Err("anyR4 failed")
            }
        )

    pub def makeAnyR5(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d], 
                        r5: Rewrite[cx, e]): Rewrite[cx, (a, b, c, d, e)] = 
        rewrite((cx, abcde) -> 
            let (a, b, c, d, e) = abcde;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b);
                (s3, c1) <- applyT(anyRewriteStep(r3), cx, c);
                (s4, d1) <- applyT(anyRewriteStep(r4), cx, d);
                (s5, e1) <- applyT(anyRewriteStep(r5), cx, e)
            ) yield (s1 or s2 or s3 or s4 or s5, a1, b1, c1, d1, e1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1)) => Ok((a1, b1, c1, d1, e1))
                case _                              => Err("anyR5 failed")
            }
        )

    pub def makeAnyR6(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d], 
                        r5: Rewrite[cx, e], r6: Rewrite[cx, f]): Rewrite[cx, (a, b, c, d, e, f)] = 
        rewrite((cx, abcdef) -> 
            let (a, b, c, d, e, f) = abcdef;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b);
                (s3, c1) <- applyT(anyRewriteStep(r3), cx, c);
                (s4, d1) <- applyT(anyRewriteStep(r4), cx, d);
                (s5, e1) <- applyT(anyRewriteStep(r5), cx, e);
                (s6, f1) <- applyT(anyRewriteStep(r6), cx, f)
            ) yield (s1 or s2 or s3 or s4 or s5 or s6, a1, b1, c1, d1, e1, f1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1, f1)) => Ok((a1, b1, c1, d1, e1, f1))
                case _                              => Err("anyR6 failed")
            }
        )

    pub def makeAnyR7(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d], 
                        r5: Rewrite[cx, e], r6: Rewrite[cx, f],
                        r7: Rewrite[cx, g]): Rewrite[cx, (a, b, c, d, e, f, g)] = 
        rewrite((cx, abcdefg) -> 
            let (a, b, c, d, e, f, g) = abcdefg;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b);
                (s3, c1) <- applyT(anyRewriteStep(r3), cx, c);
                (s4, d1) <- applyT(anyRewriteStep(r4), cx, d);
                (s5, e1) <- applyT(anyRewriteStep(r5), cx, e);
                (s6, f1) <- applyT(anyRewriteStep(r6), cx, f);
                (s7, g1) <- applyT(anyRewriteStep(r7), cx, g)
            ) yield (s1 or s2 or s3 or s4 or s5 or s6 or s7, a1, b1, c1, d1, e1, f1, g1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1, f1, g1)) => Ok((a1, b1, c1, d1, e1, f1, g1))
                case _                                      => Err("anyR7 failed")
            }
        )

    pub def makeAnyR8(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d], 
                        r5: Rewrite[cx, e], r6: Rewrite[cx, f],
                        r7: Rewrite[cx, g], r8: Rewrite[cx, h]): Rewrite[cx, (a, b, c, d, e, f, g, h)] = 
        rewrite((cx, abcdefgh) -> 
            let (a, b, c, d, e, f, g, h) = abcdefgh;
            let ans = forM (
                (s1, a1) <- applyT(anyRewriteStep(r1), cx, a);
                (s2, b1) <- applyT(anyRewriteStep(r2), cx, b);
                (s3, c1) <- applyT(anyRewriteStep(r3), cx, c);
                (s4, d1) <- applyT(anyRewriteStep(r4), cx, d);
                (s5, e1) <- applyT(anyRewriteStep(r5), cx, e);
                (s6, f1) <- applyT(anyRewriteStep(r6), cx, f);
                (s7, g1) <- applyT(anyRewriteStep(r7), cx, g);
                (s8, h1) <- applyT(anyRewriteStep(r8), cx, h)
            ) yield (s1 or s2 or s3 or s4 or s5 or s6 or s7 or s8, a1, b1, c1, d1, e1, f1, g1, h1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1, f1, g1, h1)) => Ok((a1, b1, c1, d1, e1, f1, g1, h1))
                case _                                          => Err("anyR8 failed")
            }
        )



    ///////////////////////////////////////////////////////////////////////////
    // OneR

    def oneRewriteStep(b: Bool, r: Rewrite[cx, a]): Transform[cx, a, (Bool, a)] = 
        transform((cx, a) -> 
            if (b) 
                Ok((true, a))
            else {
                match applyR(r, cx, a) {
                    case Ok(a1) => Ok((true, a1))
                    case Err(_) => Ok((false, a))
                }
            }
        )


    pub def makeOneR2(r1: Rewrite[cx, a], r2: Rewrite[cx, b]): Rewrite[cx, (a, b)] = 
        rewrite((cx, ab) -> 
            let (a, b) = ab;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b)
            ) yield (s2, a1, b1);
            match ans {
                case Ok((true, a1, b1)) => Ok((a1, b1))
                case _                  => Err("oneR2 failed")
            }
        )





    pub def makeOneR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c]): Rewrite[cx, (a, b, c)] = 
        rewrite((cx, abc) -> 
            let (a, b, c) = abc;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b);
                (s3, c1) <- applyT(oneRewriteStep(s2, r3), cx, c)
            ) yield (s3, a1, b1, c1);
            match ans {
                case Ok((true, a1, b1, c1)) => Ok((a1, b1, c1))
                case _                      => Err("oneR3 failed")
            }
        )

    pub def makeOneR4(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d]): Rewrite[cx, (a, b, c, d)] = 
        rewrite((cx, abcd) -> 
            let (a, b, c, d) = abcd;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b);
                (s3, c1) <- applyT(oneRewriteStep(s2, r3), cx, c);
                (s4, d1) <- applyT(oneRewriteStep(s3, r4), cx, d)
            ) yield (s4, a1, b1, c1, d1);
            match ans {
                case Ok((true, a1, b1, c1, d1)) => Ok((a1, b1, c1, d1))
                case _                      => Err("oneR4 failed")
            }
        )

    pub def makeOneR5(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                        r5: Rewrite[cx, e]): Rewrite[cx, (a, b, c, d, e)] = 
        rewrite((cx, abcde) -> 
            let (a, b, c, d, e) = abcde;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b);
                (s3, c1) <- applyT(oneRewriteStep(s2, r3), cx, c);
                (s4, d1) <- applyT(oneRewriteStep(s3, r4), cx, d);
                (s5, e1) <- applyT(oneRewriteStep(s4, r5), cx, e)
            ) yield (s5, a1, b1, c1, d1, e1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1)) => Ok((a1, b1, c1, d1, e1))
                case _                      => Err("oneR5 failed")
            }
        )

    pub def makeOneR6(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                        r5: Rewrite[cx, e], r6: Rewrite[cx, f]): Rewrite[cx, (a, b, c, d, e, f)] = 
        rewrite((cx, abcdef) -> 
            let (a, b, c, d, e, f) = abcdef;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b);
                (s3, c1) <- applyT(oneRewriteStep(s2, r3), cx, c);
                (s4, d1) <- applyT(oneRewriteStep(s3, r4), cx, d);
                (s5, e1) <- applyT(oneRewriteStep(s4, r5), cx, e);
                (s6, f1) <- applyT(oneRewriteStep(s5, r6), cx, f)
            ) yield (s6, a1, b1, c1, d1, e1, f1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1, f1)) => Ok((a1, b1, c1, d1, e1, f1))
                case _                                  => Err("oneR6 failed")
            }
        )

    pub def makeOneR7(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                        r5: Rewrite[cx, e], r6: Rewrite[cx, f],
                        r7: Rewrite[cx, g]): Rewrite[cx, (a, b, c, d, e, f, g)] = 
        rewrite((cx, abcdefg) -> 
            let (a, b, c, d, e, f, g) = abcdefg;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b);
                (s3, c1) <- applyT(oneRewriteStep(s2, r3), cx, c);
                (s4, d1) <- applyT(oneRewriteStep(s3, r4), cx, d);
                (s5, e1) <- applyT(oneRewriteStep(s4, r5), cx, e);
                (s6, f1) <- applyT(oneRewriteStep(s5, r6), cx, f);
                (s7, g1) <- applyT(oneRewriteStep(s6, r7), cx, g)
            ) yield (s7, a1, b1, c1, d1, e1, f1, g1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1, f1, g1)) => Ok((a1, b1, c1, d1, e1, f1, g1))
                case _                                      => Err("oneR7 failed")
            }
        )

    pub def makeOneR8(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
                        r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                        r5: Rewrite[cx, e], r6: Rewrite[cx, f],
                        r7: Rewrite[cx, g], r8: Rewrite[cx, h]): Rewrite[cx, (a, b, c, d, e, f, g, h)] = 
        rewrite((cx, abcdefgh) -> 
            let (a, b, c, d, e, f, g, h) = abcdefgh;
            let ans = forM (
                (s1, a1) <- applyT(oneRewriteStep(false, r1), cx, a);
                (s2, b1) <- applyT(oneRewriteStep(s1, r2), cx, b);
                (s3, c1) <- applyT(oneRewriteStep(s2, r3), cx, c);
                (s4, d1) <- applyT(oneRewriteStep(s3, r4), cx, d);
                (s5, e1) <- applyT(oneRewriteStep(s4, r5), cx, e);
                (s6, f1) <- applyT(oneRewriteStep(s5, r6), cx, f);
                (s7, g1) <- applyT(oneRewriteStep(s6, r7), cx, g);
                (s8, h1) <- applyT(oneRewriteStep(s7, r8), cx, h)
            ) yield (s8, a1, b1, c1, d1, e1, f1, g1, h1);
            match ans {
                case Ok((true, a1, b1, c1, d1, e1, f1, g1, h1)) => Ok((a1, b1, c1, d1, e1, f1, g1, h1))
                case _                                          => Err("oneR8 failed")
            }
        )

    // List

    pub def anyRTraversable(r1: Rewrite[cx, kid]): Rewrite[cx, t[kid]] \ Foldable.Aef[t] with Traversable[t] = 
        rewrite((cx, xs) -> 
            def step(accB, x) = 
                match applyR(r1, cx, x) {
                    case Err(_) => (accB, x)
                    case Ok(x1) => (true, x1)
                };
            let (acc, ys) = Traversable.mapAccumLeft(step, false, xs);
            if (acc) Ok(ys) else Err("anyRTraversable failed")
        )

    pub def oneRTraversable(r1: Rewrite[cx, kid]): Rewrite[cx, t[kid]] \ Foldable.Aef[t] with Traversable[t] = 
        rewrite((cx, xs) -> 
            def step(accB, x) = {
                if (accB) 
                    (true, x)
                else {
                    match applyR(r1, cx, x) {
                        case Err(_) => (accB, x)
                        case Ok(x1) => (true, x1)
                    }
                }
            };
            let (acc, ys) = Traversable.mapAccumLeft(step, false, xs);
            if (acc) Ok(ys) else Err("oneRTraversable failed")
        )

    ///////////////////////////////////////////////////////////////////////////
    // Map
    
    // Rewrite only values, keys stay the same
    pub def anyRMap(r1: Rewrite[cx, kid]): Rewrite[cx, Map[k, kid]] with Order[k] = 
        rewrite((cx, mp) -> 
            def step(accB, kv) = {
                let (k, v) = kv;
                match applyR(r1, cx, v) {
                    case Err(_) => (accB, (k, v))
                    case Ok(v1) => (true, (k, v1))
                }
            };
            let (acc, ys) = Map.toList(mp) |> Traversable.mapAccumLeft(step, false);
            if (acc) Ok(List.toMap(ys)) else Err("anyRMap failed")
        )

    pub def oneRMap(r1: Rewrite[cx, kid]): Rewrite[cx, Map[k, kid]] with Order[k] = 
        rewrite((cx, mp) -> 
            def step(accB, kv) = {
                if (accB) 
                    (true, kv)
                else {
                    let (k, v) = kv;
                    match applyR(r1, cx, v) {
                        case Err(_) => (accB, (k, v))
                        case Ok(v1) => (true, (k, v1))
                    }
                }
            };
            let (acc, ys) = Map.toList(mp) |> Traversable.mapAccumLeft(step, false);
            if (acc) Ok(List.toMap(ys)) else Err("oneRMap failed")
        )


}


