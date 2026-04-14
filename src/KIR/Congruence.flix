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

    // In Haskell the machinery for AnyR amd OneR changes the monad 
    // but we have fixed it to Answer, so we need our own solution
    // to simplify writing congruence combinators


    ///////////////////////////////////////////////////////////////////////////
    // AllR

    // All must succeed
    pub def allR2(r1: Rewrite[cx, a], r2: Rewrite[cx, b]): Rewrite[cx, (a, b)] = 
        rewrite((cx, ab) -> 
            let (a, b) = ab;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b)
            ) yield (a1, b1);
            Result.mapErr(_ -> "anyR2 failed", ans)
        )

    pub def allR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b],
                    r3: Rewrite[cx, c]): Rewrite[cx, (a, b, c)] = 
        rewrite((cx, abc) -> 
            let (a, b, c) = abc;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b);
                c1 <- applyR(r3, cx, c)
            ) yield (a1, b1, c1);
            Result.mapErr(_ -> "anyR3 failed", ans)
        )

    pub def allR4(r1: Rewrite[cx, a], r2: Rewrite[cx, b],
                    r3: Rewrite[cx, c], r4: Rewrite[cx, d]): Rewrite[cx, (a, b, c, d)] = 
        rewrite((cx, abcd) -> 
            let (a, b, c, d) = abcd;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b);
                c1 <- applyR(r3, cx, c);
                d1 <- applyR(r4, cx, d)
            ) yield (a1, b1, c1, d1);
            Result.mapErr(_ -> "anyR4 failed", ans)
        )

    pub def allR5(r1: Rewrite[cx, a], r2: Rewrite[cx, b],
                    r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                    r5: Rewrite[cx, e]): Rewrite[cx, (a, b, c, d, e)] = 
        rewrite((cx, abcde) -> 
            let (a, b, c, d, e) = abcde;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b);
                c1 <- applyR(r3, cx, c);
                d1 <- applyR(r4, cx, d);
                e1 <- applyR(r5, cx, e)
            ) yield (a1, b1, c1, d1, e1);
            Result.mapErr(_ -> "anyR5 failed", ans)
        )

    pub def allR6(r1: Rewrite[cx, a], r2: Rewrite[cx, b],
                    r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                    r5: Rewrite[cx, e], r6: Rewrite[cx, f]): Rewrite[cx, (a, b, c, d, e, f)] = 
        rewrite((cx, abcdef) -> 
            let (a, b, c, d, e, f) = abcdef;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b);
                c1 <- applyR(r3, cx, c);
                d1 <- applyR(r4, cx, d);
                e1 <- applyR(r5, cx, e);
                f1 <- applyR(r6, cx, f)
            ) yield (a1, b1, c1, d1, e1, f1);
            Result.mapErr(_ -> "anyR6 failed", ans)
        )

    pub def allR7(r1: Rewrite[cx, a], r2: Rewrite[cx, b],
                    r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                    r5: Rewrite[cx, e], r6: Rewrite[cx, f], 
                    r7: Rewrite[cx, g]): Rewrite[cx, (a, b, c, d, e, f, g)] = 
        rewrite((cx, abcdefg) -> 
            let (a, b, c, d, e, f, g) = abcdefg;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b);
                c1 <- applyR(r3, cx, c);
                d1 <- applyR(r4, cx, d);
                e1 <- applyR(r5, cx, e);
                f1 <- applyR(r6, cx, f);
                g1 <- applyR(r7, cx, g)
            ) yield (a1, b1, c1, d1, e1, f1, g1);
            Result.mapErr(_ -> "anyR7 failed", ans)
        )

    pub def allR8(r1: Rewrite[cx, a], r2: Rewrite[cx, b],
                    r3: Rewrite[cx, c], r4: Rewrite[cx, d],
                    r5: Rewrite[cx, e], r6: Rewrite[cx, f], 
                    r7: Rewrite[cx, g], r8: Rewrite[cx, h]): Rewrite[cx, (a, b, c, d, e, f, g, h)] = 
        rewrite((cx, abcdefgh) -> 
            let (a, b, c, d, e, f, g, h) = abcdefgh;
            let ans = forM (
                a1 <- applyR(r1, cx, a);
                b1 <- applyR(r2, cx, b);
                c1 <- applyR(r3, cx, c);
                d1 <- applyR(r4, cx, d);
                e1 <- applyR(r5, cx, e);
                f1 <- applyR(r6, cx, f);
                g1 <- applyR(r7, cx, g);
                h1 <- applyR(r8, cx, h)
            ) yield (a1, b1, c1, d1, e1, f1, g1, h1);
            Result.mapErr(_ -> "anyR8 failed", ans)
        )

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
    pub def anyR2(r1: Rewrite[cx, a], r2: Rewrite[cx, b]): Rewrite[cx, (a, b)] = 
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
    pub def anyR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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
    
    pub def anyR4(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def anyR5(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def anyR6(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def anyR7(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def anyR8(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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


    pub def oneR2(r1: Rewrite[cx, a], r2: Rewrite[cx, b]): Rewrite[cx, (a, b)] = 
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





    pub def oneR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def oneR4(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def oneR5(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def oneR6(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def oneR7(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    pub def oneR8(r1: Rewrite[cx, a], r2: Rewrite[cx, b], 
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

    ///////////////////////////////////////////////////////////////////////////
    // List (Traversable)

    pub def allR_Traversable(r1: Rewrite[cx, kid]): Rewrite[cx, t[kid]] \ Foldable.Aef[t] with Traversable[t] = 
        rewrite((cx, xs) -> 
            def step(accB, x) = 
                match applyR(r1, cx, x) {
                    case Err(_) => (false, x)
                    case Ok(x1) => (accB, x1)
                };
            let (acc, ys) = Traversable.mapAccumLeft(step, true, xs);
            if (acc) Ok(ys) else Err("allRTraversable failed")
        )

    pub def anyR_Traversable(r1: Rewrite[cx, kid]): Rewrite[cx, t[kid]] \ Foldable.Aef[t] with Traversable[t] = 
        rewrite((cx, xs) -> 
            def step(accB, x) = 
                match applyR(r1, cx, x) {
                    case Err(_) => (accB, x)
                    case Ok(x1) => (true, x1)
                };
            let (acc, ys) = Traversable.mapAccumLeft(step, false, xs);
            if (acc) Ok(ys) else Err("anyRTraversable failed")
        )

    pub def oneR_Traversable(r1: Rewrite[cx, kid]): Rewrite[cx, t[kid]] \ Foldable.Aef[t] with Traversable[t] = 
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


    // Combine all successes (monoid required)
    pub def allT_Foldable(t1: Transform[cx, kid, b]): Transform[cx, t[kid], b] \ Foldable.Aef[t] with Traversable[t], Monoid[b] = 
        transform((cx, xs) -> 
            def step(acc, x) = match acc {
                case Ok(b) => applyT(t1, cx, x) |> Functor.map(Monoid.combine(b))
                case _     => acc
            };
            Foldable.foldLeft(step, Ok(Monoid.empty()), xs) 
                |> Result.mapErr(_ -> "allTFoldable failed")
        )


    // Get the first success (no monoid required)
    pub def oneT_Foldable(t1: Transform[cx, kid, b]): Transform[cx, t[kid], b] \ Foldable.Aef[t] with Traversable[t] = 
        transform((cx, xs) -> 
            def step(acc, x) = match acc {
                case None => 
                    match applyT(t1, cx, x) {
                        case Err(_) => None
                        case Ok(x1) => Some(x1)
                    }
                case _   => acc
            };
            Foldable.foldLeft(step, None, xs) 
                |> Option.toOk("oneTFoldable failed")
        )


    ///////////////////////////////////////////////////////////////////////////
    // Map
    
    // Rewrite keys and values
    pub def allR_Map(r1: Rewrite[cx, (k, v)]): Rewrite[cx, Map[k, v]] with Order[k] = 
        rewrite((cx, mp) -> 
            def step(accB, kv) = {
                if (accB) {
                    match applyR(r1, cx, kv) {
                        case Err(_) => (accB, kv)
                        case Ok(kv1) => (true, kv1)
                    }
                } else (false, kv)
            };
            let (acc, ys) = Map.toList(mp) |> Traversable.mapAccumLeft(step, true);
            if (acc) Ok(List.toMap(ys)) else Err("anyRMap failed")
        )



    // Rewrite keys and values
    pub def anyR_Map(r1: Rewrite[cx, (k, v)]): Rewrite[cx, Map[k, v]] with Order[k] = 
        rewrite((cx, mp) -> 
            def step(accB, kv) = {
                match applyR(r1, cx, kv) {
                    case Err(_) => (accB, kv)
                    case Ok(kv1) => (true, kv1)
                }
            };
            let (acc, ys) = Map.toList(mp) |> Traversable.mapAccumLeft(step, false);
            if (acc) Ok(List.toMap(ys)) else Err("anyRMap failed")
        )

    pub def oneR_Map(r1: Rewrite[cx, (k, v)]): Rewrite[cx, Map[k, v]] with Order[k] = 
        rewrite((cx, mp) -> 
            def step(accB, kv) = {
                if (accB) 
                    (true, kv)
                else {
                    match applyR(r1, cx, kv) {
                        case Err(_) => (accB, kv)
                        case Ok(kv1) => (true, kv1)
                    }
                }
            };
            let (acc, ys) = Map.toList(mp) |> Traversable.mapAccumLeft(step, false);
            if (acc) Ok(List.toMap(ys)) else Err("oneRMap failed")
        )

    pub def oneT_Map(t1: Transform[cx, (k, v), b]): Transform[cx, Map[k, v], b] with Order[k] = 
        transform((cx, mp) -> {
            let ys = Map.toList(mp);
            match List.findMap(x -> { applyT(t1, cx, x) |> Result.toOption }, ys) {
                case Some(ans) => Ok(ans)
                case None      => Err("oneT_Map")
            }
        })



}


