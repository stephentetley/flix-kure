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


    def anyRewriteStep(r: Rewrite[cx, a]): Transform[cx, a, (Bool, a)] = 
        transform((cx, a) -> 
            match applyR(r, cx, a) {
                case Ok(a1) => Ok((true, a1))
                case Err(_) => Ok((false, a))
            }
        )
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



    // At least one success - try all
    pub def makeAnyR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b], r3: Rewrite[cx, c]): Rewrite[cx, (a, b, c)] = 
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


    pub def makeOneR3(r1: Rewrite[cx, a], r2: Rewrite[cx, b], r3: Rewrite[cx, c]): Rewrite[cx, (a, b, c)] = 
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



    pub def anyRList(r1: Rewrite[cx, kid]): Rewrite[cx, List[kid]] = 
        rewrite((cx, xs) -> 
            def step(accB, x) = 
                match applyR(r1, cx, x) {
                    case Err(_) => (accB, x)
                    case Ok(x1) => (true, x1)
                };
            let (acc, ys) = Traversable.mapAccumLeft(step, false, xs);
            if (acc) Ok(ys) else Err("makeAnyRList failed")
        )

    pub def oneRList(r1: Rewrite[cx, kid]): Rewrite[cx, List[kid]] = 
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
            if (acc) Ok(ys) else Err("makeAnyRList failed")
        )

    // pub def makeAnyRList(r1: Rewrite[cx, kid], f: a -> List[kid], g: List[kid] -> a): Rewrite[cx, a] = 
    //     rewrite((cx, xs) -> 
    //         def step(accB, x) = 
    //             match applyR(r1, cx, x) {
    //                 case Err(_) => (accB, x)
    //                 case Ok(x1) => (true, x1)
    //             };
    //         let (acc, ys) = Traversable.mapAccumLeft(step, false, f(xs));
    //         if (acc) Ok(g(ys)) else Err("makeAnyRList failed")
    //     )


    // def checkSuccessPBool(msg: String, ma: Answer[PBool[a]]): Answer[a] = 
    //     Monad.flatMap(match (PBool.PBool(bool,a)) -> if (bool) Ok(a) else Err(msg), ma)

    // pub enum AnyR[a] {
    //     case AnyR(Answer[PBool[a]])
    // }

    // def wrapAnyR()

}


