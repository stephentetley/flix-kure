
/*
 * Copyright 2025 Stephen Tetley
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

pub mod TestKIR {
    use TestKIR.NoCtx
    

    use Assert.{assertEq, assertTrue}
    use KIR.Base.{Rewrite}
    use KIR.Base.{applyT}


    pub enum NoCtx with Eq, ToString { case NoCtx }

    def noCtx(): NoCtx = NoCtx.NoCtx

    @Test
    pub def successT01(): Unit \ {Assert, IO} = 
        let ans = applyT(KIR.Base.successT(), noCtx(), 10);
        println(ans);
        assertEq(
            expected = Ok(()),
            ans
        )

    @Test
    pub def constT02(): Unit \ {Assert, IO} = 
        let ans = applyT(KIR.Base.constT(Applicative.point(12)), noCtx(), 10);
        println(ans);
        assertEq(
            expected = Ok(12),
            ans
        )

    @Test
    pub def contextT01(): Unit \ {Assert, IO} = 
        let ans = applyT(KIR.Base.contextT(), noCtx(), 10);
        println(ans);
        assertEq(
            expected = Ok(NoCtx.NoCtx),
            ans
        )

    @Test
    pub def exposeT01(): Unit \ {Assert, IO} = 
        let ans = applyT(KIR.Base.exposeT(), noCtx(), 10);
        println(ans);
        assertEq(
            expected = Ok((NoCtx.NoCtx, 10)),
            ans
        )

    pub def plus1R(): Rewrite[cx, Int32] = 
        KIR.Base.contextFreeT(i -> Ok(i+1))

    @Test
    pub def mapT01(): Unit \ {Assert, IO} = 
        let tf = KIR.Base.mapT(plus1R());
        let ans = applyT(tf, noCtx(), List#{10, 9, 8});
        println(ans);
        assertEq(
            expected = Ok(List#{11, 10, 9}),
            ans
        )


}

