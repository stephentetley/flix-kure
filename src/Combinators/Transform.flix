/*
 * Copyright 2024 Stephen Tetley
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

mod FlixKure.Combinators.Transform {

    use FlixKure.Transform.{Transform, Rewrite}

    pub def idR(): Rewrite[c, a, ef] = FlixKure.Transform.rewrite((_, a) -> checked_ecast(a))
    
    pub def successT(): Transform[c, a, Unit, ef] = FlixKure.Transform.transform((_, _) -> checked_ecast(()))
    
    pub def contextT(): Transform[c, a, c, ef] = FlixKure.Transform.transform((cx, _) -> checked_ecast(cx))

    pub def exposeT(): Transform[c, a, (c, a), ef] = FlixKure.Transform.transform((cx, a) -> checked_ecast((cx, a)))

    pub def liftContext(f: c -> cx \ ef1, t: Transform[cx, a, b, ef]): Transform[c, a, b, ef + ef1] = 
        FlixKure.Transform.transform((cx, a) -> {let cx1 = f(cx); FlixKure.Transform.applyT(t, cx1, a)})

}

