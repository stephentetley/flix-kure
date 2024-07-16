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

mod FlixKure.Transform {

    pub enum Transform[cx: Type, a: Type, b: Type, ef: Eff] {
        case Transform(cx -> a -> b \ ef)
    }

    pub def applyT(t: Transform[cx, a, b, ef], c: cx, x: a): b \ ef = match t {
        case Transform.Transform(f) => f(c, x)
    }

    pub def transform(f: cx -> a -> b \ ef): Transform[cx, a, b, ef] = 
        Transform.Transform(f)

    pub type alias Rewrite[cx: Type, a: Type, ef: Eff] = Transform[cx, a, a, ef]

    pub def applyR(t: Rewrite[cx, a, ef], c: cx, x: a): a \ ef = applyT(t, c, x)


    pub def rewrite(f: cx -> a  -> a \ ef): Rewrite[cx, a, ef] = 
        transform(f)


    pub def contextfreeT(f: a -> b \ ef): Transform[cx, a, b, ef] = 
        Transform.Transform((_, a) -> f(a))
    
    pub def contextonlyT(f: cx -> b \ ef): Transform[cx, a, b, ef] = 
        Transform.Transform((c, _) -> f(c))
    
}

