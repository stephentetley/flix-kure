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

mod RestageLib.Base {

    pub trait Restage[t] {
        pub def children(x: t): List[t]
        pub def factory(e: t, cs: List[t]): t
    }

    pub type alias Rewrite[ef: Eff, cx: Type, p: Type] = Transform[ef, cx, p, p]
    pub type alias Transform[ef: Eff, cx: Type, a: Type, b: Type] = (cx, a) -> TransformResult[ef, cx, a, b] \ ef

    pub enum TransformResult[ef: Eff, cx: Type, a: Type, b: Type] {
        case Success(b)
        case Failure(Transform[ef, cx, a, b])
    }


    pub def restage(e: t): (List[t], List[t] -> t) with Restage[t] = 
        let cs = Restage.children(e);
        let fact = Restage.factory(e);
        (cs, fact)

    pub def isSuccess(x: TransformResult[ef, cx, a, b]): Bool = match x {
        case TransformResult.Success(_) => true
        case TransformResult.Failure(_) => false
    }

    pub def getSuccess(x: TransformResult[ef, cx, a, b]): b = match x {
        case TransformResult.Success(p) => p
        case TransformResult.Failure(_) => bug!("to elim...")
    }


}

