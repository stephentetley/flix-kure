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
    pub enum Transform[ef: Eff, cx: Type, a: Type, b: Type] { 
        case Transform((cx, a) -> TransformResult[b] \ ef)
    }

    // TODO - change to Result with String for error?
    pub enum TransformResult[a] {
        case Success(a)
        case Failure
    }

    pub def toResult(x: TransformResult[a]): Result[String, a] = match x {
        case TransformResult.Success(a) => Ok(a)
        case TransformResult.Failure    => Err("Failure")
    }

    pub def applyT(t: Transform[ef, cx, a, b], cx: cx, a: a): TransformResult[b] \ ef =
        let Transform.Transform(f) = t;
        f(cx, a)


    pub def applyR(t: Rewrite[ef, cx, a], cx: cx, a: a): TransformResult[a] \ ef = applyT(t, cx, a)
        


    pub def restage(e: t): (List[t], List[t] -> t) with Restage[t] = 
        let cs = Restage.children(e);
        let fact = Restage.factory(e);
        (cs, fact)

    pub def isSuccess(x: TransformResult[a]): Bool = match x {
        case TransformResult.Success(_) => true
        case TransformResult.Failure    => false
    }

    // This is partial so we don't want to reintroduce it if we can avoid it...
    // pub def getSuccess(x: TransformResult[ef, cx, a, b]): b = match x {
    //     case TransformResult.Success(p) => p
    //     case TransformResult.Failure(_) => bug!("to elim...")
    // }


    pub def allSuccesses(xs: List[TransformResult[a]]): Option[List[a]] = 
        def loop(ll, fk, sk) = match ll {
            case Nil                                => sk(Nil)
            case TransformResult.Success(p) :: rs   => loop(rs, fk, ks -> sk(p :: ks))
            case TransformResult.Failure :: _       => fk()
        };
        loop(xs, _ -> None, ks -> Some(ks))

}

