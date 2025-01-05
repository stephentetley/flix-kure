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

mod RestageLib.Combinators {


    use RestageLib.Base.Restage
    use RestageLib.Base.{Transform, Rewrite, TransformResult}

    pub def idR(): Rewrite[t] with Restage[t] = e -> TransformResult.Success(e)

    pub def seqR(p: Rewrite[t], q: Rewrite[t]): Rewrite[t] with Restage[t] = e -> match p(e) {
        case TransformResult.Success(_)   => q(e)
        case fk                         => fk
    }


    pub def alt(p: Rewrite[t], q: Rewrite[t]): Rewrite[t] with Restage[t] = e -> match p(e) {
        case TransformResult.Failure(_)   => q(e)
        case sk                         => sk
    }


    // aka `try`
    pub def attemptR(s: Rewrite[t]): Rewrite[t] with Restage[t] = alt(s, idR())

    pub def repeatR(s: Rewrite[t]): Rewrite[t] with Restage[t] = 
        attemptR(seqR(s, repeatR(s)))

    pub def allR(s: Rewrite[t]): Rewrite[t] with Restage[t] = e ->
        let (cs, fact) = RestageLib.Base.restage(e);
        let csn = List.map(s, cs);
        if (List.forAll(RestageLib.Base.isSuccess, csn)) {
            let ans = fact(List.map(RestageLib.Base.getSuccess, csn));
            TransformResult.Success(ans)
        } else {
            TransformResult.Failure(s)
        }

    
    pub def allT(s: Transform[s, t]): Transform[s, t] with Restage[s], Monoid[t] = e ->
        let cs = Restage.children(e);
        let csn = List.map(s, cs);
        if (List.forAll(RestageLib.Base.isSuccess, csn)) {
            let ans = Monoid.fold(List.map(RestageLib.Base.getSuccess, csn));
            TransformResult.Success(ans)
        } else {
            TransformResult.Failure(s)
        }

    pub def oneR(s: Rewrite[t]): Rewrite[t] with Restage[t] = e ->
        let (cs, fact) = RestageLib.Base.restage(e);
        let cs1 = List.zipWithIndex(cs);
        let ans = List.foldLeft((state, ei) ->
            let (cont, _) = state;
            let (idx, exp) = ei;
            if (cont) { 
                match s(exp) {
                    case TransformResult.Success(nexp)    => {
                        let csn = List.zipWithIndex(cs) |> List.map(x -> if (fst(x) == idx) nexp else snd(x));
                        (false, TransformResult.Success(fact(csn)))
                    }
                    case f                              => (true, f)
                }
            } else state,
            (true, TransformResult.Failure(s)), 
            cs1);
        snd(ans)

    
    pub def oneT(s: Transform[s, t]): Transform[s, t] with Restage[s] = e ->
        let cs = Restage.children(e);
        let cs1 = List.zipWithIndex(cs);
        let ans = List.foldLeft((state, ei) ->
            let (cont, _) = state;
            let (_, exp) = ei;
            if (cont) { 
                match s(exp) {
                    case TransformResult.Success(nexp)  => {
                        (false, TransformResult.Success(nexp))
                    }
                    case f                              => (true, f)
                }
            } else state,
            (true, TransformResult.Failure(s)), 
            cs1);
        snd(ans)

}

