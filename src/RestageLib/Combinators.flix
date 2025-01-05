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

    pub def idR(): Rewrite[ef, cx, t] with Restage[t] = (_, e) -> checked_ecast(TransformResult.Success(e))

    pub def seqR(p: Rewrite[ef, cx, t], q: Rewrite[ef, cx, t]): Rewrite[ef, cx, t] with Restage[t] = (cx, e) -> match p(cx, e) {
        case TransformResult.Success(_) => q(cx, e)
        case fk                         => fk
    }


    pub def altR(p: Rewrite[ef, cx, t], q: Rewrite[ef, cx, t]): Rewrite[ef, cx, t] with Restage[t] =(cx, e) ->  match p(cx, e) {
        case TransformResult.Failure(_) => q(cx, e)
        case sk                         => sk
    }



    pub def tryR(s: Rewrite[ef, ctx, t]): Rewrite[ef, ctx, t] with Restage[t] = altR(s, idR())

    pub def repeatR(s: Rewrite[ef, ctx, t]): Rewrite[ef, ctx, t] with Restage[t] = 
        tryR(seqR(s, repeatR(s)))

    pub def allR(s: Rewrite[ef, ctx, t]): Rewrite[ef, ctx, t] with Restage[t] = (cx, e) ->
        let (cs, fact) = RestageLib.Base.restage(e);
        let csn = List.map(x -> s(cx, x), cs);
        match RestageLib.Base.allSuccesses(csn) {
            case Some(xs) => TransformResult.Success(fact(xs))
            case None     => TransformResult.Failure(s) 
        }

    
    pub def allT(s: Transform[ef, cx, s, t]): Transform[ef, cx, s, t] with Restage[s], Monoid[t] = (cx, e) ->
        let cs = Restage.children(e);
        let csn = List.map(x -> s(cx, x), cs);
        match RestageLib.Base.allSuccesses(csn) {
            case Some(xs) => TransformResult.Success(Monoid.fold(xs))
            case None     => TransformResult.Failure(s) 
        }

    pub def oneR(s: Rewrite[ef, cx, t]): Rewrite[ef, cx, t] with Restage[t] = (cx, e) ->
        let (cs, fact) = RestageLib.Base.restage(e);
        let cs1 = List.zipWithIndex(cs);
        let ans = List.foldLeft((state, ei) ->
            let (cont, _) = state;
            let (idx, exp) = ei;
            if (cont) { 
                match s(cx, exp) {
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

    
    pub def oneT(s: Transform[ef, cx, s, t]): Transform[ef, cx, s, t] with Restage[s] = (cx,e) ->
        let cs = Restage.children(e);
        let cs1 = List.zipWithIndex(cs);
        let ans = List.foldLeft((state, ei) ->
            let (cont, _) = state;
            let (_, exp) = ei;
            if (cont) { 
                match s(cx, exp) {
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

