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

    pub def idR(): Rewrite[ef, cx, t] with Restage[t] = 
        Transform.Transform((_, e) -> checked_ecast(TransformResult.Success(e)))

    pub def seqR(p: Rewrite[ef, cx, t], q: Rewrite[ef, cx, t]): Rewrite[ef, cx, t] with Restage[t] = 
        Transform.Transform((cx, e) -> 
            let Transform.Transform(pf) = p;
            let Transform.Transform(qf) = q;
            match pf(cx, e) {
                case TransformResult.Success(e1)    => qf(cx, e1)
                case fk                             => fk
        })


    pub def altR(p: Rewrite[ef, cx, t], q: Rewrite[ef, cx, t]): Rewrite[ef, cx, t] with Restage[t] =
        Transform.Transform((cx, e) -> 
            let Transform.Transform(pf) = p;
            let Transform.Transform(qf) = q;
            match pf(cx, e) {
                case TransformResult.Failure    => qf(cx, e)
                case sk                         => sk
            })



    pub def tryR(s: Rewrite[ef, ctx, t]): Rewrite[ef, ctx, t] with Restage[t] = altR(s, idR())

    pub def repeatR(s: Rewrite[ef, ctx, t]): Rewrite[ef, ctx, t] with Restage[t] = 
        tryR(seqR(s, repeatR(s)))

    pub def allR(s: Rewrite[ef, ctx, t]): Rewrite[ef, ctx, t] with Restage[t] = 
        Transform.Transform((cx, e) ->
            let (cs, fact) = RestageLib.Base.restage(e);
            let csn = List.map(x -> RestageLib.Base.applyT(s, cx, x), cs);
            match RestageLib.Base.allSuccesses(csn) {
                case Some(xs) => TransformResult.Success(fact(xs))
                case None     => TransformResult.Failure
            })

    
    pub def allT(s: Transform[ef, cx, s, t]): Transform[ef, cx, s, t] with Restage[s], Monoid[t] = 
        Transform.Transform((cx, e) ->
            let cs = Restage.children(e);
            let csn = List.map(x -> RestageLib.Base.applyT(s, cx, x), cs);
            match RestageLib.Base.allSuccesses(csn) {
                case Some(xs) => TransformResult.Success(Monoid.fold(xs))
                case None     => TransformResult.Failure
            })

    pub def oneR(s: Rewrite[ef, cx, t]): Rewrite[ef, cx, t] with Restage[t] = 
        Transform.Transform((cx, e) ->
            let (cs, fact) = RestageLib.Base.restage(e);
            let cs1 = List.zipWithIndex(cs);
            let ans = List.foldLeft((state, ei) ->
                let (cont, _) = state;
                let (idx, exp) = ei;
                if (cont) { 
                    match RestageLib.Base.applyT(s, cx, exp) {
                        case TransformResult.Success(nexp)    => {
                            let csn = List.zipWithIndex(cs) |> List.map(x -> if (fst(x) == idx) nexp else snd(x));
                            (false, TransformResult.Success(fact(csn)))
                        }
                        case f                              => (true, f)
                    }
                } else state,
                (true, TransformResult.Failure), 
                cs1);
            snd(ans))

    
    pub def oneT(s: Transform[ef, cx, s, t]): Transform[ef, cx, s, t] with Restage[s] =
        Transform.Transform((cx, e) ->
            let cs = Restage.children(e);
            let cs1 = List.zipWithIndex(cs);
            let ans = List.foldLeft((state, ei) ->
                let (cont, _) = state;
                let (_, exp) = ei;
                if (cont) { 
                    match RestageLib.Base.applyT(s, cx, exp) {
                        case TransformResult.Success(nexp)  => {
                            (false, TransformResult.Success(nexp))
                        }
                        case f                              => (true, f)
                    }
                } else state,
                (true, TransformResult.Failure), 
                cs1);
            snd(ans))


    pub def contextfreeT(f: a -> b \ ef): Transform[ef, cx, a, b] = 
        Transform.Transform((_, e) ->
            let ans = f(e);
            TransformResult.Success(ans)
        )

    pub def contextonlyT(f: cx -> b \ ef): Transform[ef, cx, a, b] = 
        Transform.Transform((cx, _) ->
            let ans = f(cx);
            TransformResult.Success(ans)
        )

    pub def pureT(f: cx -> a -> b): Transform[ef, cx, a, b] = 
        Transform.Transform((cx, e) ->
            let ans = checked_ecast(f(cx, e));
            TransformResult.Success(ans)
        )


    pub def constT(e: b): Transform[ef, cx, a, b] =
        Transform.Transform((_, _) ->
            checked_ecast(TransformResult.Success(e))
        )

    pub def successT(): Transform[ef, cx, a, Unit] = 
        Transform.Transform((_, _) ->
            checked_ecast(TransformResult.Success(()))
        )

    pub def contextT(): Transform[ef, cx, a, cx] =
        Transform.Transform((cx, _) ->
            checked_ecast(TransformResult.Success(cx))
        )


    pub def exposeT(): Transform[ef, cx, a, (cx, a)] =
        Transform.Transform((cx, a) ->
            checked_ecast(TransformResult.Success((cx, a)))
        )


    pub def liftContext(f: cx -> cx1, s: Transform[ef, cx1, a, b]): Transform[ef, cx, a, b] = 
        Transform.Transform((cx, e) ->
            let cx1 = f(cx);
            RestageLib.Base.applyT(s, cx1, e)
        )

    pub def readerT(f: a -> Transform[ef, cx, a, b]): Transform[ef, cx, a, b] =
        Transform.Transform((cx, e) ->
            let f1 = f(e);
            RestageLib.Base.applyT(f1, cx, e)
        )

    pub def optionT(f: (cx, a) -> Option[b] \ ef): Transform[ef, cx, a, b] = 
        Transform.Transform((cx, e) ->
            match f(cx, e) {
                case Some(a) => TransformResult.Success(a)
                case None    => TransformResult.Failure
            })
        
    pub def resultT(f: (cx, a) -> Result[err, b] \ ef): Transform[ef, cx, a, b] = 
        Transform.Transform((cx, e) ->
            match f(cx, e) {
              case Ok(a)  => TransformResult.Success(a)
                case Err(_) => TransformResult.Failure
            })

    pub def mapT(s: Transform[ef, cx, a, b]): Transform[ef + Foldable.Aef[t], cx, t[a], t[b]] with Traversable[t] = 
        Transform.Transform((cx, es) ->
            let mf = RestageLib.Base.applyT(s, cx) >> RestageLib.Base.toResult;
            match Traversable.traverse(mf, es) {
                case Ok(xs) => TransformResult.Success(xs)
                case Err(_) => TransformResult.Failure
            })

    pub def andR(ts: f[Rewrite[ef, cx, a]]): Rewrite[ef + Foldable.Aef[f], cx, a] with Restage[a], Foldable[f] = 
        Transform.Transform((cx, e) ->
            let f = Foldable.foldRight((b, a) -> seqR(a, b), idR(), ts);
            RestageLib.Base.applyT(f, cx, e)
        )




}

