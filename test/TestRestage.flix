
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

mod TestRestage {

    use FlixKure.Restage

    pub enum Exp with Eq, Order, ToString {
        case Build(Exp, String, Exp)
        case Length(Exp)
        case Plus(Exp, Exp)
        case Mult(Exp, Exp)
        case Const(Float64)
    }

    instance Restage[Exp] {
        pub def children(e: Exp): List[Exp] = match e {
            case Exp.Build(e1, _, e2)   => List#{e1, e2}
            case Exp.Length(e1)         => List#{e1}
            case Exp.Plus(e1, e2)       => List#{e1, e2}
            case Exp.Mult(e1, e2)       => List#{e1, e2}
            case Exp.Const(_)           => Nil
        }

        pub def factory(e: Exp, cs: List[Exp]): Exp = match (cs, e) {
            case (c1 :: c2 :: _,    Exp.Build(_, x, _)) => Exp.Build(c1, x, c2)
            case (c1 :: _ ,         Exp.Length(_))      => Exp.Length(c1)
            case (c1 :: c2 :: _,    Exp.Plus(_, _))     => Exp.Plus(c1, c2)
            case (c1 :: c2 :: _,    Exp.Mult(_, _))     => Exp.Mult(c1, c2)
            case (_,                Exp.Const(c))       => Exp.Const(c) 
            case (_, _)                                 => bug!("factory")
        }
    }

    pub def restage(e: t): (List[t], List[t] -> t) with Restage[t] = 
        let cs = Restage.children(e);
        let fact = Restage.factory(e);
        (cs, fact)

    // TODO cps transform...
    pub def buRestage(f: t -> Option[t] \ ef, e: t): t \ ef with Restage[t] = match restage(e) {
        case (cs, fact) => {
            let ne = fact(List.map(buRestage(f), cs));
            Option.getWithDefault(ne, f(ne))
        }
    }

    // TODO cps transform...
    pub def tdRestage(f: t -> Option[t] \ ef, e: t): t \ ef with Restage[t] = 
        let top = Option.getWithDefault(e, f(e));
        match restage(top) {
            case (cs, fact) => {
                fact(List.map(tdRestage(f), cs))
            }
        }


    type alias Rewrite[p] = Transform[p, p]
    type alias Transform[a, b] = a -> TransformResult[a, b]

    pub enum TransformResult[a, b] {
        case Success(b)
        case Failure(Transform[a, b])
    }

    pub def isSuccess(x: TransformResult[a, b]): Bool = match x {
        case TransformResult.Success(_) => true
        case TransformResult.Failure(_) => false
    }

    pub def getS(x: TransformResult[a, b]): b = match x {
        case TransformResult.Success(p) => p
        case TransformResult.Failure(_) => bug!("to elim...")
    }



    pub def seqR(p: Rewrite[t], q: Rewrite[t]): Rewrite[t] with Restage[t] = e -> match p(e) {
        case TransformResult.Success(_)   => q(e)
        case fk                         => fk
    }


    pub def alt(p: Rewrite[t], q: Rewrite[t]): Rewrite[t] with Restage[t] = e -> match p(e) {
        case TransformResult.Failure(_)   => q(e)
        case sk                         => sk
    }

    pub def idR(): Rewrite[t] with Restage[t] = e -> TransformResult.Success(e)

    // aka `try`
    pub def attemptR(s: Rewrite[t]): Rewrite[t] with Restage[t] = alt(s, idR())

    pub def repeatR(s: Rewrite[t]): Rewrite[t] with Restage[t] = 
        attemptR(seqR(s, repeatR(s)))

    pub def allR(s: Rewrite[t]): Rewrite[t] with Restage[t] = e ->
        let (cs, fact) = restage(e);
        let csn = List.map(s, cs);
        if (List.forAll(isSuccess, csn)) {
            let ans = fact(List.map(getS, csn));
            TransformResult.Success(ans)
        } else {
            TransformResult.Failure(s)
        }

    
    pub def allT(s: Transform[s, t]): Transform[s, t] with Restage[s], Monoid[t] = e ->
        let cs = Restage.children(e);
        let csn = List.map(s, cs);
        if (List.forAll(isSuccess, csn)) {
            let ans = Monoid.fold(List.map(getS, csn));
            TransformResult.Success(ans)
        } else {
            TransformResult.Failure(s)
        }

    pub def oneR(s: Rewrite[t]): Rewrite[t] with Restage[t] = e ->
        let (cs, fact) = restage(e);
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

    @test
    pub def test01(): Bool = 
        Restage.factory(Exp.Const(0.0f64), Nil) == Exp.Const(0.0f64)


}

