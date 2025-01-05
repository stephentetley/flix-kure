
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

    use RestageLib.Base.Restage
    use RestageLib.Base.{Transform, Rewrite, TransformResult}
    use RestageLib.Base.{restage}

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



    @test
    pub def test01(): Bool = 
        Restage.factory(Exp.Const(0.0f64), Nil) == Exp.Const(0.0f64)


}

