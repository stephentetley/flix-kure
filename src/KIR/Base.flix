/*
 * Copyright 2022 Stephen Tetley
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


mod KIR.Base {
    

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject

    pub type alias Answer[a] = Result[String, a]

    // Transform is a function monad but we "pretend" it is 
    // just a simple monad like Option or Result 
    // so we don't have to worry about capturing efffects
    pub enum Transform[cx: Type, a: Type, b: Type] { 
        case Transform((cx, a) -> Answer[b])
    }
    
    pub type alias Rewrite[cx: Type, t: Type] = Transform[cx, t, t]

    def runTransform(f: Transform[cx: Type, a: Type, b: Type], ctx: cx, a: a): Result[String, b] = 
        let Transform.Transform(f1) = f;
        f1(ctx, a)

    instance Functor[Transform[cx, t]] {
        pub def map(f: a -> b \ ef, t: Transform[cx, t, a]): Transform[cx, t, b] \ ef = 
            let Transform.Transform(f1) = t;
            unchecked_cast(Transform.Transform((cx, a) -> {
                match f1(cx, a) {
                    case Ok(a1)   => Ok(unchecked_cast(f(a1) as _ \ {}))
                    case Err(msg) => Err(msg)
                }
            }) as _ \ ef)
    }

    instance Applicative[Transform[cx, t]] {
        pub def point(a: a): Transform[cx, t, a] = 
            Transform.Transform((_, _) -> Ok(a))
        
        pub def ap(f: Transform[cx, t, a -> b \ ef], t: Transform[cx, t, a]): Transform[cx, t, b] \ ef = 
            unchecked_cast(Transform.Transform((cx, a) -> 
                match runTransform(f, cx, a) {
                    case Ok(f1)   => match runTransform(t, cx, a) {
                        case Ok(a1)   => Ok(unchecked_cast(f1(a1) as _ \ {}))
                        case Err(msg) => Err(msg)
                    }
                    case Err(msg) => Err(msg)
                }) as _ \ ef)
    }

    instance Monad[Transform[cx, t]] {
        pub def flatMap(f: a -> Transform[cx, t, b] \ ef, x: Transform[cx, t, a]): Transform[cx, t, b] \ ef = 
            unchecked_cast(Transform.Transform((cx, a) -> 
                  match runTransform(x, cx, a) {
                    case Ok(a1)   => { 
                        let b1 = unchecked_cast(f(a1) as _ \ {});
                        runTransform(b1, cx, a)
                    }
                    case Err(msg) => Err(msg)
                }) as _ \ ef)
    }


    pub trait Injection[a] {
        type Universe[a]: Type

        pub def inj(a: a): Injection.Universe[a]

        pub def proj(u: Injection.Universe[a]): Option[a]
    }

    pub enum U {
        case UV(JsonValue)
        case UA(JsonArray)
        case UO(JsonObject)
    }

    instance Injection[JsonValue] {
        type Universe[JsonValue] = U
        
        pub def inj(a: JsonValue): U = U.UV(a)
        pub def proj(u: U): Option[JsonValue] = match u {
            case U.UV(x) => Some(x)
            case _       => None

        }
    }


    instance Injection[JsonArray] {
        type Universe[JsonArray] = U
        
        pub def inj(a: JsonArray): U = U.UA(a)
        pub def proj(u: U): Option[JsonArray] = match u {
            case U.UA(x) => Some(x)
            case _       => None

        }
    }

    instance Injection[JsonObject] {
        type Universe[JsonObject] = U
        
        pub def inj(a: JsonObject): U = U.UO(a)
        pub def proj(u: U): Option[JsonObject] = match u {
            case U.UO(x) => Some(x)
            case _       => None

        }
    }

    pub def fail(msg: String): Answer[a] = Err(msg)

    pub def catchErr(t: Transform[cx, a, b], th: String -> Transform[cx, a, b] \ ef): Transform[cx, a, b] \ ef = 
        unchecked_cast(Transform.Transform((cx, a) -> 
            match runTransform(t, cx, a) {
                case Err(msg) => { 
                    let fh = unchecked_cast(th(msg) as _ \ {});
                    runTransform(fh, cx, a)
                }
                case Ok(ans) => Ok(ans)
            }) as _ \ ef)


    pub def idT(): Transform[cx, a, a] =
        Transform.Transform((_, a) -> Ok(a))


    pub def composeT(t1: Transform[cx, b, c], t2: Transform[cx, a, b]): Transform[cx, a, c] =
        Transform.Transform((cx, a) -> 
            match runTransform(t2, cx, a) {
                case Ok(b)    => runTransform(t1, cx, b)
                case Err(msg) => Err(msg)
            })

    pub def arrT(f: a -> b \ ef): Transform[cx, a, b] \ ef =
        unchecked_cast(Transform.Transform((_, a) -> Ok(unchecked_cast(f(a) as _ \ {}))) as _ \ ef)

    pub def firstT(t: Transform[cx, a, b]): Transform[cx, (a, z), (b, z)] =
        Transform.Transform((cx, az) -> {
            let (a, z) = az;
            Functor.map(b -> (b, z), runTransform(t, cx, a))
        })


    pub def applyT(t: Transform[cx, a, b], cx: cx, a: a): Answer[b] \ ef =
        unchecked_cast(runTransform(t, cx, a) as _ \ ef)

    pub def applyR(t: Rewrite[cx, a], cx: cx, a: a): Answer[a] \ ef = 
        applyT(t, cx, a)


    pub def transform(f: (cx, a) -> Answer[b] \ ef): Transform[cx, a, b] \ ef = 
        unchecked_cast(Transform.Transform((cx, a) -> 
            unchecked_cast(f(cx, a) as _ \ {})
        ) as _ \ ef) 

    pub def transformOk(f: (cx, a) -> b \ ef): Transform[cx, a, b] \ ef = 
        transform((cx, a) -> Ok(f(cx, a))) 


    pub def rewrite(f: (cx, a) -> Answer[a] \ ef): Rewrite[cx, a] \ ef = 
        transform(f)

    pub def rewriteOk(f: (cx, a) -> a \ ef): Rewrite[cx, a] \ ef = 
        transformOk(f) 


    pub def contextFreeT(f: a -> Answer[b] \ ef): Transform[cx, a, b] \ ef = 
        transform((_, a) -> f(a))


    pub def contextOnlyT(f: cx -> Answer[b] \ ef): Transform[cx, a, b] \ ef = 
        transform((cx, _) -> f(cx))


    pub def constT(ab: Answer[b]): Transform[cx, a, b] = 
        contextFreeT(_ -> ab)

    pub def effectFreeT(f: (cx, a) -> Answer[b]): Transform[cx, a, b] = 
        transform((cx, a) -> f(cx, a))

    pub def injectT(): Transform[cx, a, u] with Injection[a] where Injection.Universe[a] ~ u = 
        arrT(Injection.inj)

    // Combinators.Transform

    pub def idR(): Rewrite[cx, a] = idT()

    pub def successT(): Transform[cx, a, Unit] = Applicative.point()

    pub def contextT(): Transform[cx, a, cx] = 
        transform((cx, _) -> Ok(cx))

    pub def exposeT(): Transform[cx, a, (cx, a)] = 
        transform((cx, a) -> Ok((cx, a)))







}

