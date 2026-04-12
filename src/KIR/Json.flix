/*
 * Copyright 2026 Stephen Tetley
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


mod KIR.Json {
    

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject
    
    use KIR.Base.{Transform, Rewrite, Answer}
    use KIR.Base.{transform, rewrite, applyR}
    use KIR.Walker.{Walker}


    // Don't bother with Injection - It makes things very complicated 
    // because JsonValue isn't an algebraic datatype and would need a 
    // newtype wrapper (otherwise orphan instance)


    
    pub enum XJsonValue(JsonValue)

    def unwrap(x: XJsonValue): JsonValue = 
        let XJsonValue.XJsonValue(x1)  = x;
        x1

    def wrap(x: JsonValue): XJsonValue = 
        XJsonValue.XJsonValue(x)




    instance Walker[XJsonValue] {
        type Context[XJsonValue] = Unit

        pub def allR(r: Rewrite[Unit, XJsonValue]): Rewrite[Unit, XJsonValue] = 
            rewrite((cx, a) -> {
                let a1 = unwrap(a);
                let rW: Rewrite[Unit, JsonValue] = 
                    rewrite((cx1, jv) -> {
                        let ans = applyR(r, cx1, wrap(jv));
                        Functor.map(unwrap, ans)
                    });
                applyR(jsonAllR(rW), cx, a1) |> Functor.map(wrap)
            })

        pub def anyR(r: Rewrite[Unit, XJsonValue]): Rewrite[Unit, XJsonValue] = 
            rewrite((cx, a) -> {
                let a1 = unwrap(a);
                let rW: Rewrite[Unit, JsonValue] = 
                    rewrite((cx1, jv) -> {
                        let ans = applyR(r, cx1, wrap(jv));
                        Functor.map(unwrap, ans)
                    });
                applyR(jsonAnyR(rW), cx, a1) |> Functor.map(wrap)
            })


    }

    
    pub enum JsonObjectRow{
        case JsonObjectRow(String, JsonValue)
    }


    pub def jsonAllR(r1: Rewrite[cx, JsonValue]): Rewrite[cx, JsonValue] = 
        rewrite((cx, v) -> 
            match InteropJson.JsonValue.getJsonArray(v) {
                case Some(arr) => {
                    let ma: Answer[JsonArray] = applyR(jsonArrayAllR(r1), cx, arr); 
                    Functor.map(InteropJson.JsonArray.toJsonValue, ma)
                }
                case None => match InteropJson.JsonValue.getJsonObject(v) {
                    case Some(obj) => {
                        let r1kv = rewrite((cx1, kv) -> { 
                            let JsonObjectRow.JsonObjectRow(k1, v1) = kv; 
                            let kids: Answer[JsonValue] = applyR(r1, cx1, v1);
                            Functor.map(JsonObjectRow.JsonObjectRow(k1), kids)
                        });
                        let ma: Answer[JsonObject] = applyR(jsonObjectAllR(r1kv), cx, obj); 
                        Functor.map(InteropJson.JsonObject.toJsonValue, ma)
                        
                    }
                    case None => Ok(v)
                }
            }
        )

    pub def jsonAnyR(r1: Rewrite[cx, JsonValue]): Rewrite[cx, JsonValue] = 
        rewrite((cx, v) -> 
            match InteropJson.JsonValue.getJsonArray(v) {
                case Some(arr) => {
                    let ma: Answer[JsonArray] = applyR(jsonArrayAnyR(r1), cx, arr); 
                    Functor.map(InteropJson.JsonArray.toJsonValue, ma)
                }
                case None => match InteropJson.JsonValue.getJsonObject(v) {
                    case Some(obj) => {
                        let r1kv = rewrite((cx1, kv) -> { 
                            let JsonObjectRow.JsonObjectRow(k1, v1) = kv; 
                            let kids: Answer[JsonValue] = applyR(r1, cx1, v1);
                            Functor.map(JsonObjectRow.JsonObjectRow(k1), kids)
                        });
                        let ma: Answer[JsonObject] = applyR(jsonObjectAnyR(r1kv), cx, obj); 
                        Functor.map(InteropJson.JsonObject.toJsonValue, ma)
                        
                    }
                    case None => Ok(v)
                }
            }
        )



    // `getNull` should be renamed `getJsonNull`, add `getJsonTrue`, `getJsonFalse`

    pub def jsonNullT(b: b): Transform[cx, JsonValue, b] = 
        KIR.Base.contextFreeT(a -> 
            match InteropJson.JsonValue.getNull(a) {
                case Some() => Ok(b)
                case None   => Err("not a JsonNull")
            }
        )

    // No rewrite combinators for JSonNull, JsonFalse, JsonTrue, JsonNumber, JsonString

    pub def jsonTrueT(b: b): Transform[cx, JsonValue, b] = 
        KIR.Base.contextFreeT(a -> 
            match InteropJson.JsonValue.getBool(a) {
                case Some(a1) if a1 => Ok(b)
                case _              => Err("not a JsonTrue")
            }
        )

    pub def jsonFalseT(b: b): Transform[cx, JsonValue, b] = 
        KIR.Base.contextFreeT(a -> 
            match InteropJson.JsonValue.getBool(a) {
                case Some(a1) if not a1 => Ok(b)
                case _                  => Err("not a JsonFalse")
            }
        )


    pub def jsonStringT(f: String -> b \ ef): Transform[cx, JsonValue, b] \ ef= 
        KIR.Base.contextFreeT(a -> 
            match InteropJson.JsonValue.getString(a) {
                case Some(s) => Functor.map(f, Ok(s))
                case None    => Err("not a JsonString")
            }
        )     

    pub def jsonNumberT(f: BigDecimal -> b \ ef): Transform[cx, JsonValue, b] \ ef= 
        KIR.Base.contextFreeT(a -> 
            match InteropJson.JsonValue.getBigDecimal(a) {
                case Some(s) => Functor.map(f, Ok(s))
                case None    => Err("not a JsonNumber")
            }
        ) 


    def jsonArrayT(t: Transform[cx, JsonValue, a], f: (List[a]) -> b \ ef): Transform[cx, JsonArray, b] \ ef = 
        KIR.Base.transform((cx, a) -> {
            let xs = InteropJson.JsonArray.toList(a);
            let ys: Answer[List[a]] = Traversable.traverse(x1 -> 
                                        KIR.Base.applyT(t, cx, x1), xs);
            Result.map(f, ys)
        })


    pub def jsonArrayAllR(t: Rewrite[cx, JsonValue]): Rewrite[cx, JsonArray] = 
        jsonArrayT(t, InteropJson.JsonArray.fromList)

    pub def jsonArrayAnyR(r1: Rewrite[cx, JsonValue]): Rewrite[cx, JsonArray] = 
        KIR.Base.transform((cx, a) -> {
            let xs = InteropJson.JsonArray.toList(a);
            let ys: Answer[List[JsonValue]] = KIR.Base.applyT(KIR.Congruence.anyRTraversable(r1), cx, xs);
            Functor.map(InteropJson.JsonArray.fromList, ys)
        }) 

    pub def jsonArrayOneR(r1: Rewrite[cx, JsonValue]): Rewrite[cx, JsonValue] =
        KIR.Base.transform((cx, a) -> 
            match InteropJson.JsonValue.getJsonArray(a) {
                case Some(arr) => { 
                    let xs = InteropJson.JsonArray.toList(arr);
                    let ys: Answer[List[JsonValue]] = KIR.Base.applyT(KIR.Congruence.oneRTraversable(r1), cx, xs);
                    Functor.map(InteropJson.JsonArray.fromList >> InteropJson.JsonArray.toJsonValue, ys)
                }
                case None      => Err("not a JsonArray")
            }
        )


    pub def jsonObjectT(t: Transform[cx, JsonObjectRow, a], f: List[a] -> b  \ ef): Transform[cx, JsonObject, b] \ ef =
        KIR.Base.transform((cx, a) -> {
            // TODO - get this down to one traversal...
            let xs = InteropJson.JsonObject.toList(a) |> List.map(match (x, y) -> JsonObjectRow.JsonObjectRow(x, y));
            let ys: Answer[List[a]] = Traversable.traverse(x1 -> KIR.Base.applyT(t, cx, x1), xs);
            Result.map(f, ys)
        }) 

    // TODO - too many traversals! ...
    pub def jsonObjectAllR(t: Rewrite[cx, JsonObjectRow]): Rewrite[cx, JsonObject] =
        jsonObjectT(t, List.map(match (JsonObjectRow.JsonObjectRow(k, v)) -> (k, v)) >>  List.toMap >> InteropJson.JsonObject.fromMap)

    pub def jsonObjectAnyR(t: Rewrite[cx, JsonObjectRow]): Rewrite[cx, JsonObject] = ???

    pub def jsonObjectOneR(t: Rewrite[cx, JsonObjectRow]): Rewrite[cx, JsonObject] = ???


}


