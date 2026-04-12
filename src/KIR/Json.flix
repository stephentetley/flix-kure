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

    use KIR.Base.{Transform, Rewrite, Answer}

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject


    // Congruence combinators (to be moved out of the library at some point)

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


    def jsonArrayT(t: Transform[cx, JsonValue, a], f: (List[a]) -> b \ ef): Transform[cx, JsonValue, b] \ ef = 
        KIR.Base.transform((cx, a) -> 
            match InteropJson.JsonValue.getJsonArray(a) {
                case Some(arr) => { 
                    let xs = InteropJson.JsonArray.toList(arr);
                    let ys: Answer[List[a]] = Traversable.traverse(x1 -> KIR.Base.applyT(t, cx, x1), xs);
                    Result.map(f, ys)
                }
                case None      => Err("not a JsonArray")
            }
        )   


    pub def jsonArrayAllR(t: Rewrite[cx, JsonValue]): Rewrite[cx, JsonValue] = 
        jsonArrayT(t, InteropJson.JsonArray.fromList >> InteropJson.JsonArray.toJsonValue)

    pub def jsonArrayAnyR(r1: Rewrite[cx, JsonValue]): Rewrite[cx, JsonValue] = 
        KIR.Base.transform((cx, a) -> 
            match InteropJson.JsonValue.getJsonArray(a) {
                case Some(arr) => { 
                    let xs = InteropJson.JsonArray.toList(arr);
                    let ys: Answer[List[JsonValue]] = KIR.Base.applyT(KIR.Congruence.anyRTraversable(r1), cx, xs);
                    Functor.map(InteropJson.JsonArray.fromList >> InteropJson.JsonArray.toJsonValue, ys)
                }
                case None      => Err("not a JsonArray")
            }
        ) 

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


    pub enum JsonObjectRow{
        case JsonObjectRow(String, JsonValue)
    }

    pub def jsonObjectT(t: Transform[cx, JsonObjectRow, a], f: List[a] -> b  \ ef): Transform[cx, JsonValue, b] \ ef =
        KIR.Base.transform((cx, a) -> 
            match InteropJson.JsonValue.getJsonObject(a) {
                case Some(obj) => { 
                    // TODO - get this down to one traversal...
                    let xs = InteropJson.JsonObject.toList(obj) |> List.map(match (x, y) -> JsonObjectRow.JsonObjectRow(x, y));
                    let ys: Answer[List[a]] = Traversable.traverse(x1 -> KIR.Base.applyT(t, cx, x1), xs);
                    Result.map(f, ys)
                }
                case None      => Err("not a JsonObject")
            }
        ) 

    // TODO - too many traversals! ...
    pub def jsonObjectAllR(t: Rewrite[cx, JsonObjectRow]): Rewrite[cx, JsonValue] =
        jsonObjectT(t, List.map(match (JsonObjectRow.JsonObjectRow(k, v)) -> (k, v)) >>  List.toMap >> InteropJson.JsonObject.fromMap >> InteropJson.JsonObject.toJsonValue)

    pub def jsonObjectAnyR(t: Rewrite[cx, JsonObjectRow]): Rewrite[cx, JsonValue] = ???

    pub def jsonObjectOneR(t: Rewrite[cx, JsonObjectRow]): Rewrite[cx, JsonValue] = ???


}


