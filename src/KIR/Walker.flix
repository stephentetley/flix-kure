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


mod KIR.Walker {

    use KIR.Base.{Transform, Rewrite}

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject

    pub trait Walker[a] {
        type Context[a]: Type

        pub def allR(t: Rewrite[Walker.Context[a], a]): Rewrite[Walker.Context[a], a] 
        
    }

    instance Walker[JsonArray] {
        type Context[JsonArray] = Unit

        pub def allR(t: Rewrite[Unit, JsonArray]): Rewrite[Unit, JsonArray] = ???
        
    }

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
                case None    => Err("not a JsomnNull")
            }
        )     

    pub def jsonNumberT(f: BigDecimal -> b \ ef): Transform[cx, JsonValue, b] \ ef= 
        KIR.Base.contextFreeT(a -> 
            match InteropJson.JsonValue.getBigDecimal(a) {
                case Some(s) => Functor.map(f, Ok(s))
                case None    => Err("not a JsomnNull")
            }
        )   


}


