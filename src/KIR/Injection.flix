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


mod KIR.Injection {

    use KIR.Base.{Transform}

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject

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

    pub def injectT(): Transform[cx, a, u] with Injection[a] where Injection.Universe[a] ~ u = 
        KIR.Base.arrT(Injection.inj)


}


