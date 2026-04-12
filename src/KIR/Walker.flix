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

    use KIR.Base.{Transform, Rewrite, Answer}

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject

    pub trait Walker[u] {
        type Context[u]: Type

        pub def allR(t: Rewrite[Walker.Context[u], u]): Rewrite[Walker.Context[u], u] 

        pub def anyR(t: Rewrite[Walker.Context[u], u]): Rewrite[Walker.Context[u], u]
        
        pub def oneR(t: Rewrite[Walker.Context[u], u]): Rewrite[Walker.Context[u], u]

        pub def allT(t: Transform[Walker.Context[u], u, b]): Transform[Walker.Context[u], u, b] with Monoid[b]

        pub def oneT(t: Transform[Walker.Context[u], u, b]): Transform[Walker.Context[u], u, b]
        
    }





}


