/*
 * Copyright 2024 Stephen Tetley
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

mod FlixKure.Walker {

    use FlixKure.Exception.Exn
    use FlixKure.Transform.{Rewrite, Transform}

    trait Walker[a] {
        pub type Context: Type

        pub type Out: Type

        pub type Eff: Eff

        pub def allR(w: Rewrite[Walker.Context[a], a, Walker.Eff[a] + Exn]): Rewrite[Walker.Context[a], a, Walker.Eff[a] + Exn]

        pub def allT(w: Transform[Walker.Context[a], a, b, Walker.Eff[a] + Exn]): Transform[Walker.Context[a], a, b, Walker.Eff[a] + Exn] with Monoid[b] where Walker.Out[a] ~ b

        pub def oneT(w: Transform[Walker.Context[a], a, b, Walker.Eff[a] + Exn]): Transform[Walker.Context[a], a, b, Walker.Eff[a] + Exn] where Walker.Out[a] ~ b

        pub def anyR(w: Rewrite[Walker.Context[a], a, Walker.Eff[a] + Exn]): Rewrite[Walker.Context[a], a, Walker.Eff[a] + Exn]

        pub def oneR(w: Rewrite[Walker.Context[a], a, Walker.Eff[a] + Exn]): Rewrite[Walker.Context[a], a, Walker.Eff[a] + Exn]

    }


}

