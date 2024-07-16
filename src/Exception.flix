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

mod FlixKure.Exception {

    pub eff Exn {
        pub def throws(x: String): Void
    }


    ///
    ///
    pub def catchExn(f: Unit -> a \ ef + Exn, handler: String -> a): a \ ef = 
        try f() with Exn {
            def throws(s, _) = checked_ecast(handler(s))
        }

    ///
    ///
    pub def exnHandler(f: Unit -> a \ ef + Exn): Result[String, a] \ ef = 
        try { 
            let x = f();
            Ok(x) 
        } with Exn {
            def throws(s, _) = checked_ecast(Err(s))
        }

}

