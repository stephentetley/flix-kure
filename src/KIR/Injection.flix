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

    use KIR.Base.{Answer, Rewrite, Transform}

    use InteropJson.JsonValue
    use InteropJson.JsonArray
    use InteropJson.JsonObject

    pub trait Injection[a] {
        type Universe[a]: Type

        pub def inj(a: a): Injection.Universe[a]

        pub def proj(u: Injection.Universe[a]): Option[a]
    }


    pub def injectT(): Transform[cx, a, u] with Injection[a] where Injection.Universe[a] ~ u = 
        KIR.Base.arrT(Injection.inj)

    def projectWithFailMsgHelper(msg: String, u: u): Answer[a] with Injection[a] where Injection.Universe[a] ~ u = 
        match Injection.proj(u) {
            case None => Err(msg)
            case Some(ans) => Ok(ans)
        }

    pub def projectWithFailMsgT(msg: String): Transform[cx, u, a] with Injection[a] where Injection.Universe[a] ~ u =  
        KIR.Base.contextFreeT(u -> projectWithFailMsgHelper(msg, u))


    pub def projectT(): Transform[cx, u, a] with Injection[a] where Injection.Universe[a] ~ u = 
        projectWithFailMsgT("projectT failed")

    pub def extractT(t: Transform[cx, u, b]): Transform[cx, a, b] with Injection[a] where Injection.Universe[a] ~ u = 
        KIR.Base.composeLeftT(injectT(), t)

    pub def promoteT(t: Transform[cx, a, b]): Transform[cx, u, b] with Injection[a] where Injection.Universe[a] ~ u = 
        KIR.Base.composeLeftT(projectT(), t)

    pub def promoteR(r: Rewrite[cx, a]): Rewrite[cx, u] with Injection[a] where Injection.Universe[a] ~ u = 
        KIR.Base.composeLeftT(
            KIR.Base.composeLeftT(projectT(), r),
            injectT()
        )

}


