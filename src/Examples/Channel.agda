{-
  Copyright 2019 Lisandra Silva

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-}

open import Prelude
open import Data.Bool renaming (_≟_ to _B≟_)
open import Data.Fin renaming (_≟_ to _F≟_)
open import Agda.Builtin.Sigma
open import Relation.Nullary.Negation using (contradiction ; contraposition)



open import StateMachineModel


{- 2 Nodes
  State Variables:
    sendedMsg : Bool
    ack₁, ack₂ : Bool
    timeout₁, timeout₂ : ℕ
    clock₁, clock₂ : ℕ
-}


{-
       NODE 1                             ||             NODE 2

   s₀: sendedMsg = true                   ||  r₀: if(sendedMsg)
   s₁: ack₁ = false                       ||  r₁:   ack₁ = true
   s₂: while(!ack₁)                       ||  r₂:   ack₂ = false
   s₃:   clock₁ = 0                       ||  r₃: while(!ack₂)
   s₄:   while(!ack₁ ∧ clock₁ < timeout₁) ||  r₄:   clock₂ = 0
   s₅:      clock₁++                      ||  r₅:   while(!ack₂ ∧ clock₂ < timeout₂)
   s₆:   if(clock₁ == timeout₁)           ||  r₆:      clock₂++
   s₇:      timeout₁++                    ||  r₇:   if(clock₂ == timeout₂)
   s₈: ack₂ = true                        ||  r₈:      timeout₂++

-}



module Examples.Channel
  {ℓ : Level}
  (Message : Set ℓ) -- Message type
  where


  -----------------------------------------------------------------------------
  -- SPECIFICATION
  -----------------------------------------------------------------------------
  record State : Set (lsuc ℓ) where
    field
     -- Data variables : updated in assignemnt statements
     senderMsg : Bool
     ack₁ ack₂ : Bool
     timeout₁ timeout₂ : ℕ
     clock₁ clock₂ : ℕ

  -- Control variables : updated acording to the control flow of the program
     control₁ control₂ : Fin 8
  open State
