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
open import Data.Bool renaming (_≟_ to _B≟_) hiding (_<_)
open import Data.Fin renaming (_≟_ to _F≟_)  hiding (_<_; _+_)
open import Agda.Builtin.Sigma
open import Relation.Nullary.Negation using (contradiction ; contraposition)



open import StateMachineModel

{-
       NODE 1                             ||             NODE 2

   s₀: sendedMsg = true                   ||  r₀: if(sendedMsg)
       ack₁ = false                       ||        ack₁ = true
       do {                               ||        ack₂ = false
   s₁:   clock₁ = 0                       ||      do {
         while(!ack₁ ∧ clock₁ < timeout₁) ||  r₁:   clock₂ = 0
   s₂:      clock₁++                      ||        while(!ack₂ ∧ clock₂ < timeout₂)
   s₃:    } while(!ack₁)                  ||  r₂:      clock₂++
       ack₂ = true                        ||  r₃:    } while(!ack₂)
-}


module Examples.Channel
  {ℓ : Level}
  (Message : Set ℓ) -- Message type
  (timeoutᵢ : ℕ)
  where


  -----------------------------------------------------------------------------
  -- SPECIFICATION
  -----------------------------------------------------------------------------
  record State : Set (lsuc ℓ) where
    field
     -- Data variables : updated in assignemnt statements
     sendedMsg         : Bool
     ack₁ ack₂         : Bool
     timeout₁ timeout₂ : ℕ
     clock₁ clock₂     : ℕ

  -- Control variables : updated acording to the control flow of the program
     ctl₁ ctl₂ : Fin 4
  open State


  -- Events : corresponding to the atomic statements
  data MyEvent : Set where
    sendMsg    : MyEvent
    sendAck₁   : MyEvent
    resetClock : MyEvent
    incClock   : MyEvent
    goToLoop   : MyEvent
    sendAck₂   : MyEvent



  -- Enabled conditions : predicate on the state variables.
  -- In any state, an atomic statement can be executed if and only if it is
  -- pointed to by a control variable and is enabled.
  MyEnabled : MyEvent → State → Set
  MyEnabled sendMsg st    = ctl₁ st ≡ 0F
  MyEnabled sendAck₁ st   = ctl₂ st ≡ 0F × sendedMsg st ≡ true
  MyEnabled resetClock st = ctl₁ st ≡ 1F ⊎ ctl₂ st ≡ 1F
  MyEnabled incClock st   = (ctl₁ st ≡ 2F × ack₁ st ≡ false × clock₁ st < timeout₁ st) ⊎
                            (ctl₂ st ≡ 2F × ack₂ st ≡ false × clock₂ st < timeout₂ st)
  MyEnabled goToLoop st   = (ack₁ st ≡ false × clock₁ st ≡ timeout₁ st) ⊎
                            (ack₂ st ≡ false × clock₂ st ≡ timeout₂ st)
  MyEnabled sendAck₂ st   = ack₁ st ≡ true



  -- Actions : executing the statement results in a new state.
  -- Thus each statement execution corresponds to a state transition.
  MyAction : ∀ {preSt} {event} → MyEnabled event preSt → State
  MyAction {ps} {sendMsg}    x = record ps
                                   { sendedMsg = true
                                   ; ack₁ = false
                                   ; ctl₁ = 1F
                                   }
  MyAction {ps} {sendAck₁}   x = record ps
                                   { ack₁ = true
                                   ; ack₂ = false
                                   ; ctl₂ = 1F
                                   }
  MyAction {ps} {resetClock} (inj₁ n1) = record ps
                                             { clock₁ = 0
                                             ; ctl₁ = 2F
                                             }
  MyAction {ps} {resetClock} (inj₂ n2) = record ps
                                             { clock₂ = 0
                                             ; ctl₂ = 2F
                                             }
  MyAction {ps} {incClock} (inj₁ n1) = record ps { clock₁ = clock₁ ps + 1}
  MyAction {ps} {incClock} (inj₂ n2) = record ps { clock₂ = clock₂ ps + 1}
  MyAction {ps} {goToLoop} (inj₁ n1) = record ps { ctl₁ = 1F}
  MyAction {ps} {goToLoop} (inj₂ n2) = record ps { ctl₂ = 1F}
  MyAction {ps} {sendAck₂}   x = record ps { ack₂ = true}



  initialState : State
  initialState = record
                   { sendedMsg = false
                   ; ack₁ = false
                   ; ack₂ = false
                   ; timeout₁ = timeoutᵢ
                   ; timeout₂ = timeoutᵢ
                   ; clock₁ = 0
                   ; clock₂ = 0
                   ; ctl₁ = 0F
                   ; ctl₂ = 0F
                   }


  MyStateMachine : StateMachine State MyEvent
  MyStateMachine = record
                     { initial = λ state → state ≡ initialState
                     ; enabled = MyEnabled
                     ; action  = MyAction
                     }

  MyEventSet : EventSet {Event = MyEvent}
  MyEventSet ev = ev ≡ sendAck₁ ⊎ ev ≡ sendAck₂


  data MyWeakFairness : EventSet → Set where
    wf : MyWeakFairness MyEventSet


  MySystem : System State MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }



   -----------------------------------------------------------------------------
   -- PROOFS
   -----------------------------------------------------------------------------

  open LeadsTo State MyEvent MySystem


  P⊆P₁⊎P₂ : ∀ {ℓ} {A : Set ℓ} (x : Bool)
            → A → A × x ≡ true ⊎ A × x ≡ false
  P⊆P₁⊎P₂ false x = inj₂ (x , refl)
  P⊆P₁⊎P₂ true x = inj₁ (x , refl)


  inv-ack₁ : Invariant MyStateMachine
                       (((_≡ true) ∘ sendedMsg ∩ (_≡ true) ∘ ack₁)
                         ⇒ ((_≡ true) ∘ sendedMsg ∩ (_≡ true) ∘ ack₁))

  !ack₁-l-t-ack₁ : ((_≡ true) ∘ sendedMsg ∩ (_≡ false) ∘ ack₁)
                   l-t
                   ((_≡ true) ∘ sendedMsg ∩ (_≡ true) ∘ ack₁)


  progressOnSendAck₂ : ((_≡ true) ∘ sendedMsg ∩ (_≡ true) ∘ ack₁)
                       l-t
                        (_≡ true) ∘ ack₁ ∩ (_≡ true) ∘ ack₂



  syncronization : ((_≡ true) ∘ sendedMsg) l-t (_≡ true) ∘ ack₁ ∩ (_≡ true) ∘ ack₂
  syncronization = viaTrans
                     (viaDisj (λ {st} x → P⊆P₁⊎P₂ (ack₁ st) x)
                              (viaInv inv-ack₁)
                              !ack₁-l-t-ack₁)
                     progressOnSendAck₂


