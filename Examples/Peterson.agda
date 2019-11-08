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

open import StateMachineModel

-- TODO : Add documentation about the model according to the paper
module Examples.Peterson where

  record State : Set where
    field
      thinking₁ : Bool
      thinking₂ : Bool
      turn      : Fin 2
      control₁  : Fin 4
      control₂  : Fin 4
  open State

  data MyEvent : Set where
    es₁ : MyEvent
    es₂ : MyEvent
    es₃ : MyEvent
    es₄ : MyEvent
    er₁ : MyEvent
    er₂ : MyEvent
    er₃ : MyEvent
    er₄ : MyEvent

  {-
  data MyEnabled (st : State) : MyEvent → Set where
    ees₁ : control₁ st ≡ 1 → MyEnabled st es₁
    ees₂ : control₁ st ≡ 2 → MyEnabled st es₂
    ees₃ : control₁ st ≡ 3 → MyEnabled st es₃
    ees₄ : control₁ st ≡ 4 → MyEnabled st es₄
  -}

  MyEnabled : MyEvent → State → Set
  MyEnabled es₁ st = control₁ st ≡ 0F
  MyEnabled es₂ st = control₁ st ≡ 1F
  MyEnabled es₃ st = control₁ st ≡ 2F × (thinking₂ st ≡ true ⊎ turn st ≡ 0F)
  MyEnabled es₄ st = control₁ st ≡ 3F
  MyEnabled er₁ st = control₂ st ≡ 0F
  MyEnabled er₂ st = control₂ st ≡ 1F
  MyEnabled er₃ st = control₂ st ≡ 2F × (thinking₁ st ≡ true ⊎ turn st ≡ 0F)
  MyEnabled er₄ st = control₂ st ≡ 3F



  MyAction : ∀ {preState} {event} → MyEnabled event preState → State
  MyAction {ps} {es₁} x = record
                            { thinking₁ = false
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 1F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₂} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = 1F
                            ; control₁  = 2F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₃} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 3F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₄} x = record
                            { thinking₁ = true
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 0F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {er₁} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = false
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 1F
                            }
  MyAction {ps} {er₂} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = 0F
                            ; control₁  = control₁ ps
                            ; control₂  = 2F
                            }
  MyAction {ps} {er₃} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 3F
                            }
  MyAction {ps} {er₄} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = true
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 0F
                            }

  initialState : State
  initialState = record
                   { thinking₁ = true
                   ; thinking₂ = true
                   ; turn      = 0F
                   ; control₁  = 0F
                   ; control₂  = 0F
                   }

  MyStateMachine : StateMachine State MyEvent
  MyStateMachine = record
                     { initial = λ state → state ≡ initialState
                     ; enabled = MyEnabled
                     ; action  = MyAction
                     }


  -- Each process has its own EventSet with its statements
  Proc1-EvSet : EventSet {Event = MyEvent}
  Proc1-EvSet x = x ≡ es₂ ⊎ x ≡ es₃ ⊎ x ≡ es₄

  Proc2-EvSet : EventSet {Event = MyEvent}
  Proc2-EvSet x = x ≡ er₂ ⊎ x ≡ er₃ ⊎ x ≡ er₄

  -- And both EventSets have weak-fairness
  data MyWeakFairness : EventSet → Set where
    wf-p1 : MyWeakFairness Proc1-EvSet
    wf-p2 : MyWeakFairness Proc2-EvSet


  MySystem : System State MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }


   -----------------------------------------------------------------------------
   -- PROOFS
   -----------------------------------------------------------------------------

  open LeadsTo State MyEvent MySystem

  P⊆P₁⊎P₂ : ∀ st → control₁ st ≡ 2F
                 → control₁ st ≡ 2F ×   (thinking₂ st ≡ true ⊎ turn st ≡ 0F)
                 ⊎ control₁ st ≡ 2F × ¬ thinking₂ st ≡ true × ¬ turn st ≡ 0F
  P⊆P₁⊎P₂ st c₁≡3
    with thinking₂ st B≟ true
  ... | yes prf = inj₁ (c₁≡3 , (inj₁ prf))
  ... | no imp₁
      with turn st F≟ 0F
  ... | yes prf = inj₁ (c₁≡3 , inj₂ prf)
  ... | no imp₂ = inj₂ (c₁≡3 , imp₁ , imp₂)


  proc1-2-l-t-3 : (λ preSt → control₁ preSt ≡ 1F)
                  l-t
                  (λ posSt → control₁ posSt ≡ 2F)
  proc1-2-l-t-3 =
    viaEvSet
      Proc1-EvSet
      wf-p1
      ( λ { es₂ (inj₁ refl)        → hoare λ { _ _ → refl }
          ; es₃ (inj₂ (inj₁ refl)) → hoare λ { refl () }
          ; es₄ (inj₂ (inj₂ refl)) → hoare λ { refl () }
          }
      )
      ( λ { es₁ x → hoare λ { refl () } -- The event is not enabled
          ; es₂ x → ⊥-elim (x (inj₁ refl))
          ; es₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; es₄ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          -- All the events of proc 2 don't interfere with the control variable
          -- in proc 1, so [ P ] e [ P ∪ Q ] holds because [ P ] e [ P ] holds
          ; er₁ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; er₂ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; er₃ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; er₄ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          }
      )
      λ rs c₁≡2 → es₂ , inj₁ refl , c₁≡2


  inv-c₁≡3⇒enabled : Invariant MyStateMachine
                               ( ( λ preSt → control₁ preSt ≡ 2F )
                              ⇒   enabledSet MyStateMachine Proc1-EvSet )
  inv-c₁≡3⇒enabled (init refl) ()
  inv-c₁≡3⇒enabled (step {pSt} {es₂} rs enEv) x = {!!}
  inv-c₁≡3⇒enabled (step {pSt} {er₁} rs enEv) x = {!!}
  inv-c₁≡3⇒enabled (step {pSt} {er₂} rs enEv) x = {!!}
  inv-c₁≡3⇒enabled (step {pSt} {er₃} rs enEv) x = {!!}
  inv-c₁≡3⇒enabled (step {pSt} {er₄} rs enEv) x = {!!}


  proc1-3-l-t-4 : (λ preSt → control₁ preSt ≡ 2F)
                  l-t
                  (λ posSt → control₁ posSt ≡ 3F)
  proc1-3-l-t-4 =
    viaEvSet
      Proc1-EvSet
      wf-p1
      ( λ { es₂ (inj₁ refl)        → hoare λ { refl () }
          ; es₃ (inj₂ (inj₁ refl)) → hoare λ { _ _ → refl }
          ; es₄ (inj₂ (inj₂ refl)) → hoare λ { refl () }
          }
      )
      ( λ { es₁ x → hoare λ { refl () }
          ; es₂ x → ⊥-elim (x (inj₁ refl))
          ; es₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; es₄ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          ; er₁ x → hoare λ c₁≡3 enEv → inj₁ c₁≡3
          ; er₂ x → hoare λ c₁≡3 enEv → inj₁ c₁≡3
          ; er₃ x → hoare λ c₁≡3 enEv → inj₁ c₁≡3
          ; er₄ x → hoare λ c₁≡3 enEv → inj₁ c₁≡3 }
      )
      {!!}



  proc2-2-l-t-3 : (λ preSt → control₂ preSt ≡ 1F)
                  l-t
                  (λ posSt → control₂ posSt ≡ 2F)
  proc2-2-l-t-3 =
    viaEvSet
      Proc2-EvSet
      wf-p2
      ( λ { er₂ (inj₁ refl)        → hoare λ { _ _ → refl }
          ; er₃ (inj₂ (inj₁ refl)) → hoare λ { refl () }
          ; er₄ (inj₂ (inj₂ refl)) → hoare λ { refl () }
          }
      )
      ((λ { -- All the events of proc 1 don't interfere with the control
            -- variable in proc 2, so [ P ] e [ P ∪ Q ] holds because
            -- [ P ] e [ P ] holds
            es₁ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; es₂ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; es₃ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; es₄ x → hoare λ c₁≡2 enEv → inj₁ c₁≡2
          ; er₁ x → hoare λ { refl () } -- The event is not enabled
          ; er₂ x → ⊥-elim (x (inj₁ refl))
          ; er₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; er₄ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          }
      ))
      λ rs c₂≡2 → er₂ , inj₁ refl , c₂≡2




  proc2-3-l-t-4 : (λ preSt → control₂ preSt ≡ 2F)
                  l-t
                  (λ posSt → control₂ posSt ≡ 3F)
  proc2-3-l-t-4 = {!!}


  proc1-live : (λ preSt → control₁ preSt ≡ 1F) l-t (λ posSt → control₁ posSt ≡ 3F)
  proc1-live = viaTrans proc1-2-l-t-3 proc1-3-l-t-4

  proc2-live : (λ preSt → control₂ preSt ≡ 1F) l-t (λ posSt → control₂ posSt ≡ 3F)
  proc2-live = viaTrans proc2-2-l-t-3 proc2-3-l-t-4

  progress : (λ preSt → control₁ preSt ≡ 1F) l-t (λ posSt → control₁ posSt ≡ 3F)
           × (λ preSt → control₂ preSt ≡ 1F) l-t (λ posSt → control₂ posSt ≡ 3F)
  progress = proc1-live , proc2-live
