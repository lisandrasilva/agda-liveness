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
open import Data.Bool

open import StateMachineModel

-- TODO : Add documentation about the model according to the paper
module Examples.Peterson where

  record State : Set where
    field
      thinking₁ : Bool
      thinking₂ : Bool
      turn      : ℕ
      control₁  : ℕ
      control₂  : ℕ
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
  MyEnabled es₁ st = control₁ st ≡ 1
  MyEnabled es₂ st = control₁ st ≡ 2
  MyEnabled es₃ st = control₁ st ≡ 3 × (thinking₂ st ≡ true ⊎ turn st ≡ 1)
  MyEnabled es₄ st = control₁ st ≡ 4
  MyEnabled er₁ st = control₂ st ≡ 1
  MyEnabled er₂ st = control₂ st ≡ 2
  MyEnabled er₃ st = control₂ st ≡ 3 × (thinking₁ st ≡ true ⊎ turn st ≡ 1)
  MyEnabled er₄ st = control₂ st ≡ 4



  MyAction : ∀ {preState} {event} → MyEnabled event preState → State
  MyAction {ps} {es₁} x = record
                            { thinking₁ = false
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 2
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₂} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = 2
                            ; control₁  = 3
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₃} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 4
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₄} x = record
                            { thinking₁ = true
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 1
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {er₁} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = false
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 2
                            }
  MyAction {ps} {er₂} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = 1
                            ; control₁  = control₁ ps
                            ; control₂  = 3
                            }
  MyAction {ps} {er₃} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 4
                            }
  MyAction {ps} {er₄} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = true
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 1
                            }

  initialState : State
  initialState = record
                   { thinking₁ = true
                   ; thinking₂ = true
                   ; turn      = 1
                   ; control₁  = 1
                   ; control₂  = 1
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

  --myWFR : ∀ {m} → State → Z → Set

  proc1-2-l-t-3 : (λ preSt → control₁ preSt ≡ 2)
                  l-t
                  (λ posSt → control₁ posSt ≡ 3)
  proc1-2-l-t-3 =
    viaEvSet
      Proc1-EvSet
      wf-p1
      (λ { es₂ (inj₁ refl)
           → {!!}
         ; es₃ (inj₂ (inj₁ refl))
           → {!!}
         ; es₄ (inj₂ (inj₂ refl))
           → {!!} })
      {!!}
      {!!}

  proc1-3-l-t-4 : (λ preSt → control₁ preSt ≡ 3)
                  l-t
                  (λ posSt → control₁ posSt ≡ 4)
  proc1-3-l-t-4 = {!!}



  proc2-2-l-t-3 : (λ preSt → control₂ preSt ≡ 2)
                  l-t
                  (λ posSt → control₂ posSt ≡ 3)
  proc2-2-l-t-3 =
    viaEvSet
      Proc2-EvSet
      wf-p2
      (λ { er₂ (inj₁ refl)
           → {!!}
         ; er₃ (inj₂ (inj₁ refl))
           → {!!}
         ; er₄ (inj₂ (inj₂ refl))
           → {!!} })
      {!!}
      {!!}

  proc2-3-l-t-4 : (λ preSt → control₂ preSt ≡ 3)
                  l-t
                  (λ posSt → control₂ posSt ≡ 4)
  proc2-3-l-t-4 = {!!}


  proc1-live : (λ preSt → control₁ preSt ≡ 2) l-t (λ posSt → control₁ posSt ≡ 4)
  proc1-live = viaTrans proc1-2-l-t-3 proc1-3-l-t-4

  proc2-live : (λ preSt → control₂ preSt ≡ 2) l-t (λ posSt → control₂ posSt ≡ 4)
  proc2-live = viaTrans proc2-2-l-t-3 proc2-3-l-t-4

  progress : (λ preSt → control₁ preSt ≡ 2) l-t (λ posSt → control₁ posSt ≡ 4)
           × (λ preSt → control₂ preSt ≡ 2) l-t (λ posSt → control₂ posSt ≡ 4)
  progress = proc1-live , proc2-live
