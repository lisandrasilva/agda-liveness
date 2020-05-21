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

{-
             PROCESS 0                   ||             PROCESS 1

    repeat                               ||    repeat
      s₀: thinking₀ = false;             ||      r₀: thinking₁ = false;
      s₁: turn = 1;                      ||      r₁: turn = 0;
      s₂: await thinking₁ ∨ turn ≡ 0;    ||      r₂: await thinking₀ ∨ turn ≡ 1;
            “critical section”;          ||            “critical section”;
      s₃: thinking₀ = true;              ||      r₃: thinking₁ = true;
    forever                              ||    forever

-}
module Examples.Peterson where

  {- Because of the atomicity assumptions, we can view a concurrent program as a
     state transition system. Simply associate with each process a control
     variable that indicates the atomic statement to be executed next by the
     process.
     The state of the program is defined by the values of the data variables and
     control variables.
  -}
  record State : Set where
    field
      -- Data variables : updated in assignemnt statements
      thinking₀ : Bool
      thinking₁ : Bool
      turn      : Fin 2
      -- Control varibales : updated acording to the control flow of the program
      control₀  : Fin 4
      control₁  : Fin 4
  open State

  -- Events : corresponding to the atomic statements
  data MyEvent : Set where
    es₀ : MyEvent
    es₁ : MyEvent
    es₂ : MyEvent
    es₃ : MyEvent
    er₀ : MyEvent
    er₁ : MyEvent
    er₂ : MyEvent
    er₃ : MyEvent

  {- Enabled conditions : predicate on the state variables.
     In any state, an atomic statement can be executed if and only if it is
     pointed to by a control variable and is enabled.
  -}
  MyEnabled : MyEvent → State → Set
  MyEnabled es₀ st = control₀ st ≡ 0F
  MyEnabled es₁ st = control₀ st ≡ 1F
  MyEnabled es₂ st = control₀ st ≡ 2F × (thinking₁ st ≡ true ⊎ turn st ≡ 0F)
  MyEnabled es₃ st = control₀ st ≡ 3F
  MyEnabled er₀ st = control₁ st ≡ 0F
  MyEnabled er₁ st = control₁ st ≡ 1F
  MyEnabled er₂ st = control₁ st ≡ 2F × (thinking₀ st ≡ true ⊎ turn st ≡ 1F)
  MyEnabled er₃ st = control₁ st ≡ 3F


  {- Actions : executing the statement results in a new state.
     Thus each statement execution corresponds to a state transition.
  -}
  MyAction : ∀ {preState} {event} → MyEnabled event preState → State
  -- Process 1
  MyAction {ps} {es₀} x = record ps
                                 { thinking₀ = false -- want to access CS
                                 ; control₀  = 1F    -- next statement
                                 }
  MyAction {ps} {es₁} x = record ps
                                 { turn      = 1F    -- gives turn to other proc
                                 ; control₀  = 2F    -- next stmt
                                 }
  MyAction {ps} {es₂} x = record ps
                                 { control₀  = 3F }  -- next stmt

  MyAction {ps} {es₃} x = record ps
                                 { thinking₀ = true  -- releases the CS
                                 ; control₀  = 0F    -- loop
                                 }
  -- Proccess 2
  MyAction {ps} {er₀} x = record ps
                                 { thinking₁ = false
                                 ; control₁  = 1F
                                 }
  MyAction {ps} {er₁} x = record ps
                                 { turn      = 0F
                                 ; control₁  = 2F
                                 }
  MyAction {ps} {er₂} x = record ps
                                 { control₁  = 3F }

  MyAction {ps} {er₃} x = record ps
                                 { thinking₁ = true
                                 ; control₁  = 0F
                                 }

  initialState : State
  initialState = record
                   { thinking₀ = true
                   ; thinking₁ = true
                   ; turn      = 0F
                   ; control₀  = 0F
                   ; control₁  = 0F
                   }

  MyStateMachine : StateMachine State MyEvent
  MyStateMachine = record
                     { initial = λ state → state ≡ initialState
                     ; enabled = MyEnabled
                     ; action  = MyAction
                     }


  -- Each process has its own EventSet with its statements
  Proc0-EvSet : EventSet {Event = MyEvent}
  Proc0-EvSet ev = ev ≡ es₁ ⊎ ev ≡ es₂ ⊎ ev ≡ es₃

  Proc1-EvSet : EventSet {Event = MyEvent}
  Proc1-EvSet ev = ev ≡ er₁ ⊎ ev ≡ er₂ ⊎ ev ≡ er₃


  -- And both EventSets have weak-fairness
  data MyWeakFairness : EventSet → Set where
    wf-p0 : MyWeakFairness Proc0-EvSet
    wf-p1 : MyWeakFairness Proc1-EvSet


  MySystem : System State MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }


   -----------------------------------------------------------------------------
   -- PROOFS
   -----------------------------------------------------------------------------

  open LeadsTo State MyEvent MySystem

  inv-c₁≡[0-4] : Invariant MyStateMachine λ st → ∃[ f ] (control₁ st ≡ f)-- ([∃ f ∶ (_≡ f) ∘ control₁ ])
  inv-c₁≡[0-4] (init refl) = 0F , refl
  inv-c₁≡[0-4] (step {event = es₀} rs enEv) = inv-c₁≡[0-4] rs
  inv-c₁≡[0-4] (step {event = es₁} rs enEv) = inv-c₁≡[0-4] rs
  inv-c₁≡[0-4] (step {event = es₂} rs enEv) = inv-c₁≡[0-4] rs
  inv-c₁≡[0-4] (step {event = es₃} rs enEv) = inv-c₁≡[0-4] rs
  inv-c₁≡[0-4] (step {event = er₀} rs refl) = 1F , refl
  inv-c₁≡[0-4] (step {event = er₁} rs enEv) = 2F , refl
  inv-c₁≡[0-4] (step {event = er₂} rs enEv) = 3F , refl
  inv-c₁≡[0-4] (step {event = er₃} rs enEv) = 0F , refl


  inv-¬think₁ : Invariant
                  MyStateMachine
                  λ st → control₀ st ≡ 1F ⊎ control₀ st ≡ 2F ⊎ control₀ st ≡ 3F
                       → thinking₀ st ≡ false
  inv-¬think₁ (init refl) (inj₂ (inj₁ ()))
  inv-¬think₁ (init refl) (inj₂ (inj₂ ()))
  inv-¬think₁ (step {event = es₀} rs enEv) x = refl
  inv-¬think₁ (step {event = es₁} rs enEv) x = inv-¬think₁ rs (inj₁ enEv)
  inv-¬think₁ (step {event = es₂} rs enEv) x = inv-¬think₁ rs (inj₂ (inj₁ (fst enEv)))
  inv-¬think₁ (step {event = es₃} rs enEv) (inj₂ (inj₁ ()))
  inv-¬think₁ (step {event = es₃} rs enEv) (inj₂ (inj₂ ()))
  inv-¬think₁ (step {event = er₀} rs enEv) x = inv-¬think₁ rs x
  inv-¬think₁ (step {event = er₁} rs enEv) x = inv-¬think₁ rs x
  inv-¬think₁ (step {event = er₂} rs enEv) x = inv-¬think₁ rs x
  inv-¬think₁ (step {event = er₃} rs enEv) x = inv-¬think₁ rs x


  inv-think₂ : Invariant
                  MyStateMachine
                  λ st → control₁  st ≡ 0F
                       → thinking₁ st ≡ true
  inv-think₂ (init refl) x = refl
  inv-think₂ (step {event = es₀} rs enEv) x = inv-think₂ rs x
  inv-think₂ (step {event = es₁} rs enEv) x = inv-think₂ rs x
  inv-think₂ (step {event = es₂} rs enEv) x = inv-think₂ rs x
  inv-think₂ (step {event = es₃} rs enEv) x = inv-think₂ rs x
  inv-think₂ (step {event = er₃} rs enEv) x = refl


  inv-¬think₂ : Invariant
                  MyStateMachine
                  λ st → control₁ st ≡ 1F ⊎ control₁ st ≡ 2F ⊎ control₁ st ≡ 3F
                       → thinking₁ st ≡ false
  inv-¬think₂ (init refl) (inj₂ (inj₁ ()))
  inv-¬think₂ (init refl) (inj₂ (inj₂ ()))
  inv-¬think₂ (step {event = es₀} rs enEv) x = inv-¬think₂ rs x
  inv-¬think₂ (step {event = es₁} rs enEv) x = inv-¬think₂ rs x
  inv-¬think₂ (step {event = es₂} rs enEv) x = inv-¬think₂ rs x
  inv-¬think₂ (step {event = es₃} rs enEv) x = inv-¬think₂ rs x
  inv-¬think₂ (step {event = er₀} rs enEv) x = refl
  inv-¬think₂ (step {event = er₁} rs enEv) x = inv-¬think₂ rs (inj₁ enEv)
  inv-¬think₂ (step {event = er₂} rs enEv) x = inv-¬think₂ rs (inj₂ (inj₁ (fst enEv)))
  inv-¬think₂ (step {event = er₃} rs enEv) (inj₂ (inj₁ ()))
  inv-¬think₂ (step {event = er₃} rs enEv) (inj₂ (inj₂ ()))




  proc0-1-l-t-2 : (λ preSt → control₀ preSt ≡ 1F)
                  l-t
                  λ posSt →   control₀ posSt ≡ 2F
  proc0-1-l-t-2 =
   viaEvSet
     Proc0-EvSet
     wf-p0
     ( λ { es₁ (inj₁ refl)
               → hoare λ { x enEv → refl }
         ; es₂ (inj₂ (inj₁ refl))
               → hoare λ { refl () }
         ; es₃ (inj₂ (inj₂ refl))
               → hoare λ { refl () }
         }
     )
     ( λ { es₀ x → hoare λ { () refl }
         ; es₁ x → ⊥-elim (x (inj₁ refl))
         ; es₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
         ; es₃ x → ⊥-elim (x (inj₂ (inj₂ refl)))
         ; er₀ x → hoare λ z enEv → inj₁ z
         ; er₁ x → hoare λ z enEv → inj₁ z
         ; er₂ x → hoare λ z enEv → inj₁ z
         ; er₃ x → hoare λ z enEv → inj₁ z
         }
     )
     λ {state} rs x → es₁ , inj₁ refl , x


  P⊆P₀⊎P₁ : ∀ {ℓ} {A : Set ℓ} (x : Fin 2)
            → A → A × x ≡ 0F ⊎ A × x ≡ 1F
  P⊆P₀⊎P₁ 0F a = inj₁ (a , refl)
  P⊆P₀⊎P₁ 1F a = inj₂ (a , refl)


  -- y4

  turn≡0-l-t-Q : ( λ preSt →  control₀ preSt ≡ 2F × turn preSt ≡ 0F )
                   l-t
                   λ posSt → control₀ posSt ≡ 3F
  turn≡0-l-t-Q =
    viaEvSet
      Proc0-EvSet
      wf-p0
      ( λ { es₁ (inj₁ refl)        → hoare λ { () refl }
          ; es₂ (inj₂ (inj₁ refl)) → hoare λ _ _ → refl
          ; es₃ (inj₂ (inj₂ refl)) → hoare λ { () refl }
          }
      )
      ( λ { es₀ x → hoare λ { () refl }
          ; es₁ x → ⊥-elim (x (inj₁ refl))
          ; es₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; es₃ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          ; er₀ x → hoare (λ z enEv → inj₁ z)
          ; er₁ x → hoare (λ z enEv → inj₁ ((fst z) , refl) )
          ; er₂ x → hoare (λ z enEv → inj₁ z)
          ; er₃ x → hoare (λ z enEv → inj₁ z)
          }
      )
      λ {st} rs x → es₂ , (inj₂ (inj₁ refl)) , (fst x) , (inj₂ (snd x))



  -- I think I could prove this with the Proc1EvSet

  Pl-tQ∨c₁≡1 : (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F )
                  × control₁ preSt ≡ 0F)
       l-t
        λ posSt →   control₀ posSt ≡ 3F
                  ⊎ (( control₀ posSt ≡ 2F × turn posSt ≡ 1F )
                     × control₁ posSt ≡ 1F )
  Pl-tQ∨c₁≡1 =
    viaEvSet
      Proc0-EvSet
      wf-p0
      ( λ { es₁ (inj₁ refl) → hoare λ { () refl }
          ; es₂ (inj₂ (inj₁ refl)) → hoare λ { _ _ → inj₁ refl }
          ; es₃ (inj₂ (inj₂ refl)) → hoare λ { () refl }
          }
      )
      ( λ { es₀ x → hoare λ { () refl }
          ; es₁ x → ⊥-elim (x (inj₁ refl))
          ; es₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; es₃ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          ; er₀ x → hoare λ { x₁ enEv → inj₂ (inj₂ (fst x₁ , refl)) }
          ; er₁ x → hoare λ { () refl }
          ; er₂ x → hoare λ { () (refl , _) }
          ; er₃ x → hoare λ { () refl }
          }
      )
      λ rs x → es₂ , inj₂ (inj₁ refl) , fst (fst x) , inj₁ (inv-think₂ rs (snd x))



  l-t-turn≡0 : (λ preSt → ( control₀ preSt ≡ 2F
                  × turn preSt ≡ 1F )
                  × control₁ preSt ≡ 1F)
       l-t
        λ posSt →   control₀ posSt ≡ 2F
                  × turn posSt ≡ 0F
                  --× control₁ posSt ≡ 2F
  l-t-turn≡0 =
    viaUseInv
      inv-¬think₂
      ( viaEvSet
          Proc1-EvSet
          wf-p1
          ( λ { er₁ (inj₁ refl)
                    → hoare λ { ((x , _) , _) _ _ → fst x , refl }
              ; er₂ (inj₂ (inj₁ refl))
                    → hoare λ { () (refl , _) _ }
              ; er₃ (inj₂ (inj₂ refl)) → hoare λ { () refl x₁ }
              }
          )
          ( λ { es₀ x → hoare λ { () refl }
              ; es₁ x → hoare λ { () refl }
              ; es₂ x → hoare λ { ((_ , c₂≡2) , x) (_ , inj₁ refl)
                                      → contradiction (x (inj₁ c₂≡2)) λ ()
                                ; ((() , _) , _) (_ , inj₂ refl) }
              ; es₃ x → hoare λ { () refl }
              ; er₀ x → hoare λ { () refl }
              ; er₁ x → ⊥-elim (x (inj₁ refl))
              ; er₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
              ; er₃ x → ⊥-elim (x (inj₂ (inj₂ refl))) }
          )
          λ rs x → er₁ , (inj₁ refl) , (snd (fst x))
      )



  l-t-c₁≡3 : (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F )
                  × control₁ preSt ≡ 2F)
       l-t
       (λ posSt → ( control₀ posSt ≡ 2F
                  × turn posSt ≡ 1F )
                  × control₁ posSt ≡ 3F)
  l-t-c₁≡3 =
    viaUseInv
      inv-¬think₂
      ( viaEvSet
          Proc1-EvSet
          wf-p1
          ( λ { er₁ (inj₁ refl) → hoare λ { () refl _ }
              ; er₂ (inj₂ (inj₁ refl)) → hoare λ { ((x , _) , _) _ _ → x , refl }
              ; er₃ (inj₂ (inj₂ refl)) → hoare λ { () refl _ }
              }
          )
          ( λ { es₀ x → hoare λ { () refl }
              ; es₁ x → hoare λ { () refl }
              ; es₂ x → hoare λ { ((_ , c₂≡3) , x) (_ , inj₁ refl)
                                      → contradiction (x (inj₂ (inj₁ c₂≡3))) λ ()
                                ; () (_ , inj₂ refl)
                                }
              ; es₃ x → hoare λ { () refl }
              ; er₀ x → hoare λ { () refl }
              ; er₁ x → ⊥-elim (x (inj₁ refl))
              ; er₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
              ; er₃ x → ⊥-elim (x (inj₂ (inj₂ refl)))
              }
          )
          λ {st} rs x → er₂ , inj₂ (inj₁ refl)
                      , (snd (fst x)) , (inj₂ (snd (fst (fst x))))
      )



  l-t-c₁≡0 : (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F )
                  × control₁ preSt ≡ 3F)
       l-t
       (λ posSt → ( control₀ posSt ≡ 2F × turn posSt ≡ 1F )
                  × control₁ posSt ≡ 0F)
  l-t-c₁≡0 =
    viaUseInv
      inv-¬think₂
      ( viaEvSet
          Proc1-EvSet
          wf-p1
          ( λ { er₁ (inj₁ refl)        → hoare λ { () refl _ }
              ; er₂ (inj₂ (inj₁ refl)) → hoare λ { () (refl , _) _ }
              ; er₃ (inj₂ (inj₂ refl)) → hoare λ { x _ _ → (fst (fst x)) , refl }
              }
          )
          ( λ { es₀ x → hoare λ { () refl }
              ; es₁ x → hoare λ { () refl }
              ; es₂ x → hoare λ { ((_ , c₂≡4) , x) (_ , inj₁ refl)
                                      → contradiction (x (inj₂ (inj₂ c₂≡4))) (λ ())
                                ; () (_ , inj₂ refl)
                                }
              ; es₃ x → hoare λ { () refl }
              ; er₀ x → hoare λ { () refl }
              ; er₁ x → ⊥-elim (x (inj₁ refl))
              ; er₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
              ; er₃ x → ⊥-elim (x (inj₂ (inj₂ refl)))
              }
          )
          λ {st} rs x → er₃ , inj₂ (inj₂ refl) , snd (fst x)
      )



  P∧c₁≡1 :  (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F ) × control₁ preSt ≡ 1F)
        l-t
        λ posSt → control₀ posSt ≡ 3F
  P∧c₁≡1 =
    viaTrans
      l-t-turn≡0
      turn≡0-l-t-Q


  P∧c₁≡0 : (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F ) × control₁ preSt ≡ 0F)
           l-t
           λ posSt → control₀ posSt ≡ 3F
  P∧c₁≡0 = viaTrans2 Pl-tQ∨c₁≡1 P∧c₁≡1

  P∧c₁≡3 : (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F )
                  × control₁ preSt ≡ 3F)
        l-t
        λ posSt → control₀ posSt ≡ 3F
  P∧c₁≡3 =
    viaTrans
      l-t-c₁≡0
      P∧c₁≡0

  P∧c₁≡2 : (λ preSt → ( control₀ preSt ≡ 2F × turn preSt ≡ 1F )
                  × control₁ preSt ≡ 2F)
        l-t
        λ posSt → control₀ posSt ≡ 3F
  P∧c₁≡2 =
    viaTrans
      l-t-c₁≡3
      P∧c₁≡3



  P⊆c₂≡r₁⊎c₂≢r₁ : ∀ {ℓ} {A : Set ℓ} (x : Fin 4)
                  → A
                  → A × x ≡ 0F ⊎ A × x ≢ 0F
  P⊆c₂≡r₁⊎c₂≢r₁ 0F a = inj₁ (a , refl)
  P⊆c₂≡r₁⊎c₂≢r₁ (suc x) a = inj₂ (a , (λ ()))


  P⊆c₂≡r₂⊎c₂≢r₂ : ∀ {ℓ} {A : Set ℓ} (x : Fin 4)
                  → A × x ≢ 0F
                  → A × x ≡ 1F ⊎ A × x ≢ 0F × x ≢ 1F
  P⊆c₂≡r₂⊎c₂≢r₂ 0F (a , x≢0) = ⊥-elim (x≢0 refl)
  P⊆c₂≡r₂⊎c₂≢r₂ 1F (a , x≢0) = inj₁ (a , refl)
  P⊆c₂≡r₂⊎c₂≢r₂ (suc (suc x)) (a , x≢0) = inj₂ (a , x≢0 , λ ())


  P⊆c₂≡r₃⊎c₂≡r₄ : ∀ {ℓ} {A : Set ℓ} (x : Fin 4)
                  → A × x ≢ 0F × x ≢ 1F
                  → A × x ≡ 2F ⊎ A × x ≡ 3F
  P⊆c₂≡r₃⊎c₂≡r₄ 0F (a , x≢0 , x≢1) = ⊥-elim (x≢0 refl)
  P⊆c₂≡r₃⊎c₂≡r₄ 1F (a , x≢0 , x≢1) = ⊥-elim (x≢1 refl)
  P⊆c₂≡r₃⊎c₂≡r₄ 2F (a , x≢0 , x≢1) = inj₁ (a , refl)
  P⊆c₂≡r₃⊎c₂≡r₄ 3F (a , x≢0 , x≢1) = inj₂ (a , refl)



  turn≡1-l-t-Q : ( λ preSt →  control₀ preSt ≡ 2F
                              × turn preSt ≡ 1F )
                   l-t
                   λ posSt → control₀ posSt ≡ 3F
  turn≡1-l-t-Q =
    viaAllVal
      inv-c₁≡[0-4]
      λ { 0F → P∧c₁≡0
        ; 1F → P∧c₁≡1
        ; 2F → P∧c₁≡2
        ; 3F → P∧c₁≡3 }


  proc0-2-l-t-3 : ( λ preSt →  control₀ preSt ≡ 2F )
                  l-t
                   λ posSt → control₀ posSt ≡ 3F
  proc0-2-l-t-3 =
    viaDisj
      (λ {st} c₀≡2 → P⊆P₀⊎P₁ (turn st) c₀≡2 )
      turn≡0-l-t-Q
      turn≡1-l-t-Q


  proc1-1-l-t-2 : (λ preSt → control₁ preSt ≡ 1F)
                  l-t
                  λ posSt →   control₁ posSt ≡ 2F
  proc1-1-l-t-2 =
    viaEvSet
      Proc1-EvSet
      wf-p1
      ( λ { er₁ (inj₁ refl) → hoare λ { x enEv → refl }
          ; er₂ (inj₂ (inj₁ refl)) → hoare λ { refl () }
          ; er₃ (inj₂ (inj₂ refl)) → hoare λ { refl () }
          }
      )
      ( λ { es₀ x → hoare λ z enEv → inj₁ z
          ; es₁ x → hoare λ z enEv → inj₁ z
          ; es₂ x → hoare λ z enEv → inj₁ z
          ; es₃ x → hoare λ z enEv → inj₁ z
          ; er₀ x → hoare λ z enEv → inj₁ refl
          ; er₁ x → ⊥-elim (x (inj₁ refl))
          ; er₂ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; er₃ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          }
      )
      λ {state} rs x → er₁ , inj₁ refl , x


  -- The proofs are the same as proc0-2-l-t-3 but symmetric.
  -- We will postulate by now!
  postulate
    proc1-2-l-t-3 : ( λ preSt →  control₁ preSt ≡ 2F )
                     l-t
                     λ posSt → control₁ posSt ≡ 3F


  -- We proved this via transitivity :
  -- control₀ fstSt ≡ 1F   l-t   control₀ someSt ≡ 2F   l-t   control₀ ≡ 3F
  proc0-live : (λ preSt → control₀ preSt ≡ 1F) l-t (λ posSt → control₀ posSt ≡ 3F)
  proc0-live = viaTrans proc0-1-l-t-2 proc0-2-l-t-3


  proc1-live : (λ preSt → control₁ preSt ≡ 1F) l-t (λ posSt → control₁ posSt ≡ 3F)
  proc1-live = viaTrans proc1-1-l-t-2 proc1-2-l-t-3


  ------------------------------------------------------------------------------
   -- Liveness property
  ------------------------------------------------------------------------------
  --   If Process 1 (Process 2) wants to access the critical section, which
  --   means its control variable is in 1F (it just expressed its will in
  --   accessing the CS in r₀) then it will eventually access the CS
  progress : ( (_≡ 1F) ∘ control₀ l-t (_≡ 3F) ∘ control₀ )
           × ( (_≡ 1F) ∘ control₁ l-t (_≡ 3F) ∘ control₁ )
  progress = proc0-live , proc1-live

