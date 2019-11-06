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

module StateMachineModel where

   -----------------------------------------------------------------------------
   -- State Machine
   -----------------------------------------------------------------------------
  record StateMachine {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂)
         : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      initial : Pred State 0ℓ
      enabled : Event → State → Set
      action  : ∀ {preState} {event}
                → enabled event preState
                → State
  open StateMachine


  data Reachable {ℓ₁ ℓ₂} {State : Set ℓ₁} {Event : Set ℓ₂}
                 {sm : StateMachine State Event}
                 : State → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    init : ∀ {sᵢ}
           → initial sm sᵢ
           → Reachable sᵢ
    step : ∀ {preState event}
           → Reachable {sm = sm} preState
           → (enEv : enabled sm event preState)
           → Reachable (action sm enEv)


  Invariant : ∀ {ℓ₁ ℓ₂ ℓ'} {State : Set ℓ₁} {Event : Set ℓ₂}
                (sm : StateMachine State Event) (P : Pred State ℓ')
              → Set (ℓ' ⊔ lsuc (ℓ₁ ⊔ ℓ₂))
  Invariant sm P = ∀ {state} (rs : Reachable {sm = sm} state) → P state

  postulate
    -- TODO : Prove the property
    lemma-Imp→Inv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {State : Set ℓ₁} {Event : Set ℓ₂}
                      (sm : StateMachine State Event)
                      {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                    → P ⊆ Q → Invariant sm (P ⇒ Q)

  EventSet : ∀ {ℓ} {Event : Set ℓ} → Set (lsuc ℓ)
  EventSet {ℓ} {Event} = Event → Set ℓ

  record System {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂)
         : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      stateMachine : StateMachine State Event
      -- Weak fairness is a predicate over EventSets
      weakFairness : Pred (EventSet {Event = Event}) ℓ₂
  open System


  enabledSet : ∀ {ℓ₁ ℓ₂} {State : Set ℓ₁} {Event : Set ℓ₂}
               → StateMachine State Event
               → EventSet {Event = Event} → State → Set ℓ₂
  enabledSet sm evSet state = ∃[ event ] (evSet event × enabled sm event state)



  module LeadsTo
    {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) (sys : System State Event)
    where

   -----------------------------------------------------------------------------
   -- HOARE Triple
   -----------------------------------------------------------------------------
   data [_]_[_] {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (event : Event) (Q : Pred State ℓ₄)
                : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
      hoare : (∀ {preState}
               → P preState
               → (enEv : enabled (stateMachine sys) event preState)
               → Q (action (stateMachine sys) enEv ))
               → [ P ] event [ Q ]


   Z : Set
   Z = ℕ

   -- Auxiliary properties with syntax renaming for better compliance with paper
   -- TODO : Try to make this more generic
   ⋃₁ : ∀ {ℓ} → (Z → Pred State ℓ) → Pred State _
   ⋃₁ P = λ x → Σ[ i ∈ Z ] P i x

   syntax ⋃₁ (λ i → P) = [∃ i ∶ P ]


   ⋃₂ : ∀ {ℓ₁ ℓ₂} → (C : Pred Z ℓ₁) → (F : Z → Pred State ℓ₂) → Pred State _
   ⋃₂ C F = λ s → Σ[ i ∈ Z ] ( C i × F i s )

   syntax ⋃₂ C (λ x → P) = [∃ x ⇒ C ∶ P ]

   -----------------------------------------------------------------------------
   -- PROOF RULES for liveness
   -----------------------------------------------------------------------------
   data _l-t_ {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (Q : Pred State ℓ₄)
              : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
     viaEvSet  : (eventSet : EventSet)
               → (weakFairness sys eventSet)
               → (∀ (e : Event) → eventSet e → [ P ] e [ Q ])
               → (∀ (e : Event) → ¬ (eventSet e) → [ P ] e [ P ∪ Q ])
               → Invariant
                     (stateMachine sys)
                     (P ⇒ enabledSet (stateMachine sys) eventSet)
               → P l-t Q

     viaInv    : Invariant (stateMachine sys) (P ⇒ Q)
               → P l-t Q

     viaTrans  : ∀ {R : Pred State ℓ₄}
               → P l-t R
               → R l-t Q
               → P l-t Q

     viaTrans2 : ∀ {R : Pred State ℓ₄}
               → P l-t (Q ∪ R)
               → R l-t Q
               → P l-t Q

     viaDisj   : ∀ {P₁ P₂ : Pred State ℓ₃}
               -- P = P₁ ∪ P₂ (from the paper)
               → P ⊆ (P₁ ∪ P₂)
               → P₁ l-t Q
               → P₂ l-t Q
               → P  l-t Q

     viaUseInv : ∀ {R : Pred State ℓ₄}
               → Invariant (stateMachine sys) R
               → (P ∩ R) l-t (R ⇒ Q)
               → P l-t Q

     viaWFR    : ∀ (F : Z → Pred State 0ℓ)
               → P l-t (Q ∪ [∃ x ∶ F x ])
               → (∀ (w : Z) → F w l-t (Q ∪ [∃ x ⇒ _< w ∶ F x ]))
               → P l-t Q
