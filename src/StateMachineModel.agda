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
      enabled : Event → State → Set 0ℓ
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
              → Set (lsuc (ℓ₁ ⊔ ℓ₂) ⊔ ℓ')
  Invariant sm P = ∀ {state} (rs : Reachable {sm = sm} state) → P state



  Stable : ∀ {ℓ₁ ℓ₂ ℓ'} {State : Set ℓ₁} {Event : Set ℓ₂}
                (sm : StateMachine State Event) (P : Pred State ℓ')
              → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ')
  Stable sm P = ∀ {state event} (enEv : enabled sm event state)
                → P state
                → P (action sm enEv)


  EventSet : ∀ {ℓ} {Event : Set ℓ} → Set (ℓ ⊔ lsuc 0ℓ)
  EventSet {ℓ} {Event} = Pred {ℓ} Event 0ℓ

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
   ⋃₁ : ∀ {ℓ ℓ'} {A : Set ℓ'} → (A → Pred State ℓ) → Pred State (ℓ ⊔ ℓ')
   ⋃₁ {A = A} P = λ x → Σ[ i ∈ A ] P i x

   syntax ⋃₁ (λ i → P) = [∃ i ∶ P ]


   ⋃₂ : ∀ {ℓ₁ ℓ₂ ℓ'} {A : Set ℓ'} → (C : Pred A ℓ₁) → (F : A → Pred State ℓ₂) → Pred State _
   ⋃₂ {A = A} C F = λ s → Σ[ i ∈ A ] ( C i × F i s )

   syntax ⋃₂ C (λ x → P) = [∃ x ⇒ C ∶ P ]

   -----------------------------------------------------------------------------
   -- PROOF RULES for liveness
   -----------------------------------------------------------------------------
   infix 1 _l-t_

   data _l-t_ (P : Pred State 0ℓ) (Q : Pred State 0ℓ)
              : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
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

     viaTrans  : ∀ {R : Pred State 0ℓ}
               → P l-t R
               → R l-t Q
               → P l-t Q

     viaTrans2 : ∀ {R : Pred State 0ℓ}
               → P l-t (Q ∪ R)
               → R l-t Q
               → P l-t Q

     viaDisj   : ∀ {P₁ P₂ : Pred State 0ℓ}
               -- P = P₁ ∪ P₂ (from the paper)
               → P ⊆ (P₁ ∪ P₂)
               → P₁ l-t Q
               → P₂ l-t Q
               → P  l-t Q

     viaUseInv : ∀ {R : Pred State 0ℓ}
               → Invariant (stateMachine sys) R
               → (P ∩ R) l-t (R ⇒ Q)
               → P l-t Q

     viaWFR    : ∀ (F : Z → Pred State 0ℓ)
               → P l-t (Q ∪ [∃ x ∶ F x ])
               → (∀ (w : Z) → F w l-t (Q ∪ [∃ x ⇒ _< w ∶ F x ]))
               → P l-t Q

     viaStable : ∀ {P' Q' : Pred State 0ℓ} {S : Pred State 0ℓ}
                 → P l-t P' ∩ S
                 → P' l-t Q'
                 → Stable (stateMachine sys) S
                 → Q' ∩ S l-t Q
                 → P l-t Q

     viaAllVal : ∀ {A : Set} → {R : A → Pred State 0ℓ}
                 → Invariant (stateMachine sys) [∃ x ∶ R x ]
                 → (∀ (a : A) → (P ∩ R a) l-t Q )
                 → P l-t Q




   P⊆QQ→Inv[P⇒Q] : ∀ {ℓ₃ ℓ₄}
                      (sm : StateMachine State Event)
                      {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                  → P ⊆ Q → Invariant sm (P ⇒ Q)
   P⊆QQ→Inv[P⇒Q] sm p⊆q rs pS
     with p⊆q pS
   ... | qS = qS


   invR⇒P-l-t-P∧R : ∀ {sm : StateMachine State Event}
                      {P : Pred State 0ℓ} {R : Pred State 0ℓ}
                    → Invariant (stateMachine sys) R
                    → P l-t P ∩ R
   invR⇒P-l-t-P∧R invR = viaInv (λ rs ps → ps , (invR rs))

