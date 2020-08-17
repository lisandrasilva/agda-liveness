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
  record StateMachine (State : Set) (Event : Set) : Set₁ where
    field
      initial : Pred State 0ℓ
      enabled : Event → State → Set
      action  : ∀ {preState} {event} → enabled event preState → State
  open StateMachine


  data Reachable {State Event} {sm : StateMachine State Event} : State → Set where
    init : ∀ {s₀} → initial sm s₀
           → Reachable s₀
    step : ∀ {st event} → Reachable {sm = sm} st → (enEv : enabled sm event st)
           → Reachable (action sm enEv)


  Invariant : ∀ {State Event} (sm : StateMachine State Event) (P : Pred State 0ℓ) → Set
  Invariant sm P = ∀ {state} (rs : Reachable {sm = sm} state) → P state


  Stable : ∀ {State Event} (sm : StateMachine State Event) (P : Pred State 0ℓ) → Set
  Stable sm P = ∀ {st ev} (enEv : enabled sm ev st)
                → P st
                → P (action sm enEv)


  EventSet : ∀ {Event : Set} → Set₁
  EventSet {Event} = Pred Event 0ℓ


  record System State Event : Set₁ where
    field
      stateMachine : StateMachine State Event
      weakFairness : Pred (EventSet {Event}) 0ℓ
  open System


  enabledSet : ∀ {State Event} → StateMachine State Event
               → EventSet {Event} → State → Set
  enabledSet sm evSet state = ∃[ event ] (event ∈ evSet × enabled sm event state)


  module LeadsTo
    (State : Set) (Event : Set) (sys : System State Event)
    where


   -----------------------------------------------------------------------------
   -- HOARE Triple
   -----------------------------------------------------------------------------
   data [_]_[_] (P : Pred State 0ℓ) (event : Event) (Q : Pred State 0ℓ) : Set where
      hoare : (∀ {st} → P st
                      → (enEv : enabled (stateMachine sys) event st)
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

   data _l-t_ (P : Pred State 0ℓ) (Q : Pred State 0ℓ) : Set₁ where
     viaEvSet  :   (evSet : EventSet) → (weakFairness sys evSet)
                 → (∀ (e : Event) → e ∈ evSet → [ P ] e [ Q ])
                 → (∀ (e : Event) → ¬ (e ∈ evSet) → [ P ] e [ P ∪ Q ])
                 → Invariant (stateMachine sys)
                             (P ⇒ enabledSet (stateMachine sys) evSet)
               → P l-t Q

     viaInv    : Invariant (stateMachine sys) (P ⇒ Q)
                 → P l-t Q

     viaTrans  : ∀ {R} → P l-t R → R l-t Q
                 → P l-t Q

     viaTrans2 : ∀ {R} → P l-t (Q ∪ R) → R l-t Q
                 → P l-t Q

     viaDisj   : ∀ {P₁ P₂} → P ⊆ (P₁ ∪ P₂) → P₁ l-t Q → P₂ l-t Q
                 → P  l-t Q

     viaUseInv : ∀ {R} → Invariant (stateMachine sys) R → (P ∩ R) l-t (R ⇒ Q)
                 → P l-t Q

     viaWFR    : ∀ (F : Z → Pred State 0ℓ)
                 → P l-t (Q ∪ [∃ x ∶ F x ])
                 → (∀ (w : Z) → F w l-t (Q ∪ [∃ x ⇒ _< w ∶ F x ]))
                 → P l-t Q

     viaAllVal : ∀ {A : Set} → {R : A → Pred State 0ℓ}
                 → Invariant (stateMachine sys) [∃ x ∶ R x ]
                 → (∀ (a : A) → (P ∩ R a) l-t Q )
                 → P l-t Q

     viaStable : ∀ {P' Q' S} → Stable (stateMachine sys) S
                 → P l-t P' ∩ S → P' l-t Q' → Q' ∩ S l-t Q
                 → P l-t Q



   P⊆QQ→Inv[P⇒Q] : ∀ {P Q} {sm : StateMachine State Event}
                   → P ⊆ Q
                   → Invariant sm (P ⇒ Q)
   P⊆QQ→Inv[P⇒Q] p⊆q rs pS
     with p⊆q pS
   ... | qS = qS


   invR⇒P-l-t-P∧R : ∀ {P R} {sm : StateMachine State Event}
                    → Invariant (stateMachine sys) R
                    → P l-t P ∩ R
   invR⇒P-l-t-P∧R invR = viaInv (λ rs ps → ps , (invR rs))


