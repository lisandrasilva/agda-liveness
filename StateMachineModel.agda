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

open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_] )
open import Relation.Unary
open import Level renaming (suc to lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Sum
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

module StateMachineModel where

  record StateMachine {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      initial : Pred State 0ℓ
      enabled : Event → State → Set
      action  : ∀ {pre} {e} → enabled e pre → State
  open StateMachine


  data Reachable {ℓ₁ ℓ₂} {s : Set ℓ₁} {e : Set ℓ₂} {sm : StateMachine s e} : s → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    init : ∀ {sᵢ} → initial sm sᵢ → Reachable sᵢ
    step : ∀ {ps}{ev} → Reachable {sm = sm} ps → (enEv : enabled sm ev ps) → Reachable (action sm enEv)


  Invariant : ∀  {ℓ₁ ℓ₂ ℓ'} {s : Set ℓ₁} {e : Set ℓ₂} (sm : StateMachine s e) (P : Pred s ℓ') → Set (ℓ' ⊔ lsuc (ℓ₁ ⊔ ℓ₂))
  -- REFACTOR : sr can be explicit
  Invariant sm P = ∀ {sr} (rs : Reachable {sm = sm} sr) → P sr

  postulate
    lemma-Imp→Inv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {s : Set ℓ₁} {e : Set ℓ₂} (sm : StateMachine s e) {P : Pred s ℓ₃} {Q : Pred s ℓ₄}
                  → P ⊆ Q → Invariant sm (P ⇒ Q)

  EventSet : ∀ {ℓ} {Event : Set ℓ} → Set (lsuc ℓ)
  EventSet {ℓ} {Event} = Event → Set ℓ

  record System {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      stateMachine : StateMachine State Event
      -- Weak fairness is a predicate over EventSets, which ones have weakfairness
      weakFairness : EventSet {Event = Event} → Set
  open System


  -- TODO : genericize event level

  enabledSet : ∀ {ℓ₁ ℓ₂} {State : Set ℓ₁}{Event : Set ℓ₂} → (StateMachine State Event) → EventSet {Event = Event} → State → Set ℓ₂
  enabledSet sm es s = ∃[ e ] enabled sm e s



  module LeadsTo {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) (sys : System State Event) where

   data [_]_[_] {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (e : Event) (Q : Pred State ℓ₄) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
      hoare : (∀ {ps} → P ps → (enEv : enabled (stateMachine sys) e ps) → Q (action (stateMachine sys) enEv )) → [ P ] e [ Q ]

   Z : Set
   Z = ℕ


   ⋃₁ : ∀ {ℓ} → (Z → Pred State ℓ) → Pred State _
   ⋃₁ P = λ x → Σ[ i ∈ Z ] P i x

   syntax ⋃₁ (λ i → P) = [∃ i ∶ P ]

   ⋃₂ : ∀ {ℓ₁ ℓ₂} → (C : Pred Z ℓ₁) → (F : Z → Pred State ℓ₂) → Pred State _
   ⋃₂ C F = λ s → Σ[ i ∈ Z ] ( C i × F i s )

   syntax ⋃₂ C (λ x → P) = [∃ x ⇒ C ∶ P ]


   data _l-t_ {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (Q : Pred State ℓ₄): Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))  where
     viaEvSet  : (eventSet : EventSet)
               -- REFACTOR : The event can be explicit and the proof implicit
               --            because we always split on the event
               -- QUESTION : 'e' shouldn't be in the weakfairness??
               → (∀ {e} → eventSet e → [ P ] e [ Q ])
               -- REFACTOR : Same thing as above
               → (∀ {e} → ¬ (eventSet e) → [ P ] e [ P ∪ Q ])
               -- REFACTOR : Use (P ⇒ enabledSet)
               → Invariant (stateMachine sys) (λ s → ¬ (P s) ⊎ enabledSet (stateMachine sys) eventSet s)
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
