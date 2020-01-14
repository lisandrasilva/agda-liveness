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
      initial : Pred State ℓ₁
      enabled : Event → State → Set ℓ₂
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



  Stable : ∀ {ℓ₁ ℓ₂ ℓ'} {State : Set ℓ₁} {Event : Set ℓ₂}
                (sm : StateMachine State Event) (P : Pred State ℓ')
              → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ')
  Stable sm P = ∀ {state event} (enEv : enabled sm event state)
                → P state
                → P (action sm enEv)


  postulate
    -- TODO : Prove the property
    lemma-Imp→Inv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {State : Set ℓ₁} {Event : Set ℓ₂}
                      (sm : StateMachine State Event)
                      {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                    → P ⊆ Q → Invariant sm (P ⇒ Q)

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
   ⋃₁ : ∀ {ℓ} → (Z → Pred State ℓ) → Pred State _
   ⋃₁ P = λ x → Σ[ i ∈ Z ] P i x

   syntax ⋃₁ (λ i → P) = [∃ i ∶ P ]


   ⋃₂ : ∀ {ℓ₁ ℓ₂} → (C : Pred Z ℓ₁) → (F : Z → Pred State ℓ₂) → Pred State _
   ⋃₂ C F = λ s → Σ[ i ∈ Z ] ( C i × F i s )

   syntax ⋃₂ C (λ x → P) = [∃ x ⇒ C ∶ P ]

   -----------------------------------------------------------------------------
   -- PROOF RULES for liveness
   -----------------------------------------------------------------------------
   infix 1 _l-t_

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

     viaStable : ∀ {P' Q' : Pred State 0ℓ} {S : Pred State ℓ₄}
                 → P l-t P' ∩ S
                 → P' l-t Q'
                 → Stable (stateMachine sys) S
                 → Q' ∩ S l-t Q
                 → P l-t Q

   postulate
     viaStable1 : ∀ {ℓ₃ ℓ₄ ℓ'}
                    {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {S : Pred State ℓ'}
                  → P l-t Q
                  → Stable (stateMachine sys) S
                  → P ∩ S l-t Q ∩ S






   -----------------------------------------------------------------------------
   -- BEHAVIORS
   -----------------------------------------------------------------------------
{-
  module Behaviors
    {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) (sys : System State Event)
    where
-}
   postulate
     iddleEnabled : (s : State) → ∃[ e ] (enabled (stateMachine sys) e s)

  -- Approach 1
   record Behavior (S : State) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      head : Behavior S
      tail : (e : Event) → (enEv : enabled (stateMachine sys) e S)
            -- {eventSet : EventSet} {evSet : eventSet event} {wf : weakFairness sys eventSet}
             → Behavior (action (stateMachine sys) enEv)
   open Behavior

   AllowedBehavior : (s : State) → Reachable {sm = stateMachine sys} s → Behavior s
   head (AllowedBehavior s (init x))
     = AllowedBehavior s (init x)
   tail (AllowedBehavior s (init x))
     = λ e enEv → AllowedBehavior (action (stateMachine sys) enEv) (step (init x) enEv)

   head (AllowedBehavior .(action (stateMachine sys) enEv) (step x enEv))
     = AllowedBehavior (action (stateMachine sys) enEv) (step x enEv)
   tail (AllowedBehavior .(action (stateMachine sys) enEv) (step x enEv))
     = λ e enEv₁ → AllowedBehavior (action (stateMachine sys) enEv₁) (step (step x enEv) enEv₁)



  -------------------------------------------------------------------------------------------
  -------------------------------------------------------------------------------------------
   -- Approach 2
   record Stream {ℓ} (A : Set ℓ) : Set ℓ where
    coinductive
    field
      head : A
      tail : Stream A
   open Stream


   Behavior2 : ∀ (s : State)
               → {event : Event} {enEv : enabled (stateMachine sys) event s}
               → Stream State
   head (Behavior2 st) = st
   tail (Behavior2 st {ev} {enEv}) = let next = action (stateMachine sys) enEv
                                         iddle = iddleEnabled next
                                     in Behavior2 next {proj₁ iddle} {proj₂ iddle}

   Behavior3 : ∀ {st} → Reachable {sm = stateMachine sys} st → Stream State
   head (Behavior3 (init {sᵢ} x)) = sᵢ
   tail (Behavior3 (init x)) = Behavior3 (init x) -- Is this equivalent to the iddle event???
   head (Behavior3 (step {st} {ev} x enEv)) = st
   tail (Behavior3 (step {st} {ev} x enEv)) = Behavior3 x

  -------------------------------------------------------------------------------------------
  -------------------------------------------------------------------------------------------


   soundness : ∀ {ℓ₃ ℓ₄} {st} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
               → (rSt : Reachable {sm = stateMachine sys} st)
               → (behavior : Behavior st)
               → P st
               → P l-t Q
               → {!!}


