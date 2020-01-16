open import Prelude

open import StateMachineModel


module Behaviors {ℓ₁ ℓ₂}
       (State : Set ℓ₁)
       (Event : Set ℓ₂)
       (sys : System State Event)
       (_∈EvSet?_ : (e : Event) → (evSet : EventSet) → Dec (evSet e))
  where


  open StateMachine
  open System
  open LeadsTo State Event sys


  StMachine = stateMachine sys


  record Stream {ℓ} (A : Set ℓ) : Set ℓ where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream


  record Behavior (S : State) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      event : Event
      enEv  : enabled StMachine event S
      tail  : Behavior (action StMachine enEv)
  open Behavior


  f : ∀ {st} → Behavior st → Stream State
  head  (f {st} x) = st
  tail (f x) = f (tail x)

  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st tail} (ps  : P st)
            → AnyS∈B P {st} tail
    there : ∀ {st}
              (σ : Behavior st)
              {tail : Behavior (action StMachine (enEv σ)) }
              (pts  : AnyS∈B P tail)
            → AnyS∈B P {st} σ

   -- A behavior σ satisfies P if there is any state ∈ σ satisfies P
  _satisfies_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P = AnyS∈B P σ


 ------------------------------------------------------------------------------
 -- PROOF
 ------------------------------------------------------------------------------
  [P]e[Q]∧P⇒Q : ∀ {ℓ₃ ℓ₄ st e}  {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                → (enEv : enabled StMachine e st)
                → P st
                → [ P ] e [ Q ]
                → Q (action StMachine enEv)
  [P]e[Q]∧P⇒Q {st = st} enEv pSt (hoare x) = x pSt enEv


  {- There is a termination checking error because I think we need a sized
     coinductive type
     See branch lis-sized-bahaviors
  -}
  soundness : ∀ {ℓ₃ ℓ₄} {st} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
              → (rSt : Reachable {sm = StMachine} st)
              → (σ : Behavior st)
              → P st
              → P l-t Q
              → tail σ satisfies Q
  soundness {st = st} {P = P} {Q = Q} rSt σ pSt (viaEvSet evSet wf c₁ c₂ c₃)
    with event σ ∈EvSet? evSet
  ... | yes p = here ([P]e[Q]∧P⇒Q (enEv σ) pSt (c₁ (event σ) p))
  ... | no ¬p
      with c₂ (event σ) ¬p
  ...   | p⇒p∨q
        with [P]e[Q]∧P⇒Q (enEv σ) pSt p⇒p∨q
  ...     | inj₂ qHolds = here qHolds
  ...     | inj₁ pHolds
          with soundness (step rSt (enEv σ))
                         (tail σ)
                         pHolds
                         (viaEvSet evSet wf c₁ c₂ c₃)
  ...       | x = there (tail σ) x
  soundness rSt σ σ⊢p (viaInv x) = {!!}
  soundness rSt σ σ⊢p (viaTrans pltq pltq₁) = {!!}
  soundness rSt σ σ⊢p (viaTrans2 pltq pltq₁) = {!!}
  soundness rSt σ σ⊢p (viaDisj x pltq pltq₁) = {!!}
  soundness rSt σ σ⊢p (viaUseInv x pltq) = {!!}
  soundness rSt σ σ⊢p (viaWFR F pltq x) = {!!}
  soundness rSt σ σ⊢p (viaStable pltq pltq₁ x pltq₂) = {!!}

