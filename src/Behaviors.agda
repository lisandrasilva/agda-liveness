open import Prelude

open import StateMachineModel
open StateMachine
open System

module Behaviors {ℓ₁ ℓ₂}
       (State : Set ℓ₁)
       (Event : Set ℓ₂)
       (sys : System State Event)
       (∃Enabled?_ : (st : State) → Dec (Σ[ e ∈ Event ] enabled (stateMachine sys) e st))
       (_∈Set?_ : (ev : Event) (evSet : EventSet) → Dec (evSet ev))
  where

  open LeadsTo State Event sys

  StMachine = stateMachine sys


  record Behavior (S : State) :
    Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tail  : ∀ {e : Event} → (enEv : enabled StMachine e S)
              → Behavior (action StMachine enEv)
  open Behavior



  record _satisfies_ {st : State} {ℓ} (σ : Behavior st) (P : Pred State ℓ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tl-any : P st
               ⊎
               Σ[ e ∈ Event ] Σ[ enEv ∈ enabled StMachine e st ] ( σ .tail enEv satisfies P)
  open _satisfies_


 ------------------------------------------------------------------------------
 -- PROOF
 ------------------------------------------------------------------------------
  [P]e[Q]∧P⇒Q : ∀ {ℓ₃ ℓ₄ st e}  {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                → (enEv : enabled StMachine e st)
                → P st
                → [ P ] e [ Q ]
                → Q (action StMachine enEv)
  [P]e[Q]∧P⇒Q {st = st} enEv pSt (hoare x) = x pSt enEv


  c₃→∃enEv : ∀ {st} {ℓ₃} {P : Pred State ℓ₃} {evSet : EventSet}
               → Σ Event (λ event →
                    Σ (evSet event) (λ x → enabled StMachine event st))
               → Σ Event (λ e → enabled StMachine e st)

  c₃→∃enEv (ev , _ , enEv) = ev , enEv




  soundness : ∀ {ℓ₃ ℓ₄} {st} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
              → (rSt : Reachable {sm = StMachine} st)
              → (σ : Behavior st)
              → P st
              → P l-t Q
              → σ satisfies Q
  tl-any (soundness {st = st} {P} {Q} rSt σ pSt (viaEvSet evSet wf c₁ c₂ c₃))
    with ∃Enabled? st
  ... | no ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ rSt pSt)))
  ... | yes (ev , enEv)
      with ev ∈Set? evSet
  ...   | yes evSetEv = inj₂ (ev , enEv , record { tl-any = inj₁ ([P]e[Q]∧P⇒Q enEv pSt (c₁ ev evSetEv)) })
  ...   | no ¬evSetEv
        with c₂ ev ¬evSetEv
  ...     | hoare p∨q
          with p∨q pSt enEv
  ...       | inj₂ qActionSt = inj₂ (ev , enEv , record { tl-any = inj₁ qActionSt })
  ...       | inj₁ pActionSt = inj₂ (ev , enEv , soundness
                                                   (step rSt enEv)
                                                   (σ .tail enEv)
                                                   pActionSt
                                                   (viaEvSet evSet wf c₁ c₂ c₃))

  soundness rSt σ pSt (LeadsTo.viaInv p⇒q) = {!!}
  soundness rSt σ pSt (viaTrans pltq₁ pltq₂) = {!!}
  soundness rSt σ pSt (viaTrans2 pltq pltq₁) = {!!}
  soundness rSt σ pSt (viaDisj x pltq pltq₁) = {!!}
  soundness rSt σ pSt (viaUseInv x pltq) = {!!}
  soundness rSt σ pSt (viaWFR F pltq x) = {!!}
  soundness rSt σ pSt (viaStable pltq pltq₁ x pltq₂) = {!!}

