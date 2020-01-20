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



  data ReachableFrom {st} (σ : Behavior st) :
       ∀ {s} → Behavior s → Set (ℓ₁ ⊔ ℓ₂) where
    head : ReachableFrom σ σ
    next : ∀ {e} → (enEv : enabled StMachine e st)
                  → ReachableFrom σ (σ .tail enEv)
    transR : ∀ {st₁ st₂ : State} {σ₁ : Behavior st₁} {σ₂ : Behavior st₂}
               → ReachableFrom σ σ₁
               → ReachableFrom σ₁ σ₂
               → ReachableFrom σ σ₂

  record _satisfies_ {st : State} {ℓ} (σ : Behavior st) (P : Pred State ℓ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    constructor satisfy
    field
      tl-any : P st
               ⊎
               Σ[ s ∈ State ]
               Σ[ σ₁ ∈ Behavior s ]
               Σ[ rB ∈ ReachableFrom σ σ₁ ] P s
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


  σ⊢R⇒∃stR : ∀ {st} {ℓ₃} {R : Pred State ℓ₃}
              → (σ : Behavior st)
              → σ satisfies R
              → Σ[ s ∈ State ]
                Σ[ σ₁ ∈ Behavior s ]
                Σ[ rB ∈ ReachableFrom σ σ₁ ] R s
  σ⊢R⇒∃stR {st} σ σ⊢R
    with tl-any σ⊢R
  ... | inj₁ s∈R = st , σ , head , s∈R
  ... | inj₂ (s , σ₁ , rFrom , s∈R) = s , σ₁ , rFrom , s∈R




  soundness : ∀ {ℓ₃ ℓ₄} {st} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
              → (rSt : Reachable {sm = StMachine} st)
              → (σ : Behavior st)
              → P st
              → P l-t Q
              → σ satisfies Q
  tl-any (soundness {st = st} {P} {Q} stR σ st∈P (viaEvSet evSet wf c₁ c₂ c₃))
    with ∃Enabled? st
  ... | no ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ stR st∈P)))
  ... | yes (ev , enEv)
      with ev ∈Set? evSet
  ...   | yes evSetEv = {!!} --inj₂ (ev , enEv , satisfy (inj₁ ([P]e[Q]∧P⇒Q enEv st∈P (c₁ ev evSetEv))) )
  ...   | no ¬evSetEv
        with c₂ ev ¬evSetEv
  ...     | hoare p∨q
          with p∨q st∈P enEv
  ...       | inj₂ qActionSt = inj₂ {!!} --(ev , enEv , satisfy (inj₁ qActionSt) )
  ...       | inj₁ pActionSt = inj₂ {!!} {-(ev , enEv , soundness
                                                   (step stR enEv)
                                                   (σ .tail enEv)
                                                   pActionSt
                                                   (viaEvSet evSet wf c₁ c₂ c₃)) -}

  tl-any (soundness stR σ st∈P (viaInv p⇒q)) = inj₁ (p⇒q stR st∈P)
  soundness stR σ st∈P (viaTrans PltR RltQ)
    with soundness stR σ st∈P PltR
  ... | σSatR
      with tl-any σSatR
  ...   | inj₁ st∈R = soundness stR σ st∈R RltQ

  ...   | inj₂ (ev , enEv , tSatR)
          = satisfy (inj₂ (ev , enEv , {!!}))

  soundness stR σ st∈P (viaTrans2 pltq pltq₁) = {!!}
  soundness stR σ st∈P (viaDisj x pltq pltq₁) = {!!}
  soundness stR σ st∈P (viaUseInv x pltq) = {!!}
  soundness stR σ st∈P (viaWFR F pltq x) = {!!}
  soundness stR σ st∈P (viaStable pltq pltq₁ x pltq₂) = {!!}
