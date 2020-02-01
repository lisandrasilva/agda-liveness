open import Prelude

open import StateMachineModel
open StateMachine
open System

module Behaviors {ℓ₁ ℓ₂}
       (State : Set ℓ₁)
       (Event : Set ℓ₂)
       (sys : System State Event)
       (∃Enabled?_ : (st : State)
                      → Dec (Σ[ e ∈ Event ] enabled (stateMachine sys) e st))
       (_∈Set?_ : (ev : Event) (evSet : EventSet)
                      → Dec (evSet ev))
  where

  open LeadsTo State Event sys

  StMachine = stateMachine sys


  record Behavior (S : State) :
    Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tail  : Σ[ e ∈ Event ] Σ[ enEv ∈ enabled StMachine e S ]
                 Behavior (action StMachine enEv)
              ⊎
              ¬ ( Σ[ e ∈ Event ] enabled StMachine e S )
  open Behavior


  data BehaviorSuffix (st : State) : Set (ℓ₁ ⊔ ℓ₂) where
      last : BehaviorSuffix st
      noEv : ¬ (Σ[ e ∈ Event ] enabled StMachine e st)
                → BehaviorSuffix st
      _∷_  : ∀ {e} → (enEv : enabled StMachine e st)
                → BehaviorSuffix (action StMachine enEv)
                → BehaviorSuffix st
  open BehaviorSuffix


  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (BehaviorSuffix st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : BehaviorSuffix st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {st e} (n : ℕ)
              (enEv : enabled StMachine e st)
              {t : BehaviorSuffix (action StMachine enEv)}
              (pts  : AnyS∈B P n t)
            → AnyS∈B P (suc n) (enEv ∷ t)

  -- Take 0 will return st because we are considering indexes starting at 0
  take : ∀ {st} → ℕ → (σ : Behavior st) → BehaviorSuffix st
  take zero σ = last
  take (suc n) σ
    with tail σ
  ... | inj₂ ¬enEv = noEv ¬enEv
  ... | inj₁ (e , enEv , t) = enEv ∷ take n t


  lastSt : ∀ {st} → BehaviorSuffix st → State
  lastSt {st} last = st
  lastSt {st} (noEv x) = st
  lastSt {st} (enEv ∷ t) = lastSt t

  _satisfies_at_ : ∀ {st : State} {ℓ}
                   → (σ : Behavior st)
                   → (P : Pred State ℓ)
                   → ℕ
                   → Set ℓ
  -- σ satisfies P at i = AnyS∈B P i (take i σ)
  σ satisfies P at i = P (lastSt (take i σ))


  data All {ℓ} (P : Pred State ℓ)
    :  ∀ {st : State} → Pred (BehaviorSuffix st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    last : ∀ {st} (ps  : P st)
           → All P (last {st})
    noEv : ∀ {st} (ps  : P st)
           → (¬enEv : ¬ ( Σ[ e ∈ Event ] enabled StMachine e st ))
           → All P (noEv ¬enEv)
    _∷_  : ∀ {st e} {enEv : enabled StMachine e st}
             {t : BehaviorSuffix (action StMachine enEv)}
             (ps  : P st)
             (pts  : All P t)
            → All P (enEv ∷ t)


  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x


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


  postulate
    weak-fairness : ∀ {evSet : EventSet} {st}
                    → (σ : Behavior st)
                    →  Σ[ n ∈ ℕ ]
                     ( All (enabledSet StMachine evSet) (take n σ)
                       → Σ[ e ∈ Event ]
                            evSet e × enabled StMachine e (lastSt (take n σ)) )

  soundness : ∀ {ℓ₃ ℓ₄} {st} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → (rSt : Reachable {sm = StMachine} st)
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] σ satisfies Q at (i + j)
  soundness rSt σ satP (LeadsTo.viaEvSet eventSet x x₁ x₂ x₃) = {!!}
  soundness rSt σ satP (LeadsTo.viaInv x) = {!!}
  soundness rSt σ satP (LeadsTo.viaTrans lt lt₁)
    with soundness rSt σ satP lt
  ... | fst , snd = soundness {!!} {!!} snd lt₁
  soundness rSt σ satP (LeadsTo.viaTrans2 lt lt₁) = {!!}
  soundness rSt σ satP (LeadsTo.viaDisj x lt lt₁) = {!!}
  soundness rSt σ satP (LeadsTo.viaUseInv x lt) = {!!}
  soundness rSt σ satP (LeadsTo.viaWFR F lt x) = {!!}
  soundness rSt σ satP (LeadsTo.viaStable lt lt₁ x lt₂) = {!!}

