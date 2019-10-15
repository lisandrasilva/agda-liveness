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
  Invariant sm P = ∀ {sr} (rs : Reachable {sm = sm} sr) → P sr



  record System {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      stateMachine : StateMachine State Event
      weakFairness : (Event → Set) → Set
  open System

  EventSet : ∀ {ℓ} {Event : Set ℓ} → Set (lsuc ℓ)
  EventSet {ℓ} {Event} = Event → Set ℓ

  -- TODO : genericize event level

  enabledSet : ∀ {ℓ₁ ℓ₂} {State : Set ℓ₁}{Event : Set ℓ₂} → (StateMachine State Event) → EventSet {Event = Event} → State → Set ℓ₂
  enabledSet sm es s = ∃[ e ] enabled sm e s

  data MyEvent : Set where
    inc  : MyEvent
    inc2 : MyEvent


  data MyEnabled : MyEvent → ℕ → Set where
    tt : ∀ {e} {n} → MyEnabled e n


  data MyWeakFairness2 : (MyEvent → Set) where
    mwf1 : MyWeakFairness2 inc
    mwf2 : MyWeakFairness2 inc2

  data MyWeakFairness : (MyEvent → Set) → Set where
    w0 : MyWeakFairness (MyWeakFairness2)


  myStateMachine : StateMachine ℕ MyEvent
  myStateMachine = record { initial = 2 ≡_ ; enabled = MyEnabled ; action = λ { {pre} {inc}  x → suc pre
                                                                              ; {pre} {inc2} x → suc (suc pre)} }

  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = myStateMachine ; weakFairness = MyWeakFairness }

  myInvariant : Invariant myStateMachine (2 ≤_)
  myInvariant (init x) =  ≤-reflexive x
  myInvariant (step {ps} {inc} rs enEv) = ≤-step (myInvariant rs)
  myInvariant (step {ps} {inc2} rs enEv) = ≤-step (≤-step (myInvariant rs))


  module LeadsTo {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) (sys : System State Event) where

   data [_]_[_] {ℓ'} (P : Pred State ℓ') (e : Event) (Q : Pred State ℓ') : Set (lsuc (ℓ' ⊔ ℓ₁)) where
      hoare : ∀ {ps} → P ps →  (enEv : enabled (stateMachine sys) e ps) → Q (action (stateMachine sys) enEv ) → [ P ] e [ Q ]

   

   data _l-t_ {ℓ'} (P Q : Pred State ℓ'): Set (lsuc (ℓ' ⊔ ℓ₁ ⊔ ℓ₂))  where
     viaEvSet : (eventSet : EventSet)
              → (∀ {e} → eventSet e → [ P ] e [ Q ])
              → (∀ {e} → ¬ (eventSet e) → [ P ] e [ P ∪ Q ])
              → Invariant (stateMachine sys) (λ s → ¬ (P s) ⊎ enabledSet (stateMachine sys) eventSet s)
              → P l-t Q
     viaInv   : Invariant (stateMachine sys) (λ s → P s → Q s)
              → P l-t Q
     viaTrans : ∀ {R : Pred State ℓ'}
              → P l-t R
              → R l-t Q
              → P l-t Q
     viaTrans2 : ∀ {R : Pred State ℓ'}
               → P l-t (Q ∪ R)
               → R l-t Q
               → P l-t Q
     viaDisj   : ∀ {P₁ P₂ : Pred State ℓ'}
               -- P = P₁ ∪ P₂ (from the paper)
               → P ⊆ (P₁ ∪ P₂)
               → P₁ l-t Q
               → P₂ l-t Q
               → P  l-t Q
     viaPenult : ∀ {R : Pred State ℓ'}
               → Invariant (stateMachine sys) R
               → (P ∩ R) l-t (λ s → R s → Q s)
               → P l-t Q


  open LeadsTo ℕ MyEvent mySystem


  myEventSet : EventSet {Event = MyEvent}
  myEventSet inc  = ⊤
  myEventSet inc2 = ⊤

  progressDumb : ∀ (n : ℕ) → (_≡ n) l-t λ x → x ≡ suc n ⊎ x ≡ suc (suc n)
  progressDumb n = LeadsTo.viaEvSet myEventSet
                                    (λ { {inc}  x → LeadsTo.hoare refl tt (inj₁ refl)
                                       ; {inc2} x → LeadsTo.hoare refl tt (inj₂ refl)})
                                    (λ { {inc}  x → ⊥-elim (x tt)
                                       ; {inc2} x → ⊥-elim (x tt) })
                                    λ { {sr} rs → inj₂ (inc , tt)}




