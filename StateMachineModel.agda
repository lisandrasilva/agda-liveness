open import Data.Nat
open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_] )
open import Relation.Unary
open import Level renaming (suc to lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Sum
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

module StateMachineModel where


  record StateMachine {ℓ} (State : Set ℓ) (Event : Set) : Set (lsuc ℓ) where
    field
      initial : Pred State 0ℓ
      enabled : Event → State → Set
      action  : ∀ {pre} {e} → enabled e pre → State
  open StateMachine

{-
  data Invariant {ℓ} {s} {e} (sm : StateMachine {ℓ} s e) (P : Pred s 0ℓ) : Set (lsuc ℓ) where
     init : initial sm ⊆ P → Invariant sm P
     step : ∀ {pre}{ev} (enEv : enabled sm ev pre) → P pre → P (action sm enEv) → Invariant sm P
-}

  data Reachable {ℓ} {s} {e} {sm : StateMachine  {ℓ} s e} : s → Set (lsuc ℓ) where
    init : ∀ {sᵢ} → initial sm sᵢ → Reachable sᵢ
    step : ∀ {ps}{ev} → Reachable {ℓ} {sm = sm} ps → (enEv : enabled sm ev ps) → Reachable (action sm enEv)


  Invariant : ∀ {ℓ} {s} {e} (sm : StateMachine {ℓ} s e) (P : Pred s 0ℓ) → Set (lsuc ℓ)
  Invariant {ℓ} {s} {e} sm P = ∀ (sr : s) (rs : Reachable {sm = sm} sr) → P sr



  record System {ℓ} (State : Set ℓ) (Event : Set) : Set (lsuc ℓ) where
    field
      stateMachine : StateMachine State Event
      weakFairness : (Event → Set) → Set
  open System


  data MyEvent : Set where
    inc : MyEvent
    inc2 : MyEvent


  data MyEnabled : MyEvent → ℕ → Set where
    tt : ∀ {e} {n} → MyEnabled e n


  data MyWeakFairness2 : (MyEvent → Set) where
    mwf1 : MyWeakFairness2 inc
    mwf2 : MyWeakFairness2 inc2

  data MyWeakFairness : (MyEvent → Set) → Set where
    w0 : MyWeakFairness (MyWeakFairness2)


  myStateMachine : StateMachine ℕ MyEvent
  myStateMachine = record { initial = 1 ≡_ ; enabled = MyEnabled ; action = λ {x} _ → suc x }


  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = myStateMachine ; weakFairness = MyWeakFairness }

  myInvariant : Invariant myStateMachine (1 ≤_)
  myInvariant sr (init x) = ≤-reflexive x
  myInvariant (suc x) (step rs enEv) = ≤-step (myInvariant x rs)

  module _ {ℓ} (State : Set ℓ) (Event : Set) (sys : System State Event) where

   --EventSet : ∀ {ℓ} {E : Set ℓ} → (E → Set (lsuc ℓ))

   EventSet : Set (lsuc ℓ)
   EventSet = Event → Set ℓ
   --  ⦃ ⦄

   data [_]_[_] (P : Pred {ℓ} State 0ℓ) (e : Event) (Q : Pred {ℓ} State 0ℓ) : Set (lsuc ℓ) where
      hoare : ∀ {ps} → P ps →  (enEv : enabled (stateMachine sys) e ps) → Q (action (stateMachine sys) enEv ) → [ P ] e [ Q ]


   data _l-t_ (P Q : Pred {ℓ} State 0ℓ): Set (lsuc ℓ)  where
     viaEvSet : (eventSet : EventSet)
              → (∀ {e} → eventSet e → [ P ] e [ Q ])
              → (∀ {e} → ¬ (eventSet e) → [ P ] e [ P ∪ Q ])
              → Invariant (stateMachine sys) (λ s → ¬ (P s) ⊎ ∃[ e ] enabled (stateMachine sys) e s)
              → P l-t Q




