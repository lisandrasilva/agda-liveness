open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Level renaming (suc to lsuc)
open import Data.Unit using (⊤; tt)

module StateMachineModel where


  record StateMachine {ℓ} (State Event : Set ℓ) : Set (lsuc ℓ) where
    field
      initial : State → Set
      enabled : Event → State → Set
      effect  : ∀ {pre} {e} → enabled e pre → State


  record System {ℓ} (State Event : Set ℓ) : Set (lsuc ℓ) where
    field
      stateMachine : StateMachine State Event
      weakFairness : (Event → Set) → Set


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
  myStateMachine = record { initial = 0 ≡_ ; enabled = MyEnabled ; effect = λ {x} _ → suc x }


  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = myStateMachine ; weakFairness = MyWeakFairness }

  module _ {ℓ} (State Event : Set ℓ) (m : StateMachine State Event) where

   data _l-t_ (P Q : Pred {ℓ} State 0ℓ): Set (lsuc ℓ)  where
     eventSet : {!!} --∀ {} {!P → Q → ?!} --(P → Q) → P l-t Q




