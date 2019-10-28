open import Data.Nat
open import Data.Nat.Divisibility
open import Relation.Nullary
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_] )
open import Relation.Unary
open import Data.Sum
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Nullary.Negation using (contradiction)



open import StateMachineModel


{-
  This State Machine begins in a state equal to 0 or 1 and if :
    - The current state s is Even then jump to state (s + 2)
    - The current state is Odd jump to state (s + 1)

  We want to prove that a state s always leads-to a state Even
-}
module SMCounterEven where

  Even : ℕ → Set
  Even n = 2 ∣ n

  Odd : ℕ → Set
  Odd = ¬_ ∘ Even


  -- SPECIFICATION

  data MyEvent : Set where
    inc : MyEvent
    inc2 : MyEvent

  data MyEnabled : MyEvent → ℕ → Set where
    odd  : ∀ {n} → Odd n  → MyEnabled inc  n
    even : ∀ {n} → Even n → MyEnabled inc2 n

  MyStateMachine : StateMachine ℕ MyEvent
  MyStateMachine = record
                   { initial =  (0 ≡_) ∪ (1 ≡_)
                   ; enabled = MyEnabled
                   ; action  = λ { {pre} {inc}  cond → 1 + pre
                                 ; {pre} {inc2} cond → 2 + pre }
                   }

  MyEventSet : EventSet {Event = MyEvent}
  MyEventSet inc  = ⊥
  MyEventSet inc2 = ⊤

  -- Only the event inc2 has WeakFairness

  data MyWeakFairness : EventSet → Set where
    wf : MyWeakFairness MyEventSet

  MySystem : System ℕ MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }
