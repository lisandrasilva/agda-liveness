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

  even? : (n : ℕ) → Dec (Even n)
  even? n = 2 ∣? n

  evenK⇒even2+K : ∀ {k} → Even k → Even (2 + k)
  evenK⇒even2+K (divides q₁ refl) = divides (1 + q₁) refl

  oddK⇒odd2+K : ∀ {k} → Odd k → Odd (2 + k)
  oddK⇒odd2+K {zero}  x x₁ = ⊥-elim (x (divides zero refl))
  oddK⇒odd2+K {suc k} x x₁ with even? k
  ... | no imp  = ⊥-elim (x {!!})
  ... | yes prf = {!!}

  oddK⇒even1+K : ∀ {k} → Odd k → Even (1 + k)
  oddK⇒even1+K {zero} x  = ⊥-elim (x (divides 0 refl))
  oddK⇒even1+K {suc k} x with even? k
  ... | no imp  = ⊥-elim (x (oddK⇒even1+K imp))
  ... | yes prf = evenK⇒even2+K prf


  odd1 : Odd 1
  odd1 (divides zero ())
  odd1 (divides (suc q₁) ())

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


  -- PROOFS
  open LeadsTo ℕ MyEvent MySystem

  -- Any state n leads to an Even state
  progressEven : ∀ {n : ℕ} → (n ≡_) l-t Even
  progressEven = viaEvSet
                   MyEventSet
                   (λ { {inc2} s → hoare λ { refl (even x)
                                                  → evenK⇒even2+K x }})
                   (λ { {inc}  s → hoare λ { refl (odd  x)
                                                  → inj₂ (oddK⇒even1+K x)}
                      ; {inc2} s → ⊥-elim (s tt) })
                   λ { (init (inj₁ refl))
                             → inj₂ (inc2 , (even (divides zero refl)))
                     ; (init (inj₂ refl))
                             → inj₂ (inc , (odd odd1))
                     ; (step rs (odd x))  → inj₂ (inc2 , even (oddK⇒even1+K x))
                     ; (step rs (even x)) → inj₂ (inc2 , even (evenK⇒even2+K x))}

