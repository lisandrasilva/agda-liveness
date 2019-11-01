open import Data.Nat
open import Data.Nat.Properties
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

  -- If we are in a state that is odd then the enabled event is inc
  -- otherwise the enabled event is inc2
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

  alwaysEnabled : ∀ (s : ℕ) → enabledSet MyStateMachine MyEventSet s
  alwaysEnabled s with even? s
  ... | yes p = inc2 , (even p)
  ... | no ¬p = inc  , (odd ¬p)

  -- Any state n leads to an Even state
  progressEven : ∀ {n : ℕ} → (n ≡_) l-t Even
  progressEven = viaEvSet
                   MyEventSet
                   (λ { {inc2} s
                             → hoare λ { refl (even x) → evenK⇒even2+K x }})
                   (λ { {inc}  s
                             → hoare λ { refl (odd  x) → inj₂ (oddK⇒even1+K x)}
                      ; {inc2} s → ⊥-elim (s tt) })
                   λ {s} rs → inj₂ (alwaysEnabled s)

  -- QUESTION : Although we don't have weakfairness (WF) on event inc it was
  -- possible to prove this.
  -- ANSWER   : This is because of the 2nd constraint in the viaEvSet constructor:
  --      - ∀ event e ∉ WF (in this case only inc) → [P] e [P ∪ Q], in this case
  --   we achieve Q (Even), because the event inc is enabled only in Odd states.


  -- REFACTOR: Maybe m is the one that should be explicit
  myWFR : ∀ {m} → ℕ → Z → Set
  myWFR {m} d s = m ≡ d + s

  xx0 :  ∀ {m} → (s : Z) → Even s → (m ≤ s × Even s) ⊎ ∃[ x ] myWFR {m} x s
  xx0 {m} s sEven with m ≤? s
  ... | yes m≤s = inj₁ (m≤s , sEven)
  ... | no  s<m = inj₂ ( m ∸ s , sym (m∸n+n≡m (<⇒≤ (≰⇒> s<m))) )


  [P]l-t[Q∪Fx] : ∀ {n m}
                 → (n ≡_) l-t (((m ≤_) ∩ Even) ∪ (λ s → ∃[ x ] myWFR {m} x s))
  [P]l-t[Q∪Fx] {n} {m} = viaEvSet
                           MyEventSet
                           (λ { {inc2} evSet
                                       → hoare λ { refl (even x)
                                            → xx0 (2 + n) (evenK⇒even2+K x) }})
                           (λ { {inc}  evSet
                                       → hoare λ { refl (odd x)
                                            → inj₂ (xx0 (1 + n) (oddK⇒even1+K x))}
                              ; {inc2} evSet
                                       → ⊥-elim (evSet tt) })
                           λ { {s} rs → inj₂ (alwaysEnabled s) }


  -- It's not being used anymore, delete later
  m+0≤n+m : ∀ {m n} → m + 0 ≤ n + m
  m+0≤n+m {m} {n} rewrite +-identityʳ m = m≤n+m m n


  -- If we are at distance 0 from m, which means state s ≡ m, then it leads-to a
  -- state s₁ > m ∩ Even s₁, because or we increment 1 if s is odd or we
  -- increment 2 if s is even.
  d≡0⇒Q : ∀ {m}
          → myWFR {m} 0
            l-t
            ( (m ≤_) ∩ Even )
  d≡0⇒Q {m} = viaEvSet
                MyEventSet
                (λ { {inc2} evSet
                            → hoare λ { refl (even x)
                                    → m≤n+m m 2 , evenK⇒even2+K x }})
                (λ { {inc}  evSet
                            → hoare λ { refl (odd x)
                                    → inj₂ (m≤n+m m 1 , oddK⇒even1+K x)}
                   ; {inc2} evSet
                            → ⊥-elim (evSet tt) })
                λ { {s} rs → inj₂ (alwaysEnabled s)}


  -- If we are at distance 1 from m, which means m ≡ s + 1.
  -- If s is odd then s is incremented by 1 (because of the enabling
  -- condition) then we go to an even state s₁ ≡ s + 1 ≡ m.
  -- If if s is even then s is incremented by 2, which leads to a state
  -- s₁ ≡ s + 2 > s + 1 ≡ m. As so, m ≤ s₁ ∩ Even s₁ will always  hold.
  d≡1⇒Q∪m≡0 : ∀ {m}
              → myWFR {m} 1
                l-t
                ( ((m ≤_) ∩ Even) ∪ (λ s → ∃[ x ] (x < 1 × myWFR {m} x s)))
  d≡1⇒Q∪m≡0 {m} = viaEvSet
                    MyEventSet
                    (λ { {inc2} evSet
                         → hoare λ { {ps} refl (even x)
                           → inj₁ (m≤n+m (suc ps) 1 , evenK⇒even2+K x) }})
                    (λ { {inc} evSet
                         → hoare λ { {ps} refl (odd x)
                           → inj₂ (inj₁ (≤-refl , oddK⇒even1+K x) )}
                       ; {inc2} evSet → ⊥-elim (evSet tt) })
                    λ {s} rs → inj₂ (alwaysEnabled s)


  assoc∘comm : ∀ {w s : ℕ} n → n + w + s ≡ w + (n + s)
  assoc∘comm {w} {s} n = trans (cong (_+ s) (+-comm n w)) (+-assoc w n s)

  xx2 : ∀ {w s : ℕ} n p → (n + p) + w + s ≡ n + w + (p + s)
  xx2 {w} {s} n p
    rewrite +-assoc n p w
          | +-comm p w
          | +-assoc n (w + p) s
          | +-assoc w p s
          | +-assoc n w (p + s) = refl


  d≡2⇒d≡1∪d≡0 : ∀ {m w}
                → myWFR {m} (suc (suc w))
                  l-t
                  ( (myWFR {m} (suc w)) ∪ (myWFR {m} w) )
  d≡2⇒d≡1∪d≡0 {m} {w} =
    viaEvSet
      MyEventSet
      (λ { {inc2} evSet
                  → hoare λ { {ps} refl enEv → inj₂ (assoc∘comm 2) }})
      (λ { {inc} evSet
                  → hoare λ { {ps} refl enEv → inj₂ (inj₁ (xx2 1 1))}
         ; {inc2} evSet
                  → ⊥-elim (evSet tt) })
      λ {s} rs → inj₂ (alwaysEnabled s)



  [Fw]l-t[Q∪Fx] : ∀ {m w}
                  → myWFR {m} w
                    l-t
                    ( ((m ≤_) ∩ Even) ∪ (λ s → ∃[ x ] (x < w × myWFR {m} x s)) )
  [Fw]l-t[Q∪Fx] {m} {zero}        = viaTrans d≡0⇒Q (viaInv (λ rs x → inj₁ x))
  [Fw]l-t[Q∪Fx] {m} {suc zero}    = d≡1⇒Q∪m≡0
  [Fw]l-t[Q∪Fx] {m} {suc (suc w)} =
    viaTrans
      d≡2⇒d≡1∪d≡0
      (viaInv (λ { rs (inj₁ mfr[1+w]) → inj₂ ( 1 + w , s≤s ≤-refl , mfr[1+w] )
                 ; rs (inj₂ mfr[w])   → inj₂ ( w , s≤s (m≤n+m w 1) , mfr[w]) }))




  -- From any n, we can reach any state m such that m is Even
  progressAlwaysEven : ∀ {n m : ℕ} → (n ≡_) l-t ((m ≤_) ∩ Even)
  progressAlwaysEven {n} {m} = viaWFR
                                 (myWFR {m})
                                 [P]l-t[Q∪Fx]
                                 λ w → [Fw]l-t[Q∪Fx]

