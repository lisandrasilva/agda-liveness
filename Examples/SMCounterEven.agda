{-
  Copyright 2019 Lisandra Silva

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Relation.Nullary
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_])
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

module Examples.SMCounterEven where

  -- DEFINITIONS and proofs about Even and Odd
  Even : ℕ → Set
  Even n = 2 ∣ n

  Odd : ℕ → Set
  Odd = ¬_ ∘ Even

  even? : (n : ℕ) → Dec (Even n)
  even? n = 2 ∣? n

  evenK⇒even2+K : ∀ {k} → Even k → Even (2 + k)
  evenK⇒even2+K (divides q₁ refl) = divides (1 + q₁) refl


  -- The following are mutually recursive properties.
  oddK⇒even1+K : ∀ {k} → Odd k → Even (suc k)
  oddK⇒evenK-1 : ∀ {k} → Odd k → Even (pred k)

  oddK⇒even1+K {zero} x = ⊥-elim (x (divides 0 refl))
  oddK⇒even1+K {suc k} x = evenK⇒even2+K (oddK⇒evenK-1 x)

  oddK⇒evenK-1 {zero} x = ⊥-elim (x (divides 0 refl))
  oddK⇒evenK-1 {suc k} x with even? k
  ...| no imp = ⊥-elim (x (oddK⇒even1+K imp))
  ...| yes prf = prf


  odd1 : Odd 1
  odd1 (divides zero ())
  odd1 (divides (suc q₁) ())


   -----------------------------------------------------------------------------
   -- SPECIFICATION
   -----------------------------------------------------------------------------

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



   -----------------------------------------------------------------------------
   -- PROOFS
   -----------------------------------------------------------------------------

  open LeadsTo ℕ MyEvent MySystem

  -- In every state there is always an enabled transition
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
                   λ {s} rs n≡s → alwaysEnabled s

  -- QUESTION : Although we don't have weakfairness (WF) on event inc it was
  -- possible to prove this.
  -- ANSWER : This is because of the 2nd constraint in the viaEvSet constructor:
  --      - ∀ event e ∉ WF (in this case only inc) → [P] e [P ∪ Q], in this case
  --   we achieve Q (Even), because the event inc is enabled only in Odd states.


  -- REFACTOR: Maybe m is the one that should be explicit
  myWFR : ∀ {m} → ℕ → Z → Set
  myWFR {m} d s = m ≡ d + s


  -- For every even state s, or s is greater than m or there is a distance x
  -- between s and m
  [Q∪Fx] :  ∀ {m} → (s : Z) → Even s → (m ≤ s × Even s) ⊎ ∃[ x ] myWFR {m} x s
  [Q∪Fx] {m} s sEven with m ≤? s
  ... | yes m≤s = inj₁ (m≤s , sEven)
  ... | no  s<m = inj₂ ( m ∸ s , sym (m∸n+n≡m (<⇒≤ (≰⇒> s<m))) )


  -- First constraint for WFR rule
  [P]l-t[Q∪Fx] : ∀ {n m}
                 → (n ≡_) l-t ( ((m ≤_) ∩ Even) ∪ [∃ x ∶ myWFR {m} x ] )
  [P]l-t[Q∪Fx] {n} {m} = viaEvSet
                           MyEventSet
                           (λ { {inc2} evSet
                                → hoare λ { refl (even x)
                                  → [Q∪Fx] (2 + n) (evenK⇒even2+K x) }})
                           (λ { {inc}  evSet
                                → hoare λ { refl (odd x)
                                  → inj₂ ([Q∪Fx] (1 + n) (oddK⇒even1+K x))}
                              ; {inc2} evSet → ⊥-elim (evSet tt) })
                           λ {s} rs n≡s → alwaysEnabled s



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
                   ; {inc2} evSet → ⊥-elim (evSet tt) })
                λ {s} rs F0 → alwaysEnabled s


  -- If we are at distance 1 from m, which means m ≡ s + 1.
  -- If s is odd then s is incremented by 1 (because of the enabling
  -- condition) then we go to an even state s₁ ≡ s + 1 ≡ m.
  -- If if s is even then s is incremented by 2, which leads to a state
  -- s₁ ≡ s + 2 > s + 1 ≡ m. As so, m ≤ s₁ ∩ Even s₁ will always  hold.
  d≡1⇒Q∪d≡0 : ∀ {m}
              → myWFR {m} 1
                l-t
                ( ((m ≤_) ∩ Even) ∪ [∃ x ⇒ _< 1 ∶ myWFR {m} x ] )
  d≡1⇒Q∪d≡0 {m} = viaEvSet
                    MyEventSet
                    (λ { {inc2} evSet
                         → hoare λ { {ps} refl (even x)
                           → inj₁ (m≤n+m (suc ps) 1 , evenK⇒even2+K x) }})
                    (λ { {inc} evSet
                         → hoare λ { {ps} refl (odd x)
                           → inj₂ (inj₁ (≤-refl , oddK⇒even1+K x) )}
                       ; {inc2} evSet → ⊥-elim (evSet tt) })
                    λ {s} rs F1 → alwaysEnabled s


  -- Auxiliary properties
  assoc∘comm : ∀ {w s : ℕ} n → n + w + s ≡ w + (n + s)
  assoc∘comm {w} {s} n = trans (cong (_+ s) (+-comm n w)) (+-assoc w n s)

  assoc∘assoc : ∀ {w s : ℕ} n p → (n + p) + w + s ≡ n + w + (p + s)
  assoc∘assoc {w} {s} n p
    rewrite +-assoc n p w
          | +-comm p w
          | +-assoc n (w + p) s
          | +-assoc w p s
          | +-assoc n w (p + s) = refl


  -- If we are at a distance greater o equal to 2 then with we decrease the
  -- distance in 1 or 2, because we can jump 1 or 2 states (inc or onc2)
  -- This property together with d≡0⇒Q and d≡1⇒Q∪d≡0 allows to prove the
  -- second constraint for the WFR rule (see below)
  [d≡2+w]⇒[d≡1+w]∪[d≡w] : ∀ {m w}
                → myWFR {m} (2 + w)
                  l-t
                  ( myWFR {m} (1 + w) ∪ myWFR {m} w )
  [d≡2+w]⇒[d≡1+w]∪[d≡w] {m} {w} =
    viaEvSet
      MyEventSet
      (λ { {inc2} evSet
                  → hoare λ { {ps} refl enEv → inj₂ (assoc∘comm 2) }})
      (λ { {inc} evSet
                  → hoare λ { {ps} refl enEv → inj₂ (inj₁ (assoc∘assoc 1 1))}
         ; {inc2} evSet
                  → ⊥-elim (evSet tt) })
      λ {s} rs F2+d → alwaysEnabled s


  -- Second constraint for WFR rule
  [Fw]l-t[Q∪Fx] : ∀ {m w}
                  → myWFR {m} w
                    l-t
                    ( ((m ≤_) ∩ Even) ∪ [∃ x ⇒ _< w ∶ myWFR {m} x ] )
  [Fw]l-t[Q∪Fx] {m} {zero}        = viaTrans d≡0⇒Q (viaInv (λ rs x → inj₁ x))
  [Fw]l-t[Q∪Fx] {m} {suc zero}    = d≡1⇒Q∪d≡0
  [Fw]l-t[Q∪Fx] {m} {suc (suc w)} =
    viaTrans
      [d≡2+w]⇒[d≡1+w]∪[d≡w]
      (viaInv (λ { rs (inj₁ mfr[1+w]) → inj₂ ( 1 + w , s≤s ≤-refl , mfr[1+w] )
                 ; rs (inj₂ mfr[w])   → inj₂ ( w , s≤s (m≤n+m w 1) , mfr[w]) }))




  ------------------------------------------------------------------------------
  -- MAIN PROPERTY
  ------------------------------------------------------------------------------
  -- From any n, we can reach any state m such that m is Even
  progressAlwaysEven : ∀ {n m : ℕ} → (n ≡_) l-t ((m ≤_) ∩ Even)
  progressAlwaysEven {n} {m} = viaWFR
                                 (myWFR {m})
                                 [P]l-t[Q∪Fx]
                                 λ w → [Fw]l-t[Q∪Fx]

