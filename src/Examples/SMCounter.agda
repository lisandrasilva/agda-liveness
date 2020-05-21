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

open import Prelude
open import Relation.Binary.HeterogeneousEquality
            using (_≅_)
            renaming (cong to ≅-cong; refl to ≅-refl)

open import StateMachineModel

module Examples.SMCounter where

  data MyEvent : Set where
    inc  : MyEvent
    inc2 : MyEvent

  data MyEnabled : MyEvent → ℕ → Set where
    tt : ∀ {e} {n} → MyEnabled e n


  MyEventSet : EventSet {Event = MyEvent}
  MyEventSet inc  = ⊤
  MyEventSet inc2 = ⊤


  MyAction : {preSt : ℕ} {ev : MyEvent} → MyEnabled ev preSt → ℕ
  MyAction {preSt} {inc} enEv = suc preSt
  MyAction {preSt} {inc2} enEv = suc (suc preSt)


  data MyWeakFairness : EventSet → Set where
    w0 : MyWeakFairness MyEventSet

  -- Another way of modelling the WeakFairness
  MyWeakFairness2 : EventSet {Event = MyEvent} → Set
  MyWeakFairness2 MyEventSet = ⊤


  MyStateMachine : StateMachine ℕ MyEvent
  MyStateMachine = record { initial = 2 ≡_
                          ; enabled = MyEnabled
                          ; action  = MyAction }

  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = MyStateMachine
                    ; weakFairness = MyWeakFairness }

  myInvariant : Invariant MyStateMachine (2 ≤_)
  myInvariant (init x) = ≤-reflexive x
  myInvariant (step {ps} {inc} rs enEv) = ≤-stepsˡ 1 (myInvariant rs)
  myInvariant (step {ps} {inc2} rs enEv) = ≤-stepsˡ 2 (myInvariant rs)


  open LeadsTo ℕ MyEvent mySystem


  -- A state equals to n leads to a state equals to (1 + n) or equals to (2 + n)
  progressDumb : ∀ {n : ℕ} → (n ≡_) l-t ((1 + n ≡_) ∪ (2 + n ≡_))
  progressDumb = viaEvSet MyEventSet w0
                           ( λ { inc  ⊤ → hoare λ { refl enEv → inj₁ refl}
                               ; inc2 ⊤ → hoare λ { refl enEv → inj₂ refl} })
                           ( λ { inc  ⊥ → ⊥-elim (⊥ tt)
                               ; inc2 ⊥ → ⊥-elim (⊥ tt)} )
                           λ rs n≡s → inc , tt , tt

  n<m+n : ∀ {n m} → 0 < m → n < m + n
  n<m+n {zero}  {suc m} x = s≤s z≤n
  n<m+n {suc n} {suc m} x = s≤s (m≤n+m (suc n) m)



  progress-< : ∀ n → (n ≡_) l-t (n <_)
  progress-< n = viaTrans
                   progressDumb
                   (viaInv (λ { rs (inj₁ refl) → s≤s ≤-refl
                              ; rs (inj₂ refl) → s≤s (m≤n+m n 1)}))

  {- A predicate on states, parameterized by m (target). The d parameter is the
     "distance" from the target m from state s.

     QUESTION : We are generalizing Z to be of a given type, however in myWFR
     we are using it knowing that is ℕ because we apply _≡_ and _+_
  -}
  F : ∀ {m} → ℕ → Z → Set
  F {m} d s = m ≡ d + s


  wfr-1 : ∀ {m} → (s : Z) → (m ≤ s) ⊎ ∃[ x ] F {m} x s
  wfr-1 {m} s with m ≤? s
  ... | yes yy  = inj₁ yy
  ... | no  s<m = inj₂ (m ∸ s , sym (m∸n+n≡m (≰⇒≥ s<m)) )


  progress-1st : ∀ {n m} → (n ≡_) l-t ( (m ≤_) ∪ [∃ x ∶ F {m} x ] )
  progress-1st {n} {m} = viaInv (λ {s} rs n≡s → wfr-1 s)


  -- A state which distance to m is 0 (if we are in the state m)
  -- leads to a state greater than m
  progress-d0 : ∀ {m} → F {m} 0 l-t ( (m ≤_) ∪ [∃ x ⇒ _< 0 ∶ F {m} x ] )
  progress-d0 {m} = viaInv (λ { {s} rs refl → inj₁ ≤-refl })



  progress-d1 : ∀ {m} → F {m} 1 l-t ((m ≤_) ∪ [∃ x ⇒ _< 1 ∶ F {m} x ] )
  progress-d1 {m} =
    viaEvSet
      MyEventSet
      w0
      (λ { inc  ⊤ → hoare (λ { refl _ → inj₁ ≤-refl })
         ; inc2 ⊤ → hoare (λ { refl _ → inj₁ (≤-step ≤-refl) })
         })
      (λ { inc  ⊥ → ⊥-elim (⊥ tt)
         ; inc2 ⊥ → ⊥-elim (⊥ tt)
         })
      λ _ _ → inc , tt , tt



  progress-d2 : ∀ {m w} → F {m} (2 + w) l-t ( (m ≤_) ∪ [∃ x ⇒ _< (2 + w) ∶ F {m} x ] )
  progress-d2 {m} {w} =
    viaEvSet
      MyEventSet
      w0
      (λ { inc ⊤ → hoare λ { {ps} refl _
                     → inj₂ (suc w , ≤-refl , cong suc (sym (+-suc w ps)) )}
         ; inc2 ⊤ → hoare λ { {ps} refl _
                     → inj₂ (w , ≤-step ≤-refl , sym (trans (+-suc w (suc ps))
                                                     (cong suc (+-suc w ps)))) }
         })
      (λ { inc  ⊥ → ⊥-elim (⊥ tt)
         ; inc2 ⊥ → ⊥-elim (⊥ tt) })
      λ _ _ → inc , tt , tt


  progress-2nd : ∀ {m w}
              → F {m} w
                l-t
                ((m ≤_) ∪ [∃ x ⇒ _< w ∶ F {m} x ] )
  progress-2nd {m} {zero}        = progress-d0
  progress-2nd {m} {suc zero}    = progress-d1
  progress-2nd {m} {suc (suc w)} = progress-d2


  -- A state equals to n leads to a state greater or equal to m, ∀ m.
  -- In other words, from n we can go to every possible state m steps
  -- away from n
  progress : ∀ {n m : ℕ} → (n ≡_) l-t (m ≤_)
  progress {n} {m} = viaWFR (F {m})
                             progress-1st
                             λ w → progress-2nd


