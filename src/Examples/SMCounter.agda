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


  data MyWeakFairness : EventSet → Set where
    w0 : MyWeakFairness MyEventSet

  -- Another way of modelling the WeakFairness
  MyWeakFairness2 : EventSet {Event = MyEvent} → Set
  MyWeakFairness2 MyEventSet = ⊤


  myStateMachine : StateMachine ℕ MyEvent
  myStateMachine = record { initial = 2 ≡_
                          ; enabled = MyEnabled
                          ; action = λ { {pre} {inc}  x → suc pre
                                       ; {pre} {inc2} x → suc (suc pre)} }

  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = myStateMachine
                    ; weakFairness = MyWeakFairness }

  myInvariant : Invariant myStateMachine (2 ≤_)
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
  myWFR : ∀ {m} → ℕ → Z → Set
  myWFR {m} d s = m ≡ s + d


  xx0 : ∀ {m} → (s : Z) → (m ≤ s) ⊎ ∃[ x ] myWFR {m} x s
  xx0 {m} s with m ≤? s
  ... | yes yy  = inj₁ yy
  ... | no  s<m = inj₂ (m ∸ s , sym (m+[n∸m]≡n (<⇒≤ (≰⇒> s<m))))


  progress0 : ∀ {n m} → (n ≡_) l-t ( (m ≤_) ∪ [∃ x ∶ myWFR {m} x ] )
  progress0 {n} {m} = viaEvSet MyEventSet w0
                        (λ { inc  evSet → hoare λ { refl enEv → xx0 (1 + n)}
                           ; inc2 evSet → hoare λ { refl enEv → xx0 (2 + n) }
                           })
                        (λ { inc  ¬evSet → ⊥-elim (¬evSet tt)
                           ; inc2 ¬evSet → ⊥-elim (¬evSet tt)})
                         λ rs n≡s → inc , tt , tt


  -- A state which distance to m is 0 (if we are in the state m)
  -- leads to a state greater than m
  progress1' : ∀ {m}
               → myWFR {m} 0
                 l-t
                 ( (m ≤_) ∪ [∃ x ⇒ _< 0 ∶ myWFR {m} x ] )
  progress1' {m} =
    viaEvSet
      MyEventSet w0
      (λ { inc  ⊤
           → hoare λ { {ps} refl enEv
             → inj₁ (subst ( _≤ 1 + ps) (sym (+-identityʳ ps)) (m≤n+m ps 1)) }
         ; inc2 ⊤
           → hoare λ { {ps} refl enEv
             → inj₁ (subst ( _≤ 2 + ps) (sym (+-identityʳ ps)) (m≤n+m ps 2)) }})
      (λ { inc  ⊥ → ⊥-elim (⊥ tt)
         ; inc2 ⊥ → ⊥-elim (⊥ tt) })
      λ rs F0 → inc , tt , tt



  xx2a : ∀ {m} → [ myWFR {m} 1 ] inc [ _≤_ m ∪ myWFR {m} 0 ]
  xx2a {m} = hoare λ {ps} x _ → inj₁ (≤-reflexive (trans x (+-comm ps 1)))

  xx2b : ∀ {m} → [ myWFR {m} 1 ] inc2 [ _≤_ m ∪ myWFR {m} 0 ]
  xx2b {m} = hoare λ {ps} → λ x _
                          → inj₁ (≤-step (≤-reflexive (trans x (+-comm ps 1))))

  progress2 : ∀ {m} → myWFR {m} 1 l-t ( (m ≤_) ∪ myWFR {m} 0 )
  progress2 {m} = viaEvSet MyEventSet w0 (λ { inc  ⊤ → xx2a {m}
                                         ; inc2 ⊤ → xx2b {m}
                                         }
                                      )
                                      (λ { inc  ⊥ → ⊥-elim (⊥ tt)
                                         ; inc2 ⊥ → ⊥-elim (⊥ tt)
                                         }
                                      )
                                      λ {sr} rs F1 → inc , tt , tt

  progress2' : ∀ {m}
               → myWFR {m} 1
                 l-t
                 ((m ≤_) ∪ [∃ x ⇒ _< 1 ∶ myWFR {m} x ] )
  progress2' {m} with progress2 {m}
  ...| xx = viaTrans {R = λ x → m ≤ x ⊎ m ≡ x + 0}
                     xx
                     (viaInv
                       (lemma-Imp→Inv
                         (System.stateMachine mySystem)
                         {P = λ x → m ≤ x ⊎ m ≡ x + 0}
                         {Q = ((m ≤_) ∪ (λ s → ∃[ x ] (x < 1 × myWFR {m} x s)))}
                         (λ {x₁} → λ { (inj₁ x) → inj₁ x
                                     ; (inj₂ x) → inj₂ (0 , (s≤s z≤n) , x) })))

  xx3a : ∀ {m d}
         → [ myWFR {m} (2 + d) ] inc  [ myWFR {m} (1 + d) ∪ myWFR {m} d ]
  xx3a {m} {d} = hoare (λ {ps} x _ → inj₁ (trans x ((+-suc ps (suc d)))))

  xx3b : ∀ {m d}
         → [ myWFR {m} (2 + d) ] inc2 [ myWFR {m} (1 + d) ∪ myWFR {m} d ]
  xx3b {m} {d} = hoare λ {ps} x _
                         → inj₂ (trans x (trans (+-suc ps (suc d))
                                                (cong suc (+-suc ps d)) ) )

  progress3 : ∀ {m d}
              → myWFR {m} (2 + d) l-t ( myWFR {m} (1 + d) ∪ myWFR {m} d )
  progress3 {m} {d} = viaEvSet MyEventSet w0 ( λ { inc  ⊤ → xx3a {m} {d}
                                              ; inc2 ⊤ → xx3b {m} {d} })
                                          (λ { inc  ⊥ → ⊥-elim (⊥ tt)
                                             ; inc2 ⊥ → ⊥-elim (⊥ tt) })
                                          λ {sr} rs F2+d → inc , tt , tt


  progress3' : ∀ {m w}
               → myWFR {m} (2 + w)
                 l-t
                 ( (m ≤_) ∪ [∃ x ⇒ _< (2 + w) ∶ myWFR {m} x ] )
  progress3' {m} {w} with progress3 {m} {w}
  ...| xx =
    viaTrans
      {R = (λ x → m ≡ x + suc w ⊎ m ≡ x + w)}
      xx
      (viaInv
        (lemma-Imp→Inv
          (System.stateMachine mySystem)
          {λ x → m ≡ x + suc w ⊎ m ≡ x + w}
          {(λ x → m ≤ x ⊎ Σ ℕ (λ x₁ → Σ (1 + x₁ ≤ 2 + w) (λ x₂ → m ≡ x + x₁)))}
          λ {x₃} →  λ { (inj₁ xx3) → inj₂ (1 + w , (≤-reflexive refl) , xx3 )
                      ; (inj₂ xx3) → inj₂ (w , ((s≤s (n≤1+n w)) , xx3)) }))

  progress4 : ∀ {m w}
              → myWFR {m} w
                l-t
                ((m ≤_) ∪ [∃ x ⇒ _< w ∶ myWFR {m} x ] )
  progress4 {m} {zero}        = progress1'
  progress4 {m} {suc zero}    = progress2'
  progress4 {m} {suc (suc w)} = progress3'


  -- A state equals to n leads to a state greater or equal to m, ∀ m.
  -- In other words, from n we can go to every possible state m steps
  -- away from n
  progress5 : ∀ {n m : ℕ} → (n ≡_) l-t (m ≤_)
  progress5 {n} {m} = viaWFR (myWFR {m})
                             progress0
                             λ w → progress4

