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
open import Data.Fin hiding (_≟_; _<_; _+_; pred; _≤_; lift)
open import Data.List
open import Data.List.Properties
open import Relation.Nullary.Negation using (contradiction ; contraposition)



open import StateMachineModel


module Examples.ProducerConsumer2
  {ℓ : Level}
  (Message : Set ℓ) -- Message type
  --(Size : ℕ) -- Size of the bounded buffer
  where


  -----------------------------------------------------------------------------
  -- SPECIFICATION
  -----------------------------------------------------------------------------
  record State : Set (lsuc ℓ) where
    field
     produced   : List Message
     consumed   : List Message
     |consumed| : ℕ
  open State



  data MyEvent : Set ℓ where
    produce : Message → MyEvent
    consume : Message → MyEvent



  data MyEnabled : MyEvent → State → Set ℓ where
    prodEnabled : ∀ {st : State} {msg} -- always enabled
                  → MyEnabled (produce msg) st
    consEnabled : ∀ {st : State} {msg}
                  → (cons<prod : |consumed| st < length (produced st) )
                  → msg ≡ lookup (produced st) (fromℕ≤ cons<prod)
                  → MyEnabled (consume msg) st




  MyAction : ∀ {preState : State} {event : MyEvent}
             → MyEnabled event preState
             → State
  MyAction {preSt} {produce m} enabled = record preSt
                                          { produced  = produced preSt ++ [ m ]
                                          }
  MyAction {preSt} {consume m} enabled = record preSt
                                          { consumed  = consumed preSt ++ [ m ]
                                          ; |consumed| = suc (|consumed| preSt)
                                          }


  initialState : State
  initialState = record
                   { produced   = []
                   ; consumed   = []
                   ; |consumed| = 0
                   }


  MyStateMachine : StateMachine State MyEvent
  MyStateMachine = record
                     { initial = λ state → state ≡ initialState
                     ; enabled = MyEnabled
                     ; action  = MyAction
                     }


  MyEventSet : EventSet {Event = MyEvent}
  MyEventSet (produce x) = ⊥
  MyEventSet (consume x) = ⊤


  data MyWeakFairness : EventSet → Set ℓ where
    wf : MyWeakFairness MyEventSet


  MySystem : System State MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }

  -----------------------------------------------------------------------------
  -- PROOFS
  -----------------------------------------------------------------------------
  open LeadsTo State MyEvent MySystem

  myWFR : ∀ {n} → Z → State → Set
  myWFR {n} d st =  d + |consumed| st ≡ n × n < length (produced st)


  length-suc : ∀ {x : Message} l → length (l ++ [ x ]) ≡ 1 + length l
  length-suc {x} l rewrite length-++ l {[ x ]} | +-comm (length l) 1 = refl

  inv-cons≤prod : Invariant
                    MyStateMachine
                    λ state → |consumed| state ≤ length (produced state)
  inv-cons≤prod (init refl) = z≤n
  inv-cons≤prod (step {st} {produce x} rs enEv)
    rewrite length-suc {x} (produced st) = ≤-step (inv-cons≤prod rs)
  inv-cons≤prod (step {event = consume x} rs (consEnabled c<p x₁)) = c<p



  m≤n⇒m≡n⊎m<n : ∀ {m n} → m ≤ n → m ≡ n ⊎ m < n
  m≤n⇒m≡n⊎m<n {0} {0} z≤n = inj₁ refl
  m≤n⇒m≡n⊎m<n {0} {suc n} x = inj₂ (s≤s z≤n)
  m≤n⇒m≡n⊎m<n {suc m} {suc n} (s≤s x)
    with m≤n⇒m≡n⊎m<n x
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ m<n  = inj₂ (s≤s m<n)


  [Q∪Fx] : ∀ {st : State} {n}
           → length (produced st) ≡ n
           → |consumed| st ≤ n
           → |consumed| st ≡ n ⊎ ∃[ x ] myWFR {n} x st
  [Q∪Fx] {st} {n} refl cons≤n
    with m≤n⇒m≡n⊎m<n cons≤n
  ... | inj₁ cons≡n = inj₁ cons≡n
  ... | inj₂ cons<n = inj₂ ( n ∸ |consumed| st , m∸n+n≡m cons≤n , {!!} )



  wfr-l++ : ∀ {m : Message} {n} l
                → n < length l
                → length (l ++ [ m ]) ∸ 1 ∸ n + n ≡ length l
                × length l < length (l ++ [ m ])
  wfr-l++ {m} {n} l n<l rewrite length-suc {m} l
    = (m∸n+n≡m (<⇒≤ n<l)) , ≤-refl


  [P]l-t[Q∪Fx] : ∀ {n}
                 → ( λ preSt → length (produced preSt) ≡ n × |consumed| preSt < n)
                   l-t
                   ( (λ posSt → |consumed| posSt ≡ n) ∪ [∃ x ∶ myWFR {n} x ] )
  [P]l-t[Q∪Fx] =
    viaEvSet
      MyEventSet
      wf
      ( λ { (consume m) evSet
              → hoare λ { {st} (p≡n , c<p) enEv
                          → [Q∪Fx] {MyAction {st} enEv}
                                   p≡n c<p
                        }
          }
      )
      (λ { (produce m) x
             → hoare λ { {st} (refl , c<p) enEv
                         → let l = length (produced st ++ [ m ]) ∸ 1
                               c = (|consumed| st)
                           in inj₂ (inj₂ ( l ∸ c , wfr-l++ (produced st) c<p))}
         ; (consume x₁) ⊥ → ⊥-elim (⊥ tt)
         }
      )
      λ { {state} rs (refl , c<p)
          → consume (lookup (produced state) (fromℕ≤ c<p))
          , tt
          , (consEnabled c<p refl) }



  m+n<o⇒n<o : ∀ {l} w m → w + m < l → m < l
  m+n<o⇒n<o w m w+m<l rewrite sym (+-suc w m) = m+n≤o⇒n≤o w w+m<l

  mono-l++ : ∀ {n} (m : Message) l → n < length l → n < length (l ++ [ m ])
  mono-l++ m l n<l rewrite length-suc {m} l = ≤-step n<l


  [Fw]l-t[Q∪Fx] : ∀ {w n}
                  → myWFR {n} w
                    l-t
                    ( (λ posSt → |consumed| posSt ≡ n)
                      ∪ [∃ x ⇒ _< w ∶ myWFR {n} x ] )
  [Fw]l-t[Q∪Fx] {0} = viaInv λ { rs (c≡n , c<p) → inj₁ c≡n }
  [Fw]l-t[Q∪Fx] {suc w} {n} =
    viaEvSet
      MyEventSet
      wf
      (λ { (consume m) ⊤ → hoare λ { {st} (refl , c<p) (consEnabled cons<prod x)
                           → inj₂ (w , ≤-refl , +-suc w (|consumed| st) , c<p ) }})
      (λ { (produce m) ⊥ → hoare λ { {st} (c≡n , n<p) enEv
                                 → inj₁ (c≡n , mono-l++ m (produced st) n<p) }
         ; (consume m) ⊥ → ⊥-elim (⊥ tt) })
      λ { {st} rs (refl , n<p) → let c<l = m+n<o⇒n<o (suc w) (|consumed| st) n<p
                                   in consume (lookup (produced st) (fromℕ≤ c<l))
                                     , tt
                                     , (consEnabled c<l refl) }



  progressOnLenght : ∀ n
                     → ( λ preSt → length (produced preSt) ≡ n
                                 × |consumed| preSt < n)
                       l-t
                       ( λ posSt → |consumed| posSt ≡ n)
  progressOnLenght n = viaWFR
                           myWFR
                           [P]l-t[Q∪Fx]
                           λ w → [Fw]l-t[Q∪Fx]



  progressLookup : ∀ {n : ℕ} {msg}
                   → ( λ preSt → (prf : n < length (produced preSt))
                               → lookup (produced preSt) (fromℕ≤ prf) ≡ msg )
                     l-t
                     ( λ posSt → (prf : n < length (consumed posSt))
                               → lookup (consumed posSt) (fromℕ≤ prf) ≡ msg )


  progress : ∀ {n} {msgs}
             → ( λ preSt → take n (produced preSt) ≡ msgs )
               l-t
               ( λ state → take n (consumed state) ≡ msgs )
