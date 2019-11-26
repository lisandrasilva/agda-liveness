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
  open State



  data MyEvent : Set ℓ where
    produce : Message → MyEvent
    consume : Message → MyEvent



  data MyEnabled : MyEvent → State → Set ℓ where
    prodEnabled : ∀ {st : State} {msg} -- always enabled
                  → MyEnabled (produce msg) st
    consEnabled : ∀ {st : State} {msg}
                  → (cons<prod : length (consumed st) < length (produced st) )
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
                                          }


  initialState : State
  initialState = record
                   { produced   = []
                   ; consumed   = []
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
  myWFR {n} d st =  d + length (consumed st) ≡ n × n ≤ length (produced st)



  length-suc : ∀ {x : Message} l → length (l ++ [ x ]) ≡ 1 + length l
  length-suc {x} l rewrite length-++ l {[ x ]} | +-comm (length l) 1 = refl



  <⇒≤-List : ∀ {n} (m : Message) (l : List Message)
             → length l < n
             → length (l ++ [ m ]) ≤ n
  <⇒≤-List m l l<n rewrite length-suc {m} l = l<n



  suc-+-List : ∀ {w} (m : Message) (l : List Message)
               →  w + length (l ++ m ∷ []) ≡ suc (w + length l)
  suc-+-List {w} m l rewrite length-suc {m} l = +-suc w (length l)



  inv-cons≤prod : Invariant
                    MyStateMachine
                    λ state → length (consumed state) ≤ length (produced state)
  inv-cons≤prod (init refl) = z≤n
  inv-cons≤prod (step {st} {produce m} rs enEv)
    rewrite length-suc {m} (produced st)
      = ≤-step (inv-cons≤prod rs)
  inv-cons≤prod (step {st} {consume m} rs (consEnabled c<p x₁))
      = <⇒≤-List m (consumed st) c<p
      --subst (_≤ length (produced st)) (sym (length-suc {m} (consumed st))) c<p



  m≤n⇒m≡n⊎m<n : ∀ {m n} → m ≤ n → m ≡ n ⊎ m < n
  m≤n⇒m≡n⊎m<n {0} {0} z≤n = inj₁ refl
  m≤n⇒m≡n⊎m<n {0} {suc n} x = inj₂ (s≤s z≤n)
  m≤n⇒m≡n⊎m<n {suc m} {suc n} (s≤s x)
    with m≤n⇒m≡n⊎m<n x
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ m<n  = inj₂ (s≤s m<n)



  [Q∪Fx] : ∀ {st : State} {n}
           → length (produced st) ≡ n
           → length (consumed st) ≤ n
           → length (consumed st) ≡ n ⊎ ∃[ x ] myWFR {n} x st
  [Q∪Fx] {st} {n} refl cons≤n
    with m≤n⇒m≡n⊎m<n cons≤n
  ... | inj₁ cons≡n = inj₁ cons≡n
  ... | inj₂ cons<n = inj₂ ( n ∸ length (consumed st) , m∸n+n≡m cons≤n , ≤-refl )



  wfr-l++ : ∀ {m : Message} {n} l
                → n < length l
                → length (l ++ [ m ]) ∸ 1 ∸ n + n ≡ length l
                × length l ≤ length (l ++ [ m ])
  wfr-l++ {m} {n} l n<l rewrite length-suc {m} l
    = (m∸n+n≡m (<⇒≤ n<l)) , ≤-step ≤-refl



{-  [P]l-t[Q∪Fx] : ∀ {n}
                 → λ preSt → length (produced preSt) ≡ n
                           × length (consumed preSt) < n
                   l-t
                   (λ posSt → length (consumed posSt) ≡ n) ∪ [∃ x ∶ myWFR {n} x ]
-}
  [P]l-t[Q∪Fx] : ∀ {n}
                 → (_≡ n) ∘ length ∘ produced   ∩   (_< n) ∘ length ∘ consumed
                   l-t
                   (_≡ n) ∘ length ∘ consumed   ∪   [∃ x ∶ myWFR {n} x ]
  [P]l-t[Q∪Fx] =
    viaEvSet
      MyEventSet
      wf
      ( λ { (consume m) evSet
              → hoare λ { {st} (p≡n , c<p) enEv → let state = MyAction {st} enEv
                                                      cons  = consumed st
                                                      c≤p   = <⇒≤-List m cons c<p
                                                  in [Q∪Fx] {state} p≡n c≤p }
          }
      )
      (λ { (produce m) x
             → hoare λ { {st} (refl , c<p) enEv
                         → let l = length (produced st ++ [ m ]) ∸ 1
                               c = length (consumed st)
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

  mono-l++ : ∀ {n} (m : Message) l → n ≤ length l → n ≤ length (l ++ [ m ])
  mono-l++ m l n<l rewrite length-suc {m} l = ≤-step n<l


{-[Fw]l-t[Q∪Fx] : ∀ {w n}
                  → myWFR {n} w
                    l-t
                    (λ posSt → length (consumed posSt) ≡ n)
                    ∪ [∃ x ⇒ _< w ∶ myWFR {n} x ]
-}
  [Fw]l-t[Q∪Fx] : ∀ {n} w
                  → myWFR {n} w
                    l-t
                    (_≡ n) ∘ length ∘ consumed   ∪   [∃ x ⇒ _< w ∶ myWFR {n} x ]
  [Fw]l-t[Q∪Fx] 0 = viaInv λ { rs (c≡n , c<p) → inj₁ c≡n }
  [Fw]l-t[Q∪Fx] (suc w) =
    viaEvSet
      MyEventSet
      wf
      (λ { (consume m) ⊤ → hoare λ { {st} (refl , c<p) (consEnabled cons<prod x)
                           → inj₂ (w , ≤-refl , suc-+-List m (consumed st) , c<p)}
         }
      )
      (λ { (produce m) ⊥ → hoare λ { {st} (c≡n , n≤p) enEv
                                 → inj₁ (c≡n , mono-l++ m (produced st) n≤p) }
         ; (consume m) ⊥ → ⊥-elim (⊥ tt)
         }
      )
      λ { {st} rs (refl , n<p) → let c<l = m+n<o⇒n<o w (length (consumed st)) n<p
                                 in consume (lookup (produced st) (fromℕ≤ c<l))
                                  , tt
                                  , (consEnabled c<l refl) }


{-P2-l-t-Q : ∀ {n}
            → λ preSt → length (produced preSt) ≡ n
                      × length (consumed preSt) < n
              l-t
              λ posSt → length (consumed posSt) ≡ n
-}
  P2-l-t-Q : ∀ {n}
             → (_≡ n) ∘ length ∘ produced   ∩   (_< n) ∘ length ∘ consumed
               l-t
               (_≡ n) ∘ length ∘ consumed
  P2-l-t-Q = viaWFR
               myWFR
               [P]l-t[Q∪Fx]
               [Fw]l-t[Q∪Fx]



  P⊆P1∪P2 : ∀ {ℓ} { P : Set ℓ } (m n : ℕ) → P → P × m ≡ n ⊎ P × m ≢ n
  P⊆P1∪P2 m n p with m ≟ n
  ... | yes prf = inj₁ (p , prf)
  ... | no  imp = inj₂ (p , imp)


{-c≢n-l-t-c<n : ∀ {n} → ( λ preSt → length (produced preSt) ≡ n
                                  × length (consumed preSt) ≢ n )
                        l-t
                        ( λ posSt → length (produced posSt) ≡ n
                                  × length (consumed posSt) < n )
-}
  c≢n-l-t-c<n : ∀ {n}
                → (_≡ n) ∘ length ∘ produced   ∩  (_≢ n) ∘ length ∘ consumed
                  l-t
                  (_≡ n) ∘ length ∘ produced   ∩  (_< n) ∘ length ∘ consumed
  c≢n-l-t-c<n =
    viaInv ( λ { {st} rs (refl , c≢n) → refl , ≤∧≢⇒< (inv-cons≤prod rs) c≢n } )



  progressOnLength : ∀ n
                     → (_≡ n) ∘ length ∘ produced
                       l-t
                       (_≡ n) ∘ length ∘ consumed
  progressOnLength n =
    viaDisj
      ( λ {st} p≡n → P⊆P1∪P2 (length (consumed st)) n p≡n )
      ( viaInv
          λ { {st} rs (_ , c≡n) → c≡n }
      )
      ( viaTrans
          c≢n-l-t-c<n
          P2-l-t-Q
      )



  lookup-l₂-++ : ∀ {n} {m : Message} l₁ l₂
                 → (finl₁ : n < length l₁) → (finl₂ : n < length l₂)
                 → (fin++ : n < length (l₂ ++ [ m ]))
                 → lookup l₁ (fromℕ≤ finl₁) ≡ lookup l₂ (fromℕ≤ finl₂)
                 → lookup l₁ (fromℕ≤ finl₁) ≡ lookup (l₂ ++ [ m ]) (fromℕ≤ fin++)


  lookup-l₁-++ : ∀ {n} {m : Message} l₁ l₂
                 → (finl₁ : n < length l₁) → (finl₂ : n < length l₂)
                 → (fin++ : n < length (l₁ ++ [ m ]))
                 → (finll : length l₁ < length l₂)
                 → lookup l₁ (fromℕ≤ finl₁) ≡ lookup l₂ (fromℕ≤ finl₂)
                 → m ≡ lookup l₂ (fromℕ≤ finll)
                 → lookup (l₁ ++ [ m ]) (fromℕ≤ fin++) ≡ lookup l₂ (fromℕ≤ finl₂)


  n<l++⇒n<l⊎n≡l : ∀ {n} {m : Message} l₁
                  → n < length (l₁ ++ [ m ])
                  → n < length l₁ ⊎ n ≡ length l₁
  n<l++⇒n<l⊎n≡l = {!!}

  lookup-length-l₁ : ∀ {m : Message} l₁
                     → (prf : length l₁ < length (l₁ ++ [ m ]))
                     → lookup (l₁ ++ [ m ]) (fromℕ≤ prf) ≡ m

  <-refl-list : ∀ {m : Message} l
                → length l < length (l ++ [ m ])



  lookup-c≡lookup-p : ∀ {n}
                    → Invariant
                        MyStateMachine
                        λ st → (prfC : n < length (consumed st))
                             → (prfP : n < length (produced st))
                             → lookup (consumed st) (fromℕ≤ prfC)
                             ≡ lookup (produced st) (fromℕ≤ prfP)
  lookup-c≡lookup-p {n} (init refl) () ()
  lookup-c≡lookup-p {n} (step {st} {produce x} rs enEv) prfC prfP
    = let c<p = <-transˡ prfC (inv-cons≤prod rs)
      in lookup-l₂-++
           (consumed st) (produced st)
           prfC c<p prfP
           (lookup-c≡lookup-p rs prfC c<p)
  lookup-c≡lookup-p {n} (step {st} {consume m} rs enEv) prfC prfP
    with enEv
  ... | consEnabled cons<prod m≡lookup
      with n<l++⇒n<l⊎n≡l (consumed st) prfC
  ... | inj₁ n<c  = lookup-l₁-++
                      (consumed st) (produced st)
                      n<c prfP prfC cons<prod
                      (lookup-c≡lookup-p rs n<c prfP) m≡lookup
  ... | inj₂ refl = trans
                      (lookup-length-l₁ (consumed st) (<-refl-list (consumed st)))
                      m≡lookup



  [c]-prefix-[p] : ∀ {n}
                   → Invariant
                       MyStateMachine
                       λ st → n ≤ length (consumed st)
                            → take n (consumed st) ≡ take n (produced st)
  [c]-prefix-[p] {n} (init refl) x = refl
  [c]-prefix-[p] {zero}  (step {st} {ev} rs enEv) x = refl
  [c]-prefix-[p] {suc n} (step {st} {ev} rs enEv) x = {!!}
  {- cons-prefix-prod {suc n} (step {st} {produce m} rs enEv) x
    with inv-cons≤prod rs
  ... | cons≤prod = {!!}
  --  with consumed st | produced st
  --... | m₁ ∷ l₁ | m₂ ∷ l₂ = {!!}
  cons-prefix-prod {suc n} (step {st} {consume x₁} rs enEv) x = {!!} -}



  progressLookup : ∀ {n : ℕ} {msg}
                   → ( λ preSt → (prf : n < length (produced preSt))
                               → lookup (produced preSt) (fromℕ≤ prf) ≡ msg )
                     l-t
                     ( λ posSt → (prf : n < length (consumed posSt))
                               → lookup (consumed posSt) (fromℕ≤ prf) ≡ msg )



  progress : ∀ {n} {msgs}
             → (_≡ msgs) ∘ take n ∘ produced
               l-t
               (_≡ msgs) ∘ take n ∘ consumed
