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



  <⇒≤-l : ∀ {n} (m : Message) (l : List Message)
             → length l < n
             → length (l ++ [ m ]) ≤ n
  <⇒≤-l m l l<n rewrite length-suc {m} l = l<n



  suc-+-l : ∀ {w} (m : Message) (l : List Message)
               →  w + length (l ++ m ∷ []) ≡ suc (w + length l)
  suc-+-l {w} m l rewrite length-suc {m} l = +-suc w (length l)



  inv-cons≤prod : Invariant
                    MyStateMachine
                    λ state → length (consumed state) ≤ length (produced state)
  inv-cons≤prod (init refl) = z≤n
  inv-cons≤prod (step {st} {produce m} rs enEv)
    rewrite length-suc {m} (produced st)
      = ≤-step (inv-cons≤prod rs)
  inv-cons≤prod (step {st} {consume m} rs (consEnabled c<p x₁))
      = <⇒≤-l m (consumed st) c<p
      --subst (_≤ length (produced st)) (sym (length-suc {m} (consumed st))) c<p



  m≤n⇒m≡n⊎m<n : ∀ {m n} → m ≤ n → m < n ⊎ m ≡ n
  m≤n⇒m≡n⊎m<n {0} {0} z≤n = inj₂ refl
  m≤n⇒m≡n⊎m<n {0} {suc n} x = inj₁ (s≤s z≤n)
  m≤n⇒m≡n⊎m<n {suc m} {suc n} (s≤s x)
    with m≤n⇒m≡n⊎m<n x
  ... | inj₁ m<n  = inj₁ (s≤s m<n)
  ... | inj₂ refl = inj₂ refl



  [Q∪Fx] : ∀ {st : State} {n}
           → length (produced st) ≡ n
           → length (consumed st) ≤ n
           → length (consumed st) ≡ n ⊎ ∃[ x ] myWFR {n} x st
  [Q∪Fx] {st} {n} refl cons≤n
    with m≤n⇒m≡n⊎m<n cons≤n
  ... | inj₂ cons≡n = inj₁ cons≡n
  ... | inj₁ cons<n = inj₂ ( n ∸ length (consumed st) , m∸n+n≡m cons≤n , ≤-refl )



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
                                                      c≤p   = <⇒≤-l m cons c<p
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
                           → inj₂ (w , ≤-refl , suc-+-l m (consumed st) , c<p)}
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



  lookup-++ : ∀ {n} {m : Message} l₁ l₂
                 → (finl₁ : n < length l₁) → (finl₂ : n < length l₂)
                 → (fin++ : n < length (l₂ ++ [ m ]))
                 → lookup l₁ (fromℕ≤ finl₁) ≡ lookup l₂ (fromℕ≤ finl₂)
                 → lookup l₁ (fromℕ≤ finl₁) ≡ lookup (l₂ ++ [ m ]) (fromℕ≤ fin++)
  lookup-++ {zero}  (x ∷ l₁) (x₁ ∷ l₂) finl₁ finl₂ fin++ ll₁≡ll₂ = ll₁≡ll₂
  lookup-++ {suc n} (x ∷ l₁) (x₁ ∷ l₂) finl₁ finl₂ fin++ ll₁≡ll₂
    = lookup-++ l₁ l₂ (≤-pred finl₁) (≤-pred finl₂) (≤-pred fin++) ll₁≡ll₂



  n≤l++⇒n≤l⊎n≡l : ∀ {m : Message} {n} l
                  → n ≤ length (l ++ [ m ])
                  → n ≤ length l ⊎ n ≡ 1 + length l
  n≤l++⇒n≤l⊎n≡l {m} l n≤l++ rewrite length-suc {m} l
    with m≤n⇒m≡n⊎m<n n≤l++
  ... | inj₁ 1+n≤1+l = inj₁ (≤-pred 1+n≤1+l)
  ... | inj₂ n≡1+l   = inj₂ n≡1+l




  lookup-length : ∀ {m : Message} l
                     → (prf : length l < length (l ++ [ m ]))
                     → lookup (l ++ [ m ]) (fromℕ≤ prf) ≡ m
  lookup-length [] prf = refl
  lookup-length (x ∷ l) prf = lookup-length l (≤-pred prf)



  <-refl-l : ∀ {m : Message} l → length l < length (l ++ [ m ])
  <-refl-l [] = s≤s z≤n
  <-refl-l (x ∷ l) = s≤s (<-refl-l l)



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
      in lookup-++
           (consumed st) (produced st)
           prfC c<p prfP
           (lookup-c≡lookup-p rs prfC c<p)
  lookup-c≡lookup-p {n} (step {st} {consume m} rs enEv) prfC prfP
    with enEv
  ... | consEnabled cons<prod m≡lookup
      with n≤l++⇒n≤l⊎n≡l (consumed st) prfC
  ... | inj₁ n<c  = sym (lookup-++
                          (produced st) (consumed st)
                          prfP n<c prfC
                          (sym (lookup-c≡lookup-p rs n<c prfP)))
  ... | inj₂ refl = trans
                      (lookup-length (consumed st) (<-refl-l (consumed st)))
                      m≡lookup


  -- TODO : Generalize all functions about lists
  take-n-l++ : ∀ {n} (l₁ l₂ : List Message)
               → n ≤ length l₁
               → take n l₁ ≡ take n (l₁ ++ l₂)
  take-n-l++ {zero}  l₁ l₂ n≤l₁ = refl
  take-n-l++ {suc n} (x ∷ l₁) l₂ n≤l₁
    rewrite take-n-l++ l₁ l₂ (≤-pred n≤l₁) = refl



  l₁≡l₂ : ∀ {m₁ m₂ : Message} {l₁ l₂}
          → m₁ ∷ l₁ ≡ m₂ ∷ l₂
          → m₁ ≡ m₂ × l₁ ≡ l₂
  l₁≡l₂ refl = refl , refl


  m₁≡m₂⇒l≡l : ∀ {m₁ m₂ : Message} {l}
                    → m₁ ≡ m₂
                    → m₁ ∷ l ≡ m₂ ∷ l
  m₁≡m₂⇒l≡l {l = l} refl = refl



  taken×lookup : ∀ {m : Message} l₁ l₂
                 → (prf : length l₁ < length l₂)
                 → l₁ ≡ take (length l₁) l₂
                 → m ≡ lookup l₂ (fromℕ≤ prf)
                 → l₁ ++ [ m ] ≡ take (suc (length l₁)) l₂
  taken×lookup [] (x₂ ∷ l₂) l₁<l₂ l₁≡take refl = refl
  taken×lookup (x₂ ∷ l₁) (x₃ ∷ l₂) l₁<l₂ l₁≡tk m≡lkp
    rewrite taken×lookup l₁ l₂ (≤-pred l₁<l₂) (proj₂ (l₁≡l₂ l₁≡tk)) m≡lkp
      = m₁≡m₂⇒l≡l (proj₁ (l₁≡l₂ l₁≡tk))


  take1+l≡takel++m : ∀ {m : Message} {n} l
                         → n ≡ 1 + length l
                         → take n (l ++ [ m ]) ≡ l ++ [ m ]
  take1+l≡takel++m [] refl = refl
  take1+l≡takel++m {m} (x₁ ∷ l) refl
    rewrite take1+l≡takel++m {m} l refl = refl

  take-length≡l : ∀ (l : List Message) → take (length l) l ≡ l
  take-length≡l [] = refl
  take-length≡l (x ∷ l) rewrite take-length≡l l = refl


  [c]-prefix-[p] : ∀ {n}
                   → Invariant
                       MyStateMachine
                       λ st → n ≤ length (consumed st)
                            → take n (consumed st) ≡ take n (produced st)
  [c]-prefix-[p] {n} (init refl) n<lc = refl
  [c]-prefix-[p] {n} (step {st} {produce m} rs enEv) n<lc
    = trans
        ([c]-prefix-[p] rs n<lc)
        (take-n-l++ (produced st) ([ m ]) (≤-trans n<lc (inv-cons≤prod rs)))
  [c]-prefix-[p] {n} (step {st} {consume m} rs enEv) n≤c++
     with enEv
  ... | consEnabled cons<prod m≡lookup
       with n≤l++⇒n≤l⊎n≡l (consumed st) n≤c++
  ... | inj₁ n≤c   = trans
                       (sym (take-n-l++ (consumed st) [ m ] n≤c))
                       ([c]-prefix-[p] rs n≤c)
  ... | inj₂ refl =  let tc≡tp = [c]-prefix-[p] rs ≤-refl
                     in trans
                          (take1+l≡takel++m (consumed st) refl)
                          (taken×lookup
                            (consumed st) (produced st) cons<prod
                            (trans (sym (take-length≡l (consumed st))) tc≡tp)
                            m≡lookup)


  lengths≡⇒p≡c : ∀ {l₁ l₂ : List Message}
               → length l₂ ≡ length l₁
               → take (length l₁) l₁ ≡ take (length l₁) l₂
               → l₁ ≡ l₂

  {- I don't think I can prove this using the proof progressOnLength because
     I have a conjunction with produced z ≡ msgs and I don't have any l-t
     constructor for conjunctions, the only one is viaUseInv but my proof of
     progressOnLength is not an inv but a liveness property. I would need to use
     viaTrans to prove that the length of consumed progresses and which together
     [c]-prefix-[p] proves that the consumed is equal to the produced, however I
     to use the transitivity I would have lost proof that produced z ≡ msgs
  -}
  progress : ∀ {msgs}
             → (λ st → produced st ≡ msgs)
               l-t
               λ st → consumed st ≡ msgs
  progress =
    viaDisj
      (λ {st} p≡m → P⊆P1∪P2 (length (produced st)) (length (consumed st)) p≡m)
      (viaInv (λ { rs (p≡m , lc≡lp)
                   → trans (lengths≡⇒p≡c lc≡lp ([c]-prefix-[p] rs ≤-refl)) p≡m
                 } ))
      {!!}
