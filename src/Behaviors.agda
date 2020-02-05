open import Prelude

open import StateMachineModel
open StateMachine
open System
open import Relation.Nullary.Negation using (contradiction)

module Behaviors {ℓ₁ ℓ₂}
       (State : Set ℓ₁)
       (Event : Set ℓ₂)
       (sys : System State Event)
       (∃Enabled?_ : (st : State) → Dec (Σ[ e ∈ Event ] enabled (stateMachine sys) e st))
       (_∈Set?_ : (ev : Event) (evSet : EventSet) → Dec (evSet ev))
  where

  open LeadsTo State Event sys

  StMachine = stateMachine sys


  record Behavior (S : State) : Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      event : Event
      enEv  : enabled (stateMachine sys) event S
      tail  : Behavior (action (stateMachine sys) enEv)
  open Behavior



  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : Behavior st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {st} {n : ℕ}
              (σ : Behavior st)
              (pts  : AnyS∈B P n (tail σ))
            → AnyS∈B P (suc n) σ


   -- A behavior σ satisfies P if there is any state ∈ σ satisfies P
  _satisfies_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P at i = AnyS∈B P i σ

  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x


  drop : ∀ {st} → ℕ → (σ : Behavior st) → Σ[ s ∈ State ] Behavior s
  drop {st} zero σ = st , σ
  drop {st} (suc n) σ = drop n (tail σ)

  data All {ℓ} {st : State} (P : Pred State ℓ)
    : ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    last  : ∀ {σ : Behavior st}
            → (ps  : P st)
            → All P zero σ
    _∷_   : ∀ {n} {σ : Behavior st}
            → (ps  : P st)
            → (pts  : All P n (tail σ))
            → All P (suc n) σ


 ------------------------------------------------------------------------------
 -- PROOF
 ------------------------------------------------------------------------------
  [P]e[Q]∧P⇒Q : ∀ {ℓ₃ ℓ₄ st e}  {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                → (enEv : enabled StMachine e st)
                → P st
                → [ P ] e [ Q ]
                → Q (action StMachine enEv)
  [P]e[Q]∧P⇒Q {st = st} enEv pSt (hoare x) = x pSt enEv


  c₃→∃enEv : ∀ {st} {ℓ₃} {P : Pred State ℓ₃} {evSet : EventSet}
               → Σ Event (λ event →
                    Σ (evSet event) (λ x → enabled StMachine event st))
               → Σ Event (λ e → enabled StMachine e st)

  c₃→∃enEv (ev , _ , enEv) = ev , enEv


{-
  witness : ∀ {st : State} {ℓ i} {σ : Behavior st} {P : Pred State ℓ}
            → Reachable {sm = StMachine} st
            → σ satisfies P at i
            → Σ[ state ∈ State ]
                 Σ[ rSt ∈ Reachable {sm = StMachine} state ] P state
  witness {st} rS (here ps) = st , rS , ps
  witness {st} rS (there σ anyT) = witness (step rS (enEv σ)) anyT
-}

  trans2 :  ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → σ satisfies (Q ∪ R) at i
              →   Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
                ⊎ Σ[ j ∈ ℕ ] i ≤ j × σ satisfies R at j
  trans2 (here (inj₁ qS)) = inj₁ (zero , ≤-refl , here qS)
  trans2 (here (inj₂ rS)) = inj₂ (zero , z≤n , here rS)
  trans2 (there σ tailQ∨R)
    with trans2 tailQ∨R
  ... | inj₁ (j , i≤j , tailQ) = inj₁ (suc j , s≤s i≤j , there σ tailQ)
  ... | inj₂ (j , i≤j , tailR) = inj₂ (suc j , s≤s i≤j , there σ tailR)



  useInv : ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → Invariant StMachine R
              → Reachable {sm = StMachine} st
              → σ satisfies (R ⇒ Q) at i
              → σ satisfies Q at i
  useInv inv rS (here ps)
    = here (ps (inv rS))
  useInv inv rS (there σ x)
    = there σ (useInv inv (step rS (enEv σ)) x)


  stable : ∀ {st} {ℓ₃ ℓ₄} {P' : Pred State ℓ₃} {S : Pred State ℓ₄}
             {i : ℕ} {σ : Behavior st}
            → Stable StMachine S
            → Reachable {sm = StMachine} st
            → σ satisfies (P' ∩ S) at i
            → σ satisfies P' at i × σ satisfies S at i
  stable stableS rS (here (p' , s))
    = here p' , here s
  stable stableS rS (there σ satP'∧S)
    with stable stableS (step rS (enEv σ)) satP'∧S
  ... | tailP' , tailS = (there σ tailP')
                       , (there σ tailS)




  postulate
    weak-fairness : ∀ {st}
                    → (evSet : EventSet)
                    → (σ : Behavior st)
                    →  Σ[ n ∈ ℕ ]
                     ( All (enabledSet StMachine evSet) n σ
                       → evSet (event (proj₂ (drop n σ))))



  soundness-WF : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                 → (n : ℕ)
                 → Reachable {sm = StMachine} st
                 → (evSet : EventSet)
                 → (σ : Behavior st)
                 → P st
                 → (∀ (e : Event) → evSet e → [ P ] e [ Q ])
                 → (∀ (e : Event) → ¬ (evSet e) → [ P ] e [ P ∪ Q ])
                 → Invariant (stateMachine sys) (P ⇒ enabledSet StMachine evSet)
                 → Σ[ j ∈ ℕ ] 0 ≤ j × σ satisfies Q at j
                 ⊎ All (enabledSet StMachine evSet ∩ P) n σ
  soundness-WF {P = P} zero    rS evSet σ ps c₁ c₂ c₃
    = inj₂ (last ((c₃ rS ps) , ps))
  soundness-WF {P = P} (suc n) rS evSet σ ps c₁ c₂ c₃
    with event σ ∈Set? evSet
  ...   | yes ∈evSet
          = let ht = c₁ (event σ) ∈evSet
                qS = [P]e[Q]∧P⇒Q (enEv σ) ps ht
            in inj₁ (1 , z≤n , there σ (here qS))
  ...   | no ¬∈evSet
        with c₂ (event σ) ¬∈evSet
  ...     | hoare p∨q
          with p∨q ps (enEv σ)
  ...       | inj₂ qNSt
              = inj₁ (1 , z≤n , there σ (here qNSt))
  ...       | inj₁ pNSt
            with soundness-WF n (step rS (enEv σ)) evSet (tail σ) pNSt c₁ c₂ c₃
  ...         | inj₁ (j , 0<j , anyQT)
                = inj₁ (suc j , z≤n , there σ anyQT)
  ...         | inj₂ allT
                = inj₂ (( c₃ rS ps , ps) ∷ allT)



  ∀P∩Q⇒∀P∩∀Q : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                → (n : ℕ)
                → (σ : Behavior st)
                → All (P ∩ Q) n σ
                → All P n σ × All Q n σ
  ∀P∩Q⇒∀P∩∀Q zero σ (last (p , q)) = (last p) , (last q)
  ∀P∩Q⇒∀P∩∀Q (suc n) σ ((p , q) ∷ allPQ)
     with ∀P∩Q⇒∀P∩∀Q n (tail σ) allPQ
  ...     | allP , allQ = (p ∷ allP) , (q ∷ allQ)


  ∀Pn⇒PdropN : ∀ {st} {ℓ₃} {P : Pred State ℓ₃} (n : ℕ)
                → (σ : Behavior st)
                → All P n σ
                → P (proj₁ (drop n σ))
  ∀Pn⇒PdropN zero    σ (last ps)   = ps
  ∀Pn⇒PdropN (suc n) σ (ps ∷ allP) = ∀Pn⇒PdropN n (tail σ) allP



  dropNσsat⇒σsat : ∀ {st} {ℓ₄} {Q : Pred State ℓ₄}
                   → (n : ℕ)
                   → (σ : Behavior st)
                   → proj₂ (drop n σ) satisfies Q at 1
                   → σ satisfies Q at (suc n)
  dropNσsat⇒σsat zero    σ satQ = satQ
  dropNσsat⇒σsat (suc n) σ satQ = there σ (dropNσsat⇒σsat n (tail σ) satQ)



  soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → Reachable {sm = StMachine} st
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness2 {st} {P = P} rS σ (here ps) rule@(viaEvSet evSet wf c₁ c₂ c₃)
    with weak-fairness evSet σ
  ... | n , wfa
      with soundness-WF n rS evSet σ ps c₁ c₂ c₃
  ...   | inj₁ satQ   = satQ
  ...   | inj₂ allE∧P
        with ∀P∩Q⇒∀P∩∀Q n σ allE∧P
  ...     | allE , allP
          with wfa allE
  ...       | dropNσ∈Evset = let dropN-σ = proj₂ (drop n σ)
                                 enE = enEv dropN-σ
                                 htD = c₁ (event dropN-σ) dropNσ∈Evset
                                 pDσ = ∀Pn⇒PdropN n σ allP
                                 qDσ = [P]e[Q]∧P⇒Q enE pDσ htD
                                 ⊢dσ = there dropN-σ (here qDσ)
                             in suc n , z≤n , dropNσsat⇒σsat n σ ⊢dσ

  soundness2 rS σ (here ps) rule@(viaInv inv) = zero , z≤n , here (inv rS ps)

  soundness2 rS σ (here ps) rule@(viaTrans x₂ x₃)
    with soundness2 rS σ (here ps) x₂
  ... | n , 0<n , anyR
      with soundness2 rS σ anyR x₃
  ... | j , n<j , anyQ = j , ≤-trans 0<n n<j , anyQ

  soundness2 rS σ (here ps) rule@(viaTrans2 x₂ x₃)
    with soundness2 rS σ (here ps) x₂
  ... | n , 0<n , anyQ∨R
      with trans2 anyQ∨R
  ...   | inj₁ (j , n≤j , anyQ) = j , ≤-trans 0<n n≤j , anyQ
  ...   | inj₂ (n₁ , n<n₁ , anyR)
        with soundness2 rS σ anyR x₃
  ...     | j , n₁≤j , anyQ  = j , ≤-trans 0<n (≤-trans n<n₁ n₁≤j) , anyQ

  soundness2 rS σ (here ps) rule@(viaDisj x x₂ x₃)
    with x ps
  ... | inj₁ p₁S = soundness2 rS σ (here p₁S) x₂
  ... | inj₂ p₂S = soundness2 rS σ (here p₂S) x₃

  soundness2 rS σ (here ps) rule@(viaUseInv inv x₂)
    with soundness2 rS σ (here (ps , inv rS)) x₂
  ... | n , 0≤n , anyR⇒Q
      with useInv inv rS anyR⇒Q
  ... | anyQ = n , 0≤n , anyQ

  soundness2 rS σ (here ps) rule@(viaWFR F x₂ x) = {!!}

  soundness2 rS σ (here ps) rule@(viaStable x₂ p'→q stableS q'∧s→q)
    with soundness2 rS σ (here ps) x₂
  ... | n , 0<n , anyP'∧S
      with stable stableS rS anyP'∧S
  ... | anyP' , anyS
        with soundness2 rS σ anyP' p'→q
  ...   | k , n<k , anyQ'
        with soundness2 rS σ {!!} q'∧s→q
  ...     | j , k<j , anyQ = j , ≤-trans 0<n (≤-trans n<k k<j) , anyQ

  soundness2 rS σ (there σ t) p→q
      with soundness2 (step rS (enEv σ)) (tail σ) t p→q
  ... | j , j<i , tail⊢Q = suc j , s≤s j<i , (there σ tail⊢Q)

