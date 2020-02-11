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


  record Behavior (S : State) :
    Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tail  : Σ[ e ∈ Event ] Σ[ enEv ∈ enabled StMachine e S ]
                 Behavior (action StMachine enEv)
              ⊎
              ¬ ( Σ[ e ∈ Event ] enabled StMachine e S )
  open Behavior


  data BehaviorPrefix (st : State) : Set (ℓ₁ ⊔ ℓ₂) where
      last : BehaviorPrefix st
      noEv : ¬ (Σ[ e ∈ Event ] enabled StMachine e st)
                → BehaviorPrefix st
      _∷_  : ∀ {e} → (enEv : enabled StMachine e st)
                → BehaviorPrefix (action StMachine enEv)
                → BehaviorPrefix st
  open BehaviorPrefix


  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x

  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : Behavior st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {st} (n : ℕ) (σ : Behavior st)
            → case tail σ of
              (λ { (inj₁ (e , enEv , t)) → AnyS∈B P n t
                 ; (inj₂ y) → AnyS∈B P 0 σ })
            → AnyS∈B P (suc n) σ



   -- A behavior σ satisfies P if there is any state ∈ σ satisfies P
  _satisfies_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P at i = AnyS∈B P i σ


  data AnyPreffix {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (BehaviorPrefix st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : BehaviorPrefix st} (ps  : P st)
            → AnyPreffix P zero σ
    there : ∀ {st e} (n : ℕ)
              (enEv : enabled StMachine e st)
              {t : BehaviorPrefix (action StMachine enEv)}
              (pts  : AnyPreffix P n t)
            → AnyPreffix P (suc n) (enEv ∷ t)




  -- Take 0 will return st because we are considering indexes starting at 0
  take : ∀ {st} → ℕ → (σ : Behavior st) → BehaviorPrefix st
  take zero σ = last
  take (suc n) σ
    with tail σ
  ... | inj₂ ¬enEv = noEv ¬enEv
  ... | inj₁ (e , enEv , t) = enEv ∷ take n t


  drop : ∀ {st} → ℕ → (σ : Behavior st) → Σ[ s ∈ State ] Behavior s
  drop {st} zero σ = st , σ
  drop {st} (suc n) σ
     with tail σ
  ... | inj₁ (e , enEv , t) = drop n t
  ... | inj₂ ¬enEv = st , σ


  lastSt : ∀ {st} → BehaviorPrefix st → State
  lastSt {st} last = st
  lastSt {st} (noEv x) = st
  lastSt {st} (enEv ∷ t) = lastSt t


  data AllS {ℓ} (P : Pred State ℓ)
    :  ∀ {st : State} → Pred (BehaviorPrefix st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    last : ∀ {st} (ps  : P st)
           → AllS P (last {st})
    noEv : ∀ {st} (ps  : P st)
           → (¬enEv : ¬ ( Σ[ e ∈ Event ] enabled StMachine e st ))
           → AllS P (noEv ¬enEv)
    _∷_  : ∀ {st e} {enEv : enabled StMachine e st}
             {t : BehaviorPrefix (action StMachine enEv)}
             (ps  : P st)
             (pts  : AllS P t)
            → AllS P (enEv ∷ t)


  data All {ℓ} {st : State} (P : Pred State ℓ)
    : ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    last  : ∀ {σ : Behavior st}
            → (ps  : P st)
            → All P zero σ
    _∷_   : ∀ {e n} {σ : Behavior st} {enEv : enabled StMachine e st}
              {t : Behavior (action StMachine enEv)}
            → (ps  : P st)
            → (pts  : All P n t)
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



  witness : ∀ {st : State} {ℓ i} {σ : Behavior st} {P : Pred State ℓ}
            → Reachable {sm = StMachine} st
            → σ satisfies P at i
            → Σ[ state ∈ State ]
                 Σ[ rSt ∈ Reachable {sm = StMachine} state ] P state
  witness {st} rS (here ps) = st , rS , ps
  witness {st} rS (there n σ satP)
    with tail σ
  ... | inj₁ (e , enEv , t) = witness (step rS enEv) satP
  ... | inj₂ ¬enEv = witness rS satP



  trans2 :  ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ}
              → (σ : Behavior st)
              → σ satisfies (Q ∪ R) at i
              →   σ satisfies Q at i
                ⊎ σ satisfies R at i
  trans2 σ (here (inj₁ qS)) = inj₁ (here qS)
  trans2 σ (here (inj₂ rS)) = inj₂ (here rS)
  trans2 σ (there n σ tailQ∨R)
    with tail σ
  ... | inj₂ ¬enEv = case tailQ∨R of
                     λ { (here (inj₁ x)) → inj₁ (there n σ {!!} )
                       ; (here (inj₂ y)) → inj₁ (there n σ {!!}) }
  ... | inj₁ (e , enEv , t)
      with trans2 t tailQ∨R
  ... | inj₁ satQ = inj₁ (there n σ {!!})
  ... | inj₂ satR = inj₁ (there n σ {!!})




  useInv : ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → Invariant StMachine R
              → Reachable {sm = StMachine} st
              → σ satisfies (R ⇒ Q) at i
              → σ satisfies Q at i
  useInv inv rS (here ps)
    = here (ps (inv rS))
  useInv inv rS (there n σ x)
    with tail σ
  ... | inj₁ (e , enEv , t) = there n σ {!!}
  ... | inj₂ y = {!!}
{-

  stable : ∀ {st} {ℓ₃ ℓ₄} {P' : Pred State ℓ₃} {S : Pred State ℓ₄}
             {i : ℕ} {σ : Behavior st}
            → Stable StMachine S
            → Reachable {sm = StMachine} st
            → σ satisfies (P' ∩ S) at i
            → σ satisfies P' at i × σ satisfies S at i
  stable stableS rS (here (p' , s))
    = here p' , here s
  stable stableS rS (there n σ enEv satP'∧S)
    with stable stableS (step rS enEv) satP'∧S
  ... | tailP' , tailS = (there n σ enEv tailP')
                       , (there n σ enEv tailS)



  last≢take>0 : ∀ {st} → (σ : Behavior st) → (n : ℕ) → 0 < n → last ≢ take n σ
  last≢take>0 σ (suc n) x
    with tail σ
  ... | inj₁ e∷t = λ { () }
  ... | inj₂ ¬ev = λ { () }


  postulate
    weak-fairness : ∀ {st}
                    → (evSet : EventSet)
                    → (σ : Behavior st)
                    →  Σ[ n ∈ ℕ ]
                     ( AllS (enabledSet StMachine evSet) (take n σ)
                       → case tail (proj₂ (drop n σ)) of
                         λ { (inj₁ (e , enEv , t)) → evSet e
                           ; (inj₂ ¬enEv) → ⊥ } )



  soundness-WF : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                 → Reachable {sm = StMachine} st
                 → (evSet : EventSet)
                 → (σ : Behavior st)
                 → (n : ℕ)
                 → P st
                 → (∀ (e : Event) → evSet e → [ P ] e [ Q ])
                 → (∀ (e : Event) → ¬ (evSet e) → [ P ] e [ P ∪ Q ])
                 → Invariant (stateMachine sys) (P ⇒ enabledSet StMachine evSet)
                 → Σ[ j ∈ ℕ ] 0 ≤ j × σ satisfies Q at j
                 ⊎ AllS (enabledSet StMachine evSet ∩ P) (take n σ)
  soundness-WF {P = P} rS evSet σ zero ps c₁ c₂ c₃
    with tail σ
  ... | inj₁ tailσ = inj₂ (last ( c₃ rS ps , ps))
  ... | inj₂ ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ rS ps)))
  soundness-WF {P = P} rS evSet σ (suc n) ps c₁ c₂ c₃
    with tail σ
  ... | inj₂ ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ rS ps)))
  ... | inj₁ (ev , enEv , t)
      with ev ∈Set? evSet
  ...   | yes ∈evSet
          = let ht = c₁ ev ∈evSet
                qS = [P]e[Q]∧P⇒Q enEv ps ht
            in inj₁ (1 , z≤n , there 0 σ enEv {t = t} (here qS))
  ...   | no ¬∈evSet
        with c₂ ev ¬∈evSet
  ...     | hoare p∨q
          with p∨q ps enEv
  ...       | inj₂ qActionSt
              = inj₁ (1 , z≤n , (there 0 σ enEv {t = t} (here qActionSt)))
  ...       | inj₁ pActionSt
            with soundness-WF (step rS enEv) evSet t
                               n pActionSt c₁ c₂ c₃
  ...         | inj₁ (j , 0<j , anyQT)
                = inj₁ (suc j , z≤n , there j σ enEv anyQT)
  ...         | inj₂ allT = inj₂ (( c₃ rS ps , ps) ∷ allT)





  ∀P∩Q⇒∀P∩∀Q : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                → (n : ℕ)
                → (σ : Behavior st)
                → AllS (P ∩ Q) (take n σ)
                → AllS P (take n σ) × AllS Q (take n σ)
  ∀P∩Q⇒∀P∩∀Q zero σ (last (p , q)) = (last p) , (last q)
  ∀P∩Q⇒∀P∩∀Q (suc n) σ allPQ
    with tail σ
  ... | inj₂ ¬ev = case allPQ of
                   λ { (noEv (p , q) ¬ev) → (noEv p ¬ev) , noEv q ¬ev }
  ... | inj₁ (e , enEv , t)
      with allPQ
  ...   | (p , q) ∷ allPQt
        with ∀P∩Q⇒∀P∩∀Q n t allPQt
  ...     | allP , allQ = (p ∷ allP) , (q ∷ allQ)



  ∀Pn⇒PdropN : ∀ {st} {ℓ₃} {P : Pred State ℓ₃} (n : ℕ)
                → (σ : Behavior st)
                → AllS P (take n σ)
                → P (proj₁ (drop n σ))
  ∀Pn⇒PdropN zero σ (last ps) = ps
  ∀Pn⇒PdropN (suc n) σ allP
    with tail σ
  ... | inj₂ ¬ev = case allP of λ { (noEv ps ¬ev) → ps }
  ... | inj₁ (e , enEv , t)
      with allP
  ... | ps ∷ allPt = ∀Pn⇒PdropN n t allPt



  dropNσsat⇒σsat : ∀ {st} {ℓ₄} {Q : Pred State ℓ₄}
                   → (n : ℕ)
                   → (σ : Behavior st)
                   → proj₂ (drop n σ) satisfies Q at 1
                   → σ satisfies Q at (suc n)
  dropNσsat⇒σsat zero    σ satQ = satQ
  dropNσsat⇒σsat (suc n) σ satQ
    with tail σ
  ... | inj₂ ¬ev = case satQ of
                   λ { (there {e = e} 0 σ enEv x) → ⊥-elim (¬ev (e , enEv)) }
  ... | inj₁ (e , enEv , t)
      with dropNσsat⇒σsat n t satQ
  ...   | anyQ = there (suc n) σ enEv anyQ



  soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → Reachable {sm = StMachine} st
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness2 {st} {P = P} rS σ (here ps) rule@(viaEvSet evSet wf c₁ c₂ c₃)
    with weak-fairness evSet σ
  ... | n , wfa
      with soundness-WF rS evSet σ n ps c₁ c₂ c₃
  ...   | inj₁ satQ   = satQ
  ...   | inj₂ allE∧P
        with ∀P∩Q⇒∀P∩∀Q n σ allE∧P
  ...     | allE , allP
          with wfa allE
  ...       | v
            with tail (proj₂ (drop n σ))
  ...         | inj₂ ¬enEv = ⊥-elim v
  ...         | inj₁ (e₁ , enEv₁ , t)
                = let htp = c₁ e₁ v
                      pSt = ∀Pn⇒PdropN n σ allP
                      qSt = [P]e[Q]∧P⇒Q enEv₁ pSt htp
                      q⊢1 = there 0 (proj₂ (drop n σ)) enEv₁ {t = t} (here qSt)
                   in suc n , z≤n , dropNσsat⇒σsat n σ q⊢1

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

  soundness2 rS σ (there {e} n σ enEv {t} x₁) x₂
      with soundness2 (step rS enEv) t x₁ x₂
  ... | j , j<i , tail⊢Q = suc j , s≤s j<i , (there j σ enEv tail⊢Q)

-}
