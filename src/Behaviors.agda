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


  data BehaviorSuffix (st : State) : Set (ℓ₁ ⊔ ℓ₂) where
      last : BehaviorSuffix st
      noEv : ¬ (Σ[ e ∈ Event ] enabled StMachine e st)
                → BehaviorSuffix st
      _∷_  : ∀ {e} → (enEv : enabled StMachine e st)
                → BehaviorSuffix (action StMachine enEv)
                → BehaviorSuffix st
  open BehaviorSuffix




  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : Behavior st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {e st} (n : ℕ)
              (σ : Behavior st) (enEv : enabled StMachine e st)
              {tail : Behavior (action StMachine enEv)}
              (pts  : AnyS∈B P n tail)
            → AnyS∈B P (suc n) σ


   -- A behavior σ satisfies P if there is any state ∈ σ satisfies P
  _satisfies_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P at i = AnyS∈B P i σ


  data AnyPreffix {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (BehaviorSuffix st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : BehaviorSuffix st} (ps  : P st)
            → AnyPreffix P zero σ
    there : ∀ {st e} (n : ℕ)
              (enEv : enabled StMachine e st)
              {t : BehaviorSuffix (action StMachine enEv)}
              (pts  : AnyPreffix P n t)
            → AnyPreffix P (suc n) (enEv ∷ t)


  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x



  -- Take 0 will return st because we are considering indexes starting at 0
  take : ∀ {st} → ℕ → (σ : Behavior st) → BehaviorSuffix st
  take zero σ = last
  take (suc n) σ
    with tail σ
  ... | inj₂ ¬enEv = noEv ¬enEv
  ... | inj₁ (e , enEv , t) = enEv ∷ take n t


  drop : ∀ {st} → ℕ → (σ : Behavior st) → Σ[ s ∈ State ] Behavior s
  drop {st} zero σ
       with tail σ
  ... | inj₁ (e , enEv , t) = (action StMachine enEv) , t
  ... | inj₂ ¬enEv = st , σ
  drop {st} (suc n) σ
     with tail σ
  ... | inj₁ (e , enEv , t) = drop n t
  ... | inj₂ ¬enEv = st , σ


  lastSt : ∀ {st} → BehaviorSuffix st → State
  lastSt {st} last = st
  lastSt {st} (noEv x) = st
  lastSt {st} (enEv ∷ t) = lastSt t


  data All {ℓ} (P : Pred State ℓ)
    :  ∀ {st : State} → Pred (BehaviorSuffix st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    last : ∀ {st} (ps  : P st)
           → All P (last {st})
    noEv : ∀ {st} (ps  : P st)
           → (¬enEv : ¬ ( Σ[ e ∈ Event ] enabled StMachine e st ))
           → All P (noEv ¬enEv)
    _∷_  : ∀ {st e} {enEv : enabled StMachine e st}
             {t : BehaviorSuffix (action StMachine enEv)}
             (ps  : P st)
             (pts  : All P t)
            → All P (enEv ∷ t)



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
  witness {st} rS (there n σ enEv x₁) = witness (step rS enEv) x₁


  trans2 :  ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → σ satisfies (Q ∪ R) at i
              →   Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
                ⊎ Σ[ j ∈ ℕ ] i ≤ j × σ satisfies R at j
  trans2 (here (inj₁ qS)) = inj₁ (zero , ≤-refl , here qS)
  trans2 (here (inj₂ rS)) = inj₂ (zero , z≤n , here rS)
  trans2 (there n σ enEv tailQ∨R)
    with trans2 tailQ∨R
  ... | inj₁ (j , i≤j , tailQ) = inj₁ (suc j , s≤s i≤j , there j σ enEv tailQ)
  ... | inj₂ (j , i≤j , tailR) = inj₂ (suc j , s≤s i≤j , there j σ enEv tailR)



  useInv : ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → Invariant StMachine R
              → Reachable {sm = StMachine} st
              → σ satisfies (R ⇒ Q) at i
              → σ satisfies Q at i
  useInv inv rS (here ps)
    = here (ps (inv rS))
  useInv inv rS (there n σ enEv x)
    = there n σ enEv (useInv inv (step rS enEv) x)


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


  action≡⇒t≡ : ∀ {st e₁ e₂}
               → (enEv₁ : enabled StMachine e₁ st)
               → (enEv₂ : enabled StMachine e₂ st)
               → action (stateMachine sys) enEv₁ ≡ action (stateMachine sys) enEv₂
               → Behavior (action (stateMachine sys) enEv₁)
               → Behavior (action (stateMachine sys) enEv₂)






  postulate
    weak-fairness : ∀ {st}
                    → (evSet : EventSet)
                    → (σ : Behavior st)
                    →  Σ[ n ∈ ℕ ]
                     ( All (enabledSet StMachine evSet) (take n σ)
                       → Σ[ e ∈ Event ]
                            Σ[ enEv ∈ enabled StMachine e (lastSt (take n σ)) ]
                             evSet e × proj₁ (drop n σ) ≡ action StMachine enEv)

  soundness-WF : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                 → Reachable {sm = StMachine} st
                 → (evSet : EventSet)
                 → (σ : Behavior st)
                 → (σPrefix : BehaviorSuffix st)
                   {n : ℕ} → σPrefix ≡ take n σ
                 → P st
                 → ( All (enabledSet StMachine evSet) σPrefix
                     →  Σ[ e ∈ Event ]
                            Σ[ enEv ∈ enabled StMachine e (lastSt (take n σ)) ]
                             evSet e × proj₁ (drop n σ) ≡ action StMachine enEv)
                 → (weakFairness sys evSet)
                 → (∀ (e : Event) → evSet e → [ P ] e [ Q ])
                 → (∀ (e : Event) → ¬ (evSet e) → [ P ] e [ P ∪ Q ])
                 → Invariant (stateMachine sys) (P ⇒ enabledSet StMachine evSet)
                 → Σ[ j ∈ ℕ ] 0 ≤ j × σ satisfies Q at j
  soundness-WF {P = P} rS evSet σ last {zero} σ≡p ps wfa wf c₁ c₂ c₃
     with tail σ
  ... | inj₂ ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ rS ps)))
  ... | inj₁ (e , enEv , t)
      with wfa (last (c₃ rS ps))
  ... | e₁ , enEv₁ , e₁∈set , enEv≡
        = let tail = action≡⇒t≡ enEv enEv₁ enEv≡ t
              qS   = [P]e[Q]∧P⇒Q enEv₁ ps (c₁ e₁ e₁∈set)
           in 1 , z≤n , (there 0 σ enEv₁ {tail = {!!}} (here qS))
  soundness-WF rS evSet σ last {suc n} σ≡p ps wfa wf c₁ c₂ c₃
    = ⊥-elim (last≢take>0 σ (suc n) (s≤s z≤n) σ≡p)
  soundness-WF rS evSet σ (noEv x) {suc n} σ≡p ps wfa wf c₁ c₂ c₃ = {!!}
  soundness-WF rS evSet σ (enEv ∷ σP) {suc n} σ≡p ps wfa wf c₁ c₂ c₃ = {!!}




  soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → Reachable {sm = StMachine} st
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness2 {st} {P = P} rS σ (here ps) rule@(viaEvSet evSet wf c₁ c₂ c₃)
    with weak-fairness evSet σ
  ... | n , wfa = soundness-WF rS evSet σ (take n σ) {n} refl ps wfa wf c₁ c₂ c₃
  {-  with ∃Enabled? st
  ... | no ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ rS ps)))
  ... | yes (ev , enEv)
      with ev ∈Set? evSet
  ...   | yes ∈evSet
          = let ht = c₁ ev ∈evSet
                qS = [P]e[Q]∧P⇒Q enEv ps ht
            in 1 , z≤n , there zero σ enEv (here qS)
  ...   | no ¬∈evSet
        with c₂ ev ¬∈evSet
  ...     | hoare p∨q
          with p∨q ps enEv
  ...       | inj₂ qActionSt = 1 , z≤n , (there zero σ enEv (here qActionSt))
  ...       | inj₁ pActionSt
            with soundness2 (step rS enEv) {!!} (here pActionSt) rule
  ... | n , 1≤n , tail⊢q = (suc n) , (≤-step 1≤n) , (there n σ enEv tail⊢q)
-}
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

