open import Prelude

open import StateMachineModel
open StateMachine
open System

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
      tail  : ∀ {e : Event} → (enEv : enabled StMachine e S)
              → Behavior (action StMachine enEv)
  open Behavior



  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : Behavior st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {e st} (n : ℕ)
              (σ : Behavior st) (enEv : enabled StMachine e st)
              (pts  : AnyS∈B P n (σ .tail enEv))
            → AnyS∈B P (suc n) σ


   -- A behavior σ satisfies P if there is any state ∈ σ satisfies P
  _satisfies_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P at i = AnyS∈B P i σ


  record _¬satisfies_ {ℓ} {st} (σ : Behavior st) (P : Pred State ℓ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      ¬head  : ¬ (P st)
      tl-any : Σ[ e ∈ Event ]
                 Σ[ enEv ∈ enabled StMachine e st ] ( σ .tail enEv ¬satisfies P)
  open _¬satisfies_



  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x


  disjSat : ∀ {st} {ℓ} {Q : Pred State ℓ}
            → (σ : Behavior st)
            → Decidable Q
            → Dec (Σ[ i ∈ ℕ ] σ satisfies Q at i)
  disjSat {st} {Q = Q} σ decQ
     with decQ st
  ... | yes p = yes (zero , (here p)) --(here p)
  ... | no ¬p
       with ∃Enabled? st
  ...    | no ¬enEv = no (λ { (zero , here ps)
                                    → ⊥-elim (¬p ps)
                            ; (suc n , there {e} .n σ enEv snd)
                                    → ⊥-elim (¬enEv (e , enEv)) })
  ...    | yes (ev , enEv)
         with disjSat (tail σ enEv) decQ
  ...      | yes (n , tS) = yes (suc n , there n σ enEv tS)
  ...      | no ¬p₁ = no (λ { (zero , here ps) → ⊥-elim (¬p ps)
                            ; (suc fst , there .fst σ enEv snd) → ⊥-elim (¬p₁ ({!!} , {!!})) }) --yes (there ? σ enEv p)




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




  soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → Reachable {sm = StMachine} st
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness2 {st} {P = P} rS σ (here ps) rule@(viaEvSet evSet x c₁ c₂ c₃)
    with ∃Enabled? st
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
            with soundness2 (step rS enEv) (σ .tail enEv) (here pActionSt) rule
  ... | n , 1≤n , tail⊢q = (suc n) , (≤-step 1≤n) , (there n σ enEv tail⊢q)
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
  soundness2 rS σ (there n .σ enEv x₁) x₂
    with soundness2 (step rS enEv) (σ .tail enEv) x₁ x₂
  ... | j , j<i , tail⊢Q = suc j , s≤s j<i , (there j σ enEv tail⊢Q)

