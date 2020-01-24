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


{-
  record _satisfies_ {st : State} {ℓ} (σ : Behavior st) (P : Pred State ℓ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    constructor satisfy
    field
      tl-any : P st
               ⊎
               Σ[ e ∈ Event ] Σ[ enEv ∈ enabled StMachine e st ] ( σ .tail enEv satisfies P)
  open _satisfies_
-}

  record _¬satisfies_ {st : State} {ℓ} (σ : Behavior st) (P : Pred State ℓ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    constructor satisfy
    field
      ¬head  : ¬ (P st)
      tl-any : ∀ {e st}
                 (σ : Behavior st) (enEv : enabled StMachine e st)
                 → σ .tail enEv ¬satisfies P
  open _¬satisfies_

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
  transSat : ∀ {ℓ₃ ℓ₄} {st}
             → {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
             → Reachable st
             → (σ : Behavior st)
             → σ satisfies P
             → P l-t Q
             → σ satisfies Q
  transSat rSt σ σ⊢P PltQ
    with tl-any σ⊢P
  ... | inj₁ x = ?
  ... | inj₂ (ev , enEv , t⊢P) = satisfy (inj₂ (ev , enEv , transSat
                                                              (step rSt enEv)
                                                              (σ .tail enEv)
                                                              t⊢P
                                                              PltQ))


  σ⊢R⇒∃stR : ∀ {st ℓ₃} {σ : Behavior st} {R : Pred State ℓ₃}
              → σ satisfies R
              → Σ[ state ∈ State ] R state
  σ⊢R⇒∃stR {st} σ⊢R
    with tl-any σ⊢R
  ... | inj₁ s∈R = st , s∈R
  ... | inj₂ (ev , enEv , t⊢R) = σ⊢R⇒∃stR t⊢R
-}

{-
  soundness : ∀ {ℓ₃ ℓ₄} {st} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
              → (rSt : Reachable {sm = StMachine} st)
              → (σ : Behavior st)
              → P st
              → P l-t Q
              → σ satisfies Q
  tl-any (soundness {st = st} {P} {Q} stR σ st∈P (viaEvSet evSet wf c₁ c₂ c₃))
    with ∃Enabled? st
  ... | no ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ stR st∈P)))
  ... | yes (ev , enEv)
      with ev ∈Set? evSet
  ...   | yes evSetEv = inj₂ (ev , enEv , satisfy (inj₁ ([P]e[Q]∧P⇒Q enEv st∈P (c₁ ev evSetEv))) )
  ...   | no ¬evSetEv
        with c₂ ev ¬evSetEv
  ...     | hoare p∨q
          with p∨q st∈P enEv
  ...       | inj₂ qActionSt = inj₂ (ev , enEv , satisfy (inj₁ qActionSt) )
  ...       | inj₁ pActionSt = inj₂ (ev , enEv , soundness
                                                   (step stR enEv)
                                                   (σ .tail enEv)
                                                   pActionSt
                                                   (viaEvSet evSet wf c₁ c₂ c₃))

  tl-any (soundness stR σ st∈P (viaInv p⇒q)) = inj₁ (p⇒q stR st∈P)
  soundness stR σ st∈P (viaTrans PltR RltQ)
    with soundness stR σ st∈P PltR
  ... | σSatR
      with tl-any σSatR
  ...   | inj₁ st∈R = soundness stR σ st∈R RltQ
  ...   | inj₂ (ev , enEv , tSatR) = {!!}
  soundness stR σ st∈P (viaTrans2 pltq pltq₁) = {!!}
  soundness stR σ st∈P (viaDisj x pltq pltq₁) = {!!}
  soundness stR σ st∈P (viaUseInv x pltq) = {!!}
  soundness stR σ st∈P (viaWFR F pltq x) = {!!}
  soundness stR σ st∈P (viaStable pltq pltq₁ x pltq₂) = {!!}
-}

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
  _satisfiesNew_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfiesNew P at i = AnyS∈B P i σ


  witness : ∀ {st : State} {ℓ i} {σ : Behavior st} {P : Pred State ℓ}
            → Reachable {sm = StMachine} st
            → σ satisfiesNew P at i
            → Σ[ state ∈ State ]
                 Σ[ rSt ∈ Reachable {sm = StMachine} state ] P state
  witness {st} rS (here ps) = st , rS , ps
  witness {st} rS (there n σ enEv x₁) = witness (step rS enEv) x₁


  trans2 :  ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → σ satisfiesNew (Q ∪ R) at i
              →   Σ[ j ∈ ℕ ] i ≤ j × σ satisfiesNew Q at j
                ⊎ Σ[ j ∈ ℕ ] i ≤ j × σ satisfiesNew R at j
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
              → σ satisfiesNew (R ⇒ Q) at i
              → σ satisfiesNew Q at i
  useInv inv rS (here ps)
    = here (ps (inv rS))
  useInv inv rS (there n σ enEv x)
    = there n σ enEv (useInv inv (step rS enEv) x)


  stable : ∀ {st} {ℓ₃ ℓ₄} {P' : Pred State ℓ₃} {S : Pred State ℓ₄}
             {i : ℕ} {σ : Behavior st}
            → Stable StMachine S
            → Reachable {sm = StMachine} st
            → σ satisfiesNew (P' ∩ S) at i
            → σ satisfiesNew P' at i × σ satisfiesNew S at i
  stable stableS rS (here (p' , s))
    = here p' , {!!}
  stable stableS rS (there n σ enEv satP'∧S)
    = {!!} --there n σ enEv (stable stableS (step rS enEv) satP'∧S)




  satQ'∧S⇒satQ' : ∀ {st} {ℓ₃ ℓ₄} {Q' : Pred State ℓ₃} {S : Pred State ℓ₄}
                    {i j : ℕ} {σ : Behavior st}
                  → Stable StMachine S
                  → σ satisfiesNew S at i
                  → i ≤ j
                  → σ satisfiesNew Q' at j
                  → σ satisfiesNew (Q' ∩ S) at j
  satQ'∧S⇒satQ' stableS (here sS) i≤j (here q'S) = here (q'S , sS)
  satQ'∧S⇒satQ' stableS (here sS) i≤j (there n σ enEv satQ')
    = let tail = satQ'∧S⇒satQ' stableS (here (stableS enEv sS)) z≤n satQ'
      in there n σ enEv tail
  satQ'∧S⇒satQ' stableS (there n σ enEv satS) i≤j (there n₁ .σ enEv₁ satQ')
    = let tail = satQ'∧S⇒satQ' stableS satS {!!} {!!}
      in {!!}




  soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → Reachable {sm = StMachine} st
              → (σ : Behavior st)
              → σ satisfiesNew P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfiesNew Q at j
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
        with soundness2 rS σ (satQ'∧S⇒satQ' stableS anyS n<k anyQ') q'∧s→q
  ...     | j , k<j , anyQ = j , ≤-trans 0<n (≤-trans n<k k<j) , anyQ
  soundness2 rS σ (there n .σ enEv x₁) x₂
    with soundness2 (step rS enEv) (σ .tail enEv) x₁ x₂
  ... | j , j<i , tail⊢Q = suc j , s≤s j<i , (there j σ enEv tail⊢Q)

