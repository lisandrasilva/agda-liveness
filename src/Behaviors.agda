open import Prelude

open import StateMachineModel
open StateMachine
open System
open import Size

module Behaviors {ℓ₁ ℓ₂}
       (State : Set ℓ₁)
       (Event : Set ℓ₂)
       (sys : System State Event)
       (∃Enabled?_ : (st : State)
                     → Dec (Σ[ e ∈ Event ] enabled (stateMachine sys) e st))
       (_∈Set?_ : (ev : Event) (evSet : EventSet)
                  → Dec (evSet ev))
  where

  open LeadsTo State Event sys

  StMachine = stateMachine sys


  data Behavior (st : State) : Set (ℓ₁ ⊔ ℓ₂) where
      last :  ¬ (Σ[ e ∈ Event ] enabled StMachine e st)
                → Behavior st
      _∷_  : ∀ {e} → (enEv : enabled StMachine e st)
                → Behavior (action StMachine enEv)
                → Behavior st
  open Behavior




  data AnyS∈B {ℓ} (P : Pred State ℓ)
    : ∀ {st : State} → ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {st} {σ : Behavior st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {st e} (n : ℕ)
              (enEv : enabled StMachine e st)
              {t : Behavior (action StMachine enEv)}
              (pts  : AnyS∈B P n t)
            → AnyS∈B P (suc n) (enEv ∷ t)


   -- A behavior σ satisfies P if there is any state ∈ σ satisfies P
  _satisfies_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P at i = AnyS∈B P i σ



  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x



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
  witness {st} rS (there n enEv x₁) = witness (step rS enEv) x₁


  trans2 :  ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → σ satisfies (Q ∪ R) at i
              →   Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
                ⊎ Σ[ j ∈ ℕ ] i ≤ j × σ satisfies R at j
  trans2 (here (inj₁ qS)) = inj₁ (zero , ≤-refl , here qS)
  trans2 (here (inj₂ rS)) = inj₂ (zero , z≤n , here rS)
  trans2 (there n enEv tailQ∨R)
    with trans2 tailQ∨R
  ... | inj₁ (j , i≤j , tailQ) = inj₁ (suc j , s≤s i≤j , there j enEv tailQ)
  ... | inj₂ (j , i≤j , tailR) = inj₂ (suc j , s≤s i≤j , there j enEv tailR)




  useInv : ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → Invariant StMachine R
              → Reachable {sm = StMachine} st
              → σ satisfies (R ⇒ Q) at i
              → σ satisfies Q at i
  useInv inv rS (here ps)
    = here (ps (inv rS))
  useInv inv rS (there n enEv x)
    = there n enEv (useInv inv (step rS enEv) x)


  stable : ∀ {st} {ℓ₃ ℓ₄} {P' : Pred State ℓ₃} {S : Pred State ℓ₄}
             {i : ℕ} {σ : Behavior st}
            → Stable StMachine S
            → Reachable {sm = StMachine} st
            → σ satisfies (P' ∩ S) at i
            → σ satisfies P' at i × σ satisfies S at i
  stable stableS rS (here (p' , s))
    = here p' , here s
  stable stableS rS (there n enEv satP'∧S)
    with stable stableS (step rS enEv) satP'∧S
  ... | tailP' , tailS = (there n enEv tailP')
                       , (there n enEv tailS)


  aux : ∀ {st} {ℓ₃ ℓ₄} {Q' : Pred State ℓ₃} {S : Pred State ℓ₄}
           {i j : ℕ} {σ : Behavior st}
            → Stable StMachine S
            → Reachable {sm = StMachine} st
            → j ≤ i
            → σ satisfies S at j
            → σ satisfies Q' at i
            → σ satisfies (Q' ∩ S) at i
  aux stableS rS j≤i (here ss) (here q's) = here (q's , ss)
  aux stableS rS j≤i (here ss) (there n enEv σ⊢Q')
    = there n enEv (aux stableS (step rS enEv) z≤n (here (stableS enEv ss)) σ⊢Q')
  aux stableS rS j≤i (there n enEv σ⊢S) (there n₁ .enEv σ⊢Q')
    = there n₁ enEv (aux stableS (step rS enEv) (+-cancelˡ-≤ 1 j≤i) σ⊢S σ⊢Q')


  wfr-zero : ∀ {st} {ℓ₄} {F : Z → Pred State 0ℓ} {Q : Pred State ℓ₄} {i : ℕ}
             → (σ : Behavior st)
             → (prf : ¬ (Σ[ e ∈ Event ] enabled StMachine e st))
             → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies (Q ∪ [∃ x ⇒ _< zero ∶ F x ]) at j
             → σ satisfies Q at zero
  wfr-zero (last x₁) ¬enEv (zero , 0≤0 , here (inj₁ qS)) = here qS
  wfr-zero (_∷_ {e} enEv σ) ¬enEv x = ⊥-elim (¬enEv (e , enEv))


{-
  wfr-sucw : ∀ {st} {ℓ₄} {F : Z → Pred State 0ℓ} {Q : Pred State ℓ₄} {i w : ℕ}
             → (σ : Behavior st)
             → (prf : ¬ (Σ[ e ∈ Event ] enabled StMachine e st))
             → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies (Q ∪ [∃ x ⇒ _< (suc w) ∶ F x ]) at j
             → (σ satisfies Q at zero) ⊎ σ satisfies F zero at zero
  wfr-sucw {w = w} (last x₁) ¬enEv (0 , z≤n , here (inj₁ x))
    = inj₁ (here x)
  wfr-sucw {w = w} (last x₁) ¬enEv (zero , z≤n , here (inj₂ (zero , s≤s z≤n , f0)))
    = inj₂ (here f0)
  wfr-sucw {w = 0} (last x₁) ¬enEv (0 , z≤n , here (inj₂ (suc fst , s≤s () , fs)))
  wfr-sucw {F = F} {w = suc w} (last x₁) ¬enEv (0 , z≤n , here (inj₂ (suc fst , s≤s <p , p))) = {!!}
  {-  with wfr-sucw {w = 2 + w} (last x₁) ¬enEv (0 , z≤n , (here (inj₂ ((suc fst) , (s≤s {!!}) , p))))
  ... | v = {!!} -}
  wfr-sucw (_∷_ {e} enEv σ) ¬enEv x = ⊥-elim (¬enEv (e , enEv))
-}



  soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → Reachable {sm = StMachine} st
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness2 {P = P} rS (last ¬enEv) (here ps) (viaEvSet evSet x c₁ c₂ c₃)
    = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ rS ps)))
  soundness2 {st} {P = P} rS (_∷_ {e} enEv t) (here ps)
                          rule@(viaEvSet evSet x c₁ c₂ c₃)
    with e ∈Set? evSet
  ... | yes ∈evSet = let ht = c₁ e ∈evSet
                         qS = [P]e[Q]∧P⇒Q enEv ps ht
                      in 1 , z≤n , there 0 enEv (here qS)
  ... | no  ∉evSet
       with c₂ e ∉evSet
  ...     | hoare p∨q
          with p∨q ps enEv
  ...       | inj₂ qActionSt = 1 , z≤n , (there 0 enEv (here qActionSt))
  ...       | inj₁ pActionSt
            with soundness2 (step rS enEv) t (here pActionSt) rule
  ...         | n , 1≤n , tail⊢q = (suc n) , z≤n , (there n enEv tail⊢q)

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

{-
  soundness2 rS σ (here ps) (viaWFR F p→q∨f f→q∨f<)
    with soundness2 rS σ (here ps) p→q∨f
  ... | n , 0<n , anyQ∨F
      with trans2 anyQ∨F
  ...   | inj₁ (j , n≤j , anyQ) = j , ≤-trans 0<n n≤j , anyQ
  ...   | inj₂ (0 , n≤j , here (w , fS)) = {!!}
  ...   | inj₂ ((suc n₁) , n≤j , there n₁ enEv anyF) = {!!}
-}

  soundness2 rS σ@(last x) (here ps) (viaWFR F p→q∨f f→q∨f<)
   with soundness2 rS σ (here ps) p→q∨f
  ... | 0 , 0<n , here (inj₁ qS) = 0 , z≤n , (here qS)
  ... | 0 , z≤n , here (inj₂ (0 , fw))
        = 0 , z≤n , wfr-zero σ x (soundness2 rS σ (here fw) (f→q∨f< 0))
  ... | 0 , z≤n , here (inj₂ (suc w , fw))
      with soundness2 rS σ (here fw) (f→q∨f< (suc w))
  ...   | 0 , z≤n , anyQ∨F
      with trans2 anyQ∨F
  ...     | inj₁ anyQ = anyQ
  ...     | inj₂ (0 , z≤n , here (0 , j<w , p))
                 = 0 , z≤n , (wfr-zero σ x (soundness2 rS σ (here p) (f→q∨f< 0)))
  ...     | inj₂ (zero , z≤n , here (suc j , s≤s (s≤s j<w) , p)) = {!!}


  soundness2 rS σ@(enEv ∷ t) (here ps) (viaWFR F p→q∨f f→q∨f<)
    with soundness2 rS σ (here ps) p→q∨f
  ... | 0 , 0<n , here (inj₁ qS) = 0 , z≤n , (here qS)
  ... | (suc n) , 0<n , there n enEv anyQ∨F
             = let next = step rS enEv
                   vInv = viaInv λ { rs (inj₁ qS) → inj₁ qS
                                   ; rs (inj₂ fS) → inj₂ fS }
                   rule = viaWFR F vInv f→q∨f<
                   (k , n<k , anyQ) = soundness2 next t anyQ∨F rule
                in suc k , (≤-trans 0<n (s≤s n<k)) , (there k enEv anyQ)
  ... | 0 , 0<n , here (inj₂ (fst , snd)) = {!!}

  soundness2 rS σ (here ps) rule@(viaStable p→p'∧s p'→q stableS q'∧s→q)
    with soundness2 rS σ (here ps) p→p'∧s
  ... | n , 0<n , anyP'∧S
      with stable stableS rS anyP'∧S
  ...   | anyP' , anyS
        with soundness2 rS σ anyP' p'→q
  ...     | k , n<k , anyQ'
          with soundness2 rS σ (aux stableS rS n<k anyS anyQ') q'∧s→q
  ...       | j , k<j , anyQ = j , ≤-trans 0<n (≤-trans n<k k<j) , anyQ

  soundness2 rS σ (there n enEv {t} x₁) x₂
    with soundness2 (step rS enEv) t x₁ x₂
  ... | j , j<i , tail⊢Q = suc j , s≤s j<i , there j enEv tail⊢Q


  soundness : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → (initial StMachine st)
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness x σ x₁ x₂ = soundness2 (init x) σ x₁ x₂
