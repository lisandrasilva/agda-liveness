open import Prelude

open import StateMachineModel
open StateMachine
open System
open import Relation.Nullary.Negation using (contraposition; contradiction)

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


  record Behavior (S : State) :
    Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tail  : ∀ {e : Event} → (enEv : enabled StMachine e S)
              → Behavior (action StMachine enEv)
  open Behavior



  data ReachableFrom {st} (σ : Behavior st) :
       ∀ {s} → Behavior s → Set (ℓ₁ ⊔ ℓ₂) where
    next : ∀ {e} → (enEv : enabled StMachine e st)
                  → ReachableFrom σ (σ .tail enEv)
    transR : ∀ {st₁ st₂ : State} {σ₁ : Behavior st₁} {σ₂ : Behavior st₂}
               → ReachableFrom σ σ₁
               → ReachableFrom σ₁ σ₂
               → ReachableFrom σ σ₂


  record _satisfies_ {st : State} {ℓ} (σ : Behavior st) (P : Pred State ℓ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    constructor satisfy
    field
      tl-any : P st
                 ⊎
               ∀ {e} (enEv : enabled StMachine e st) → σ .tail enEv satisfies P
  open _satisfies_


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



  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x


  contradict : ∀ {st} {ℓ} {P : Pred State ℓ}
               → (σ : Behavior st)
               → ¬ Σ Event (λ e → enabled (stateMachine sys) e st)
               → (∀ {e : Event} (enEv : enabled (stateMachine sys) e st)
                 → ¬ σ .tail enEv satisfies P)
  contradict σ ¬enabled = {!!}



  satP⇒∃st⊢P : ∀ {st} {ℓ} {P : Pred State ℓ}
               → (rs : Reachable {sm = StMachine} st)
               → (σ : Behavior st)
               → σ satisfies P
               → Σ[ s ∈ State ] Σ[ σ₁ ∈ Behavior s ]
                    (Reachable {sm = StMachine} s × P s)
  satP⇒∃st⊢P {st} rs σ satP
    with tl-any satP
  ... | inj₁ pS = st , σ , rs , pS
  ... | inj₂ y
      with ∃Enabled? st
  ... | no ¬p = contradiction (contradict {!!} {!!}) λ { x → {!!}}
  ... | yes (e , enEv) = satP⇒∃st⊢P (step rs enEv) (tail σ enEv) (y enEv)



  soundness : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                    → (rSt : Reachable {sm = StMachine} st)
                    → (σ : Behavior st)
                    → P st
                    → P l-t Q
                    → σ satisfies Q
  tl-any (soundness {st} {P = P} rS σ pS rule@(viaEvSet evSet wF c₁ c₂ c₃))
    = inj₂ (λ {e} enEv
           → case e ∈Set? evSet of
              λ { (yes p)
                       → let qS = [P]e[Q]∧P⇒Q enEv pS (c₁ e p)
                         in satisfy (inj₁ qS)
                ; (no ¬p)
                       → case c₂ e ¬p of
                         λ { (hoare p∨q)
                                    → case p∨q pS enEv of
                                      λ { (inj₂ qS)
                                                → satisfy (inj₁ qS)
                                        ; (inj₁ pNS)
                                                → let nS = step rS enEv
                                                      σt = tail σ enEv
                                                   in soundness nS σt pNS rule
                                        }
                           }
                }
             )
  tl-any (soundness rS σ pS (viaInv inv)) = inj₁ (inv rS pS)
  soundness rS σ pS (LeadsTo.viaTrans x₁ x₂) = {!!}
  soundness rS σ pS (LeadsTo.viaTrans2 x₁ x₂) = {!!}
  soundness rS σ pS (LeadsTo.viaDisj x₁ x₂ x₃) = {!!}
  soundness rS σ pS (LeadsTo.viaUseInv x₁ x₂) = {!!}
  soundness rS σ pS (LeadsTo.viaWFR F x₁ x₂) = {!!}
  soundness rS σ pS (LeadsTo.viaStable x₁ x₂ x₃ x₄) = {!!}
{-  tl-any (soundness {st = st} {P} {Q} stR σ σ⊢p prf@(viaEvSet evSet wf c₁ c₂ c₃))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
        = inj₂ (s , σ₁ , rFrom , (soundness
                                   (rFrom→reachable stR σ σ₁ rFrom)
                                   σ₁
                                   satP
                                   prf))
  ... | inj₁ s∈P
      with ∃Enabled? st
  ...   | no ¬enEv = ⊥-elim (¬enEv (c₃→∃enEv {P = P} (c₃ stR s∈P)))
  ...   | yes (ev , enEv)
        with ev ∈Set? evSet
  ...     | yes e∈s = inj₂ ( action StMachine enEv
                         , σ .tail enEv
                         , next enEv
                         , satisfy (inj₁ ([P]e[Q]∧P⇒Q enEv s∈P (c₁ ev e∈s))) )
  ...     | no ¬e∈s
          with c₂ ev ¬e∈s
  ...       | hoare p∨q
            with p∨q s∈P enEv
  ...         | inj₂ qActionSt = inj₂ ( action StMachine enEv
                                    , σ .tail enEv
                                    , next enEv
                                    , satisfy (inj₁ qActionSt) )
  ...         | inj₁ pActionSt = inj₂ ( action StMachine enEv
                                    , σ .tail enEv
                                    , next enEv
                                    , soundness
                                        (step stR enEv)
                                        (σ .tail enEv)
                                        (satisfy (inj₁ pActionSt))
                                        prf )
  tl-any (soundness rSt σ σ⊢p prf@(viaInv inv))
    with tl-any σ⊢p
  ... | inj₁ s∈P
             = inj₁ (inv rSt s∈P)
  ... | inj₂ (s , σ₁ , rFrom , satP)
             = inj₂ (s , σ₁ , rFrom , (soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satP
                                        prf))
  tl-any (soundness {st = st} rSt σ x (viaTrans p→r r→q))
    with tl-any (soundness rSt σ x p→r)
  ... | inj₁ r∈s
             = inj₂ (st , σ , head , soundness rSt σ (satisfy (inj₁ r∈s)) r→q)
  ... | inj₂ (s , σ₁ , rFrom , satR)
             = inj₂ (s , σ₁ , rFrom , soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satR
                                        r→q)
  tl-any (soundness {st = st} rSt σ σ⊢p (viaTrans2 x₁ x₂))
    with tl-any (soundness rSt σ σ⊢p x₁)
  ... | inj₂ (s , σ₁ , rFrom , satR∨Q)
             = inj₂ (s , σ₁ , rFrom , soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satR∨Q
                                        (viaTrans2 (viaInv (λ rs x₃ → x₃)) x₂))
  ... | inj₁ (inj₁ qS) = inj₁ qS
  ... | inj₁ (inj₂ rS) = tl-any (soundness rSt σ (satisfy (inj₁ rS)) x₂)
  tl-any (soundness rSt σ σ⊢p (viaDisj p⊆p₁∨p₂ p₁→q p₂→q))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
        = inj₂ (s , σ₁ , rFrom , soundness
                                   (rFrom→reachable rSt σ σ₁ rFrom)
                                   σ₁
                                   satP
                                   (viaDisj p⊆p₁∨p₂ p₁→q p₂→q))
  ... | inj₁ pSt
      with p⊆p₁∨p₂ pSt
  ...   | inj₁ p₁St = tl-any (soundness rSt σ (satisfy (inj₁ p₁St)) p₁→q)
  ...   | inj₂ p₂St = tl-any (soundness rSt σ (satisfy (inj₁ p₂St)) p₂→q)
  tl-any (soundness rSt σ σ⊢p prf@(viaUseInv invR p∧r→r∧q))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
             = inj₂ (s , σ₁ , rFrom , soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satP
                                        prf )
  ... | inj₁ pSt
      with tl-any (soundness rSt σ (satisfy (inj₁ (pSt , (invR rSt)))) p∧r→r∧q)
  ...   | inj₁ r→q
               = inj₁ (r→q (invR rSt))
  ...   | inj₂ (s , σ₁ , rFrom , satR→Q)
               = inj₂ (s , σ₁ , rFrom , ([r⇒q]∧r⇒[q]
                                             (rFrom→reachable rSt σ σ₁ rFrom)
                                             satR→Q
                                             invR))
  soundness rSt σ σ⊢p (viaWFR F x₁ x₂) = {!!}
  tl-any (soundness rSt σ σ⊢p prf@(viaStable p⇒p'∧s p'⇒q' stableS q'∧s⇒q))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
             = inj₂ (s , σ₁ , rFrom , soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satP
                                        prf)
  ... | inj₁ pSt
      with tl-any (soundness rSt σ (satisfy (inj₁ pSt)) p⇒p'∧s)
  ...   | inj₂ (s , σ₁ , rFrom , satP'∧S)
               = let p'∧s⇒q'∧s = viaStable (viaInv (λ rs x → x))
                                           p'⇒q'
                                           stableS
                                           (viaInv (λ rs x → x))
                 in inj₂ (s , σ₁ , rFrom , (soundness
                                          (rFrom→reachable rSt σ σ₁ rFrom)
                                          σ₁
                                          satP'∧S
                                          (viaTrans p'∧s⇒q'∧s q'∧s⇒q) ) )
  ...   | inj₁ (p'St , sSt)
        with tl-any (soundness rSt σ (satisfy (inj₁ p'St)) p'⇒q')
  ... | inj₁ q'St
             = tl-any (soundness rSt σ (satisfy (inj₁ (q'St , sSt))) q'∧s⇒q)
  ... | inj₂ (s , σ₁ , rFrom , satQ')
             = let sReach  = rFrom→reachable rSt σ σ₁ rFrom
                   s∈S     = rFrom→stable stableS sSt σ rFrom
                   satQ'∧S = σ⊢q⇒σ⊢q∧s σ₁ stableS s∈S satQ'
               in inj₂ (s , σ₁ , rFrom , soundness sReach σ₁ satQ'∧S q'∧s⇒q)
-}
