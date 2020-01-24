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


  record Behavior (S : State) :
    Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tail  : ∀ {e : Event} → (enEv : enabled StMachine e S)
              → Behavior (action StMachine enEv)
  open Behavior



  data ReachableFrom {st} (σ : Behavior st) :
       ∀ {s} → Behavior s → ℕ → Set (ℓ₁ ⊔ ℓ₂) where
    head : ReachableFrom σ σ zero
    next : ∀ {e} → (enEv : enabled StMachine e st)
                  → ReachableFrom σ (σ .tail enEv) 1
    transR : ∀ {st₁ st₂ : State} {n m : ℕ}
               {σ₁ : Behavior st₁} {σ₂ : Behavior st₂}
               → ReachableFrom σ σ₁ n
               → ReachableFrom σ₁ σ₂ m
               → ReachableFrom σ σ₂ (n + m)


  record _satisfies_at_ {st : State} {ℓ} (σ : Behavior st) (P : Pred State ℓ) (i : ℕ) :
    Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂) where
    coinductive
    constructor satisfy
    field
      tl-any : P st
               ⊎
               ∀ {e} → (enEv : enabled StMachine e st) → σ .tail enEv satisfies P at suc i
               -- ∀ {s : State} {σ₁ : Behavior s} ????
  open _satisfies_at_


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
  rFrom→reachable : ∀ {s₁ s₂}
                    → Reachable {sm = StMachine} s₁
                    → (σ₁ : Behavior s₁)
                    → (σ₂ : Behavior s₂)
                    → ReachableFrom σ₁ σ₂
                    → Reachable {sm = StMachine} s₂
  rFrom→reachable r σ₁ .σ₁ head = r
  rFrom→reachable r σ₁ .(σ₁ .tail enEv) (next enEv) = step r enEv
  rFrom→reachable r σ₁ σ₂ (transR {σ₁ = σ₃} x x₁)
    with rFrom→reachable r σ₁ σ₃ x
  ... | z = rFrom→reachable z σ₃ σ₂ x₁

  rFrom→stable : ∀ {s₁ s₂} {ℓ₄} {S : Pred State ℓ₄} {σ₂ : Behavior s₂}
                 → Stable StMachine S
                 → S s₁
                 → (σ₁ : Behavior s₁)
                 → ReachableFrom σ₁ σ₂
                 → S s₂
  rFrom→stable stableS st∈S σ₁ head = st∈S
  rFrom→stable stableS st∈S σ₁ (next enEv) = stableS enEv st∈S
  rFrom→stable stableS st∈S σ₁ (transR {σ₁ = σ₃} σ₁rfσ₃ σ₃rfσ₂)
    = rFrom→stable stableS (rFrom→stable stableS st∈S σ₁ σ₁rfσ₃) σ₃ σ₃rfσ₂


  σ⊢q⇒σ⊢q∧s : ∀ {st} {ℓ₄} {Q : Pred State 0ℓ} {S : Pred State ℓ₄}
              → (σ : Behavior st)
              → Stable StMachine S
              → S st
              → σ satisfies Q
              → σ satisfies (Q ∩ S)
  tl-any (σ⊢q⇒σ⊢q∧s σ stableS st∈S σ⊢q)
    with tl-any σ⊢q
  ... | inj₁ st∈Q = inj₁ (st∈Q , st∈S)
  ... | inj₂ (s , σ₁ , rFrom , sat)
      with σ⊢q⇒σ⊢q∧s σ₁ stableS (rFrom→stable stableS st∈S σ rFrom) sat
  ... | σ₁⊢q∧s = inj₂ (s , σ₁ , rFrom , σ₁⊢q∧s)



  [r⇒q]∧r⇒[q] : ∀ {st} {ℓ₃ ℓ₄} {R : Pred State ℓ₃} {Q : Pred State ℓ₄}
                  {σ : Behavior st}
                → Reachable {sm = StMachine} st
                → σ satisfies (R ⇒ Q)
                → Invariant StMachine R
                → σ satisfies Q
  tl-any ([r⇒q]∧r⇒[q] {σ = σ} rSt σ⊢r⇒q invR)
    with tl-any σ⊢r⇒q
  ... | inj₁ r⇒q = inj₁ (r⇒q (invR rSt))
  ... | inj₂ (s , σ₁ , rFrom , sat)
      with [r⇒q]∧r⇒[q] (rFrom→reachable rSt σ σ₁ rFrom) sat invR
  ...   | σ₁⊢q = inj₂ (s , σ₁ , rFrom , σ₁⊢q)


 -}

  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x


  soundness : ∀ {st ℓ₃ ℓ₄}  {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                {i : ℕ}
              → (rSt : Reachable {sm = StMachine} st)
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  proj₁ (soundness {i = i} rSt σ satP (viaEvSet eventSet wF c₁ c₂ c₃))
    = suc i
  proj₁ (proj₂ (soundness rSt σ satP (viaEvSet eventSet wF c₁ c₂ c₃)))
    = ≤-step ≤-refl
  tl-any (proj₂ (proj₂ (soundness {st} {P = P} {i = i}
                                  rSt σ satP rule@(viaEvSet evSet wF c₁ c₂ c₃))))
    with tl-any satP
  ... | inj₂ tS =
         inj₂ (λ enEv → let next = step rSt enEv
                            tail = σ .tail enEv
                            prf  = soundness next tail (tS enEv) rule
                        in (proj₂ ∘ proj₂) prf)
  ... | inj₁ pS =
         inj₂ (λ { {e} enEv
           → case e ∈Set? evSet of
           λ { (yes p)
               → let qS = [P]e[Q]∧P⇒Q enEv pS (c₁ e p)
                 in satisfy (inj₁ qS)
            ; (no ¬p)
              → case c₂ e ¬p of
              λ { (hoare p∨q)
                  → case  p∨q pS enEv of
                  λ { (inj₂ qAS) → satisfy (inj₁ qAS)
                    ; (inj₁ pAS)
                      → let next = step rSt enEv
                            tail = σ .tail enEv
                            satP = satisfy (inj₁ pAS)
                            satQ = soundness next tail satP rule
                        in (proj₂ ∘ proj₂) satQ }}}})
  proj₁ (soundness {i = i} rSt σ satP (LeadsTo.viaInv inv)) = i
  proj₁ (proj₂ (soundness {i = i} rSt σ satP (LeadsTo.viaInv inv))) = ≤-refl
  tl-any (proj₂ (proj₂ (soundness {i = i} rSt σ satP rule@(viaInv inv))))
    with tl-any satP
  ... | inj₁ pS    = inj₁ (inv rSt pS)
  ... | inj₂ tailP = inj₂ (λ enEv →  let next = step rSt enEv
                                         tail = σ .tail enEv
                                         satP = tailP enEv
                                         satQ = soundness next tail satP rule
                                     in (proj₂ ∘ proj₂) satQ)
  soundness rSt σ satP rule@(viaTrans lt lt₁) = {!!}
  soundness rSt σ satP rule@(viaTrans2 lt lt₁) = {!!}
  soundness rSt σ satP rule@(viaDisj x lt lt₁) = {!!}
  soundness rSt σ satP rule@(viaUseInv x lt) = {!!}
  soundness rSt σ satP rule@(viaWFR F lt x) = {!!}
  soundness rSt σ satP rule@(viaStable lt lt₁ x lt₂) = {!!}



 {- tl-any (soundness {st = st} {P} {Q} stR σ σ⊢p rule@(viaEvSet evSet wf c₁ c₂ c₃))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
        = inj₂ (s , σ₁ , rFrom , (soundness
                                   (rFrom→reachable stR σ σ₁ rFrom)
                                   σ₁
                                   satP
                                   rule))
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
                                        rule )

  tl-any (soundness rSt σ σ⊢p rule@(viaInv inv))
    with tl-any σ⊢p
  ... | inj₁ s∈P
             = inj₁ (inv rSt s∈P)
  ... | inj₂ (s , σ₁ , rFrom , satP)
             = inj₂ (s , σ₁ , rFrom , (soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satP
                                        rule))
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

  tl-any (soundness rSt σ σ⊢p rule@(viaDisj p⊆p₁∨p₂ p₁→q p₂→q))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
        = inj₂ (s , σ₁ , rFrom , soundness
                                   (rFrom→reachable rSt σ σ₁ rFrom)
                                   σ₁
                                   satP
                                   rule)
  ... | inj₁ pSt
      with p⊆p₁∨p₂ pSt
  ...   | inj₁ p₁St = tl-any (soundness rSt σ (satisfy (inj₁ p₁St)) p₁→q)
  ...   | inj₂ p₂St = tl-any (soundness rSt σ (satisfy (inj₁ p₂St)) p₂→q)

  tl-any (soundness rSt σ σ⊢p rule@(viaUseInv invR p∧r→r∧q))
    with tl-any σ⊢p
  ... | inj₂ (s , σ₁ , rFrom , satP)
             = inj₂ (s , σ₁ , rFrom , soundness
                                        (rFrom→reachable rSt σ σ₁ rFrom)
                                        σ₁
                                        satP
                                        rule )
  ... | inj₁ pSt
      with tl-any (soundness rSt σ (satisfy (inj₁ (pSt , (invR rSt)))) p∧r→r∧q)
  ...   | inj₁ r→q
               = inj₁ (r→q (invR rSt))
  ...   | inj₂ (s , σ₁ , rFrom , satR→Q)
               = inj₂ (s , σ₁ , rFrom , ([r⇒q]∧r⇒[q]
                                             (rFrom→reachable rSt σ σ₁ rFrom)
                                             satR→Q
                                             invR))

  tl-any (soundness rSt σ σ⊢p rule@(viaStable p⇒p'∧s p'⇒q' stableS q'∧s⇒q))
    with tl-any (soundness rSt σ σ⊢p p⇒p'∧s)
  ... | inj₂ (s , σ₁ , rFrom , satP'∧S)
               = let p'∧s⇒q'∧s = viaStable (viaInv (λ rs x → x))
                                           p'⇒q'
                                           stableS
                                           (viaInv (λ rs x → x))
                     rS        = rFrom→reachable rSt σ σ₁ rFrom
                     p'∧s⇒q    = viaTrans p'∧s⇒q'∧s q'∧s⇒q
                 in inj₂ (s , σ₁ , rFrom , (soundness rS σ₁ satP'∧S p'∧s⇒q ) )
  ... | inj₁ (p'St , sSt)
      with tl-any (soundness rSt σ (satisfy (inj₁ p'St)) p'⇒q')
  ...   | inj₁ q'St
             = tl-any (soundness rSt σ (satisfy (inj₁ (q'St , sSt))) q'∧s⇒q)
  ...   | inj₂ (s , σ₁ , rFrom , satQ')
             = let sReach  = rFrom→reachable rSt σ σ₁ rFrom
                   s∈S     = rFrom→stable stableS sSt σ rFrom
                   satQ'∧S = σ⊢q⇒σ⊢q∧s σ₁ stableS s∈S satQ'
               in inj₂ (s , σ₁ , rFrom , soundness sReach σ₁ satQ'∧S q'∧s⇒q)


  tl-any (soundness rSt σ σ⊢p rule@(viaWFR F p⇒q∨f f⇒q∨f))
    with tl-any (soundness rSt σ σ⊢p p⇒q∨f)
  ... | inj₂ (s , σ₁ , rFrom , sat)
             = let sR   = rFrom→reachable rSt σ σ₁ rFrom
                   wfrN = viaWFR F (viaInv (λ rs x → x)) f⇒q∨f
               in inj₂ (s , σ₁ , rFrom , soundness sR σ₁ sat wfrN)
  ... | inj₁ (inj₁ s∈Q) = inj₁ s∈Q
  ... | inj₁ (inj₂ (suc w , w∈F))
             = let x = viaWFR F (viaInv (λ rs x → x)) f⇒q∨f
               in tl-any {!!} --(soundness rSt σ (satisfy (inj₁ (inj₂ ((suc w) , w∈F)))) x)
  ... | inj₁ (inj₂ (zero , w∈F))
    with tl-any (soundness rSt σ (satisfy (inj₁ w∈F)) (f⇒q∨f zero))
  ... | inj₁ (inj₁ qSt) = inj₁ qSt
  ... | inj₂ (s , σ₁ , rFrom , sat)
             = let sR   = rFrom→reachable rSt σ σ₁ rFrom
                   wfrN = viaWFR F (viaInv (λ { rs (inj₁ qSt) → inj₁ qSt})) f⇒q∨f
               in inj₂ (s , σ₁ , rFrom , soundness sR σ₁ sat wfrN)
-}
