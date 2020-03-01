open import Prelude

open import StateMachineModel
open StateMachine
open System
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.Core using (Tri)


module Behaviors {ℓ₁ ℓ₂}
       (State : Set ℓ₁)
       (Event : Set ℓ₂)
       (sys : System State Event)
       (_∈Set?_ : (ev : Event) (evSet : EventSet) → Dec (evSet ev))
  where

  open LeadsTo State Event sys

  StMachine = stateMachine sys


  -- A Behavior is a coinductive data type, such that it has a head with a given
  -- state S and a tail that can be next state for an existent transition or can
  -- be finite, which means that there is no enabled transition

  -- Question : Would it make more sense the behavior over
  --            ReachableState instead of State???
  record Behavior (S : State) :
    Set (ℓ₁ ⊔ ℓ₂) where
    coinductive
    field
      tail  : Σ[ e ∈ Event ] Σ[ enEv ∈ enabled StMachine e S ]
                 Behavior (action StMachine enEv)
              ⊎
              ¬ ( Σ[ e ∈ Event ] enabled StMachine e S )
  open Behavior


  -- Auxiliary function that allows to do pattern matching on the RHS of an
  -- expression.
  -- (ref: https://agda.readthedocs.io/en/v2.5.2/language/with-abstraction.html)
  case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
  case x of f = f x



  -- Inductive data type to express that Any State ∈ Behavior (AnyS∈B) satisfies
  -- a given Predicate P at a given index n
  -- It's similar to the Any for Lists, with the difference that in the 'there'
  -- contructor we also need to give a proof that the behavior has a tail t.
  data AnyS∈B {ℓ} {st} (P : Pred State ℓ)
    : ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    here  : ∀ {σ : Behavior st} (ps  : P st)
            → AnyS∈B P zero σ
    there : ∀ {e enEv t} {σ : Behavior st} (n : ℕ)
            → tail σ ≡ inj₁ (e , enEv , t)
            → AnyS∈B P n t
            → AnyS∈B P (suc n) σ



  -- Syntactic sugar for better reading of lemmas:
  -- σ satisfies P at i if there is a state ∈ σ that satisfies P at i
  _satisfies_at_ : ∀ {st : State} {ℓ}
                → (σ : Behavior st)
                → (P : Pred State ℓ)
                → ℕ
                → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  σ satisfies P at i = AnyS∈B P i σ


  -- Gives the tail of the behavior after n transitions.
  -- If the behavior is finite returns the behavior itself
  drop : ∀ {st} → ℕ → (σ : Behavior st) → Σ[ s ∈ State ] Behavior s
  drop {st} zero σ = st , σ
  drop {st} (suc n) σ
     with tail σ
  ... | inj₁ (e , enEv , t) = drop n t
  ... | inj₂ ¬enEv = st , σ


  -- Inductive data type to express that all states in a behavior n satisfy a
  -- Predicate P up to a given index n
  -- It's similar to the All for Lists, with the difference that in the '_∷_'
  -- contructor we also need to give a proof that the behavior has a tail t.
  data AllSt {ℓ} {st : State} (P : Pred State ℓ)
    : ℕ → Pred (Behavior st) (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
    where
    last  : ∀ {σ : Behavior st}
            → (ps  : P st)
            → AllSt P zero σ
    _∷_∣_ : ∀ {e enEv t n} {σ : Behavior st}
            → (ps  : P st)
            → tail σ ≡ inj₁ (e , enEv , t)
            → (pts  : AllSt P n t)
            → AllSt P (suc n) σ


  -- Syntactic sugar for better reading of lemmas
  AllSt_upTo_sat_ : ∀ {st : State} {ℓ}
                 → (σ : Behavior st)
                 → ℕ
                 → (P : Pred State ℓ)
                 → Set (ℓ ⊔ ℓ₁ ⊔ ℓ₂)
  AllSt σ upTo n sat P = AllSt P n σ


 ------------------------------------------------------------------------------
 -- PROOF
 ------------------------------------------------------------------------------
  -- If a behavior σ satisfies P at i then it exists a state s at index i such
  -- that s is reachable and P s
  witness : ∀ {st : State} {ℓ i} {σ : Behavior st} {P : Pred State ℓ}
            → Reachable {sm = StMachine} st
            → σ satisfies P at i
            → Σ[ state ∈ State ]
                 Σ[ rSt ∈ Reachable {sm = StMachine} state ] P state
  witness {st} rS (here ps) = st , rS , ps
  witness {st} rS (there {σ = σ} n eq satP)
    with tail σ | eq
  ... | inj₁ (e , enEv , t) | refl = witness (step rS enEv) satP


  -- If a behavior σ satisfies Q ∪ R at a given index i then
  -- or σ satisfies Q at i or σ satisfies R at i
  trans2 :  ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → σ satisfies (Q ∪ R) at i
              →   σ satisfies Q at i
                ⊎ σ satisfies R at i
  trans2 (here (inj₁ qS)) = inj₁ (here qS)
  trans2 (here (inj₂ rS)) = inj₂ (here rS)
  trans2 {σ = σ} (there n eq tailQ∨R)
    with tail σ | eq
  ... | inj₁ (e , enEv , t) | refl
      with trans2 tailQ∨R
  ... | inj₁ anyQ = inj₁ (there n eq anyQ)
  ... | inj₂ anyR = inj₂ (there n eq anyR)


  -- If σ satisfies (R ⇒ Q) at a given index i and if R is an invariant then
  -- σ satisfies Q at i
  useInv : ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {R : Pred State ℓ₄}
              {i : ℕ} {σ : Behavior st}
              → Invariant StMachine R
              → Reachable {sm = StMachine} st
              → σ satisfies (R ⇒ Q) at i
              → σ satisfies Q at i
  useInv inv rS (here r→q) = here (r→q (inv rS))
  useInv inv rS (there {e} {enEv} n eq sat)
    = there n eq (useInv inv (step rS enEv) sat)


  -- If σ satisfies (P ∩ S) at i then σ satisfies P at i and σ satisfies S at i
  σ⊢P∧S⇒σ⊢P∧σ⊢S : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {S : Pred State ℓ₄}
                     {i : ℕ} {σ : Behavior st}
                   → σ satisfies (P ∩ S) at i
                   → σ satisfies P at i × σ satisfies S at i
  σ⊢P∧S⇒σ⊢P∧σ⊢S (here (p' , s))
    = here p' , here s
  σ⊢P∧S⇒σ⊢P∧σ⊢S (there {e} {enEv} n eq satP'∧S)
    with σ⊢P∧S⇒σ⊢P∧σ⊢S satP'∧S
  ... | tailP' , tailS = (there n eq tailP') , (there n eq tailS)



  -- If a behavior σ satisfies a stable predicate S at a given index i, and
  -- satisfies Q at a given k ≥ i then  σ satisfies (Q ∩ S) at k
  stableAux : ∀ {st} {ℓ₃ ℓ₄} {Q : Pred State ℓ₃} {S : Pred State ℓ₄}
                {i k : ℕ} {σ : Behavior st}
                → Stable StMachine S
                → σ satisfies S at i
                → i ≤ k
                → σ satisfies Q at k
                → σ satisfies (Q ∩ S) at k
  stableAux stable (here sS) i<k (here qS)
    = here (qS , sS)
  stableAux {σ = σ} stable (here sS) i<k (there {e} {enEv} n eq satQ')
    = there n eq (stableAux stable (here (stable enEv sS)) z≤n satQ')
  stableAux stable (there n eq satS) i<k (there n₁ eq₁ satQ')
    with trans (sym eq₁) eq
  ... | refl
      with stableAux stable satS (≤-pred i<k) satQ'
  ... | satT = there n₁ eq₁ satT


  -- Let A be a concurrent system. EventSet is a subset of events of A.
  -- The EventSet evSet is enabled in a state st if:
  --    ∃[ e ∈ evSet ] enabled e st (see definition of enabledSet)

  -- A behavior σ satisfies weak fairness for evSet if given that
  -- evSet is continuously enabled then it will eventually occurs
  postulate
    weak-fairness : ∀ {st}
                    → (evSet : EventSet)
                    → weakFairness sys evSet
                    → (σ : Behavior st)
                    →  Σ[ n ∈ ℕ ]
                     ( AllSt σ upTo n sat (enabledSet StMachine evSet)
                       → case tail (proj₂ (drop n σ)) of
                         λ { (inj₁ (e , enEv , t)) → evSet e
                           ; (inj₂ ¬enEv) → ⊥ } )

  -- Question : The weak fairness assumption could be a function such that if in
  -- all states up to n the evSet is enabled and the event in the tail after n
  -- transitions is on the evSet (without giving the contradiction but
  -- proving the contradiction in the soundness proof):

  -- AllUpTo (enabledSet StMachine evSet) n σ
  -- → tail (proj₂ (drop n σ)) ≡ inj₁ (e , enEv , t)
  --   → evSet e

  {- weak-fairness : ∀ {st}
                    → (evSet : EventSet)
                    → weakFairness sys evSet
                    → (σ : Behavior st)
                    →  Σ[ n ∈ ℕ ]
                     ( AllSt σ upTo n sat (enabledSet StMachine evSet)
                       → case tail (proj₂ (drop n σ)) of
                         λ { (inj₁ (e , enEv , t))
                              → Σ[ e₁ ∈ Event ] (e₁ ≡ e × evSet e₁)
                           ; (inj₂ ¬enEv)
                              → ¬ (Σ[ e ∈ Event ] evSet e) } )  -}



  -- For all n, given the constraints of the viaEvSet rule of LeadsTo, we know
  -- that either we reach Q at some point or in all states up to that n the evSet
  -- will be enabled
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
                 ⊎ AllSt σ upTo n sat (enabledSet StMachine evSet ∩ P)
  soundness-WF {P = P} rS evSet σ zero ps c₁ c₂ c₃
    with tail σ
  ... | inj₁ tailσ = inj₂ (last ( c₃ rS ps , ps))
  ... | inj₂ ¬enEv = case c₃ rS ps of
                     λ { (ev , _ , enEv) → ⊥-elim (¬enEv (ev , enEv)) }

  soundness-WF {P = P} rS evSet σ (suc n) ps c₁ c₂ c₃
    with tail σ    | inspect tail σ
  ... | inj₂ ¬enEv | _ =  case c₃ rS ps of
                          λ { (ev , _ , enEv) → ⊥-elim (¬enEv (ev , enEv)) }
  ... | inj₁ (ev , enEv , t) | Reveal[ t≡i₁ ]
      with ev ∈Set? evSet
  ...   | yes ∈evSet
          = case c₁ ev ∈evSet of
            λ { (hoare p→q)
                → inj₁ (1 , z≤n , (there 0 t≡i₁ (here (p→q ps enEv))))
              }
  ...   | no ¬∈evSet
        with c₂ ev ¬∈evSet
  ...     | hoare p∨q
          with p∨q ps enEv
  ...       | inj₂ qActionSt
              = inj₁ (1 , z≤n , (there 0 t≡i₁ (here qActionSt)))
  ...       | inj₁ pActionSt
            with soundness-WF (step rS enEv) evSet t
                               n pActionSt c₁ c₂ c₃
  ...         | inj₁ (j , 0<j , anyQT)
                = inj₁ (suc j , z≤n , there j t≡i₁ anyQT)
  ...         | inj₂ allT = inj₂ (( c₃ rS ps , ps) ∷ t≡i₁ ∣ allT)




  -- If all states in a behavior σ up to an index n satisfy (P ∩ Q), then
  -- all states in σ up to n satisfy P and all states in σ up to n satisfy Q
  ∀P∩Q⇒∀P∩∀Q : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄}
                → (n : ℕ)
                → (σ : Behavior st)
                → AllSt σ upTo n sat (P ∩ Q)
                → AllSt σ upTo n sat P × AllSt σ upTo n sat Q
  ∀P∩Q⇒∀P∩∀Q zero σ (last (p , q)) = (last p) , (last q)
  ∀P∩Q⇒∀P∩∀Q (suc n) σ ((ps , qs) ∷ eq ∣ allPQ)
    with tail σ | eq
  ... | inj₁ (ev , enEv , t) | refl
      with ∀P∩Q⇒∀P∩∀Q n t allPQ
  ...   | allP , allQ = (ps ∷ eq ∣ allP) , (qs ∷ eq ∣ allQ)


  -- If all states up to an index n in a behavior σ satisfy P, the state at the
  -- nᵗʰ state of σ satisfy P
  ∀Pn⇒PdropN : ∀ {st} {ℓ₃} {P : Pred State ℓ₃} (n : ℕ)
                → (σ : Behavior st)
                → AllSt σ upTo n sat P
                → P (proj₁ (drop n σ))
  ∀Pn⇒PdropN zero σ (last ps) = ps
  ∀Pn⇒PdropN (suc n) σ (ps ∷ t≡i₁ ∣ allP)
    with tail σ          | t≡i₁
  ... | inj₁ (_ , _ , t) | refl = ∀Pn⇒PdropN n t allP


  -- If the nᵗʰ state of σ satisfy P at 1 then σ satisfy Q at (suc n)
  dropNσsat⇒σsat : ∀ {st} {ℓ₄} {Q : Pred State ℓ₄}
                   → (n : ℕ)
                   → (σ : Behavior st)
                   → proj₂ (drop n σ) satisfies Q at 1
                   → σ satisfies Q at (suc n)
  dropNσsat⇒σsat zero    σ satQ = satQ
  dropNσsat⇒σsat (suc n) σ satQ
    with tail σ | inspect tail σ
  ... | inj₂ ¬ev | _ = case satQ of
                       λ { (there {e} {enEv} 0 t≡inj₁ x)
                                  → ⊥-elim (¬ev (e , enEv)) }
  ... | inj₁ (e , enEv , t) | Reveal[ eq ]
      with dropNσsat⇒σsat n t satQ
  ...   | anyQ = there (suc n) eq anyQ


  -- If a behavior σ satisfy that it exists a w such that F w at index i then
  -- it exists a w such that σ satisfy Fw at index i
  σ⊢Fw : ∀ {st} {F : Z → Pred State 0ℓ} {i : ℕ} {σ : Behavior st}
         → σ satisfies [∃ w ∶ F w ] at i
         → Σ[ w ∈ ℕ ] σ satisfies F w at i
  σ⊢Fw (here (w , fw)) = w , (here fw)
  σ⊢Fw (there n eq satF)
    with σ⊢Fw satF
  ... | w , fw = w , (there n eq fw)


  -- If a behavior σ satisfy that it exists a w₁ such that w₁ < w and F w₁
  -- at an index i then it exists a w₁ such that w₁ < w and
  -- σ satisfy F w₁ at index i
  σ⊢Fw< : ∀ {st} {F : Z → Pred State 0ℓ} {j w : ℕ} {σ : Behavior st}
          → σ satisfies [∃ w₁ ⇒ _< w ∶ F w₁ ] at j
          → Σ[ w₁ ∈ ℕ ] w₁ < w × σ satisfies F w₁ at j
  σ⊢Fw< (here (w₁ , w₁<w , fw₁)) = w₁ , w₁<w , (here fw₁)
  σ⊢Fw< (there n x satF)
    with σ⊢Fw< satF
  ... | w , x<w , fw = w , x<w , (there n x fw)




  -- The following definitions are mutual because the soundness proof use the
  -- lemma wfr→Q in the viaWFR rule to prove that given the viaWFR rule we reach
  -- a state that satisfies Q, and the wfr→Q lemma uses the soundness proof to
  -- prove that progress is made in the well founded ranking, which means that
  -- either we get to a state that satisfies Q or we reach a state where exists
  -- a w₁ such that w₁ < w and F w₁. This implies that or we reach Q or w₁ will
  -- become 0 and Q must hold.
  mutual

    wfr→Q : ∀ {w₁ w₂ i : ℕ} {st ℓ₄} {F : Z → Pred State 0ℓ} {Q : Pred State ℓ₄}
               → w₁ < w₂
               → Reachable {sm = StMachine} st
               → (σ : Behavior st)
               → σ satisfies F w₁ at i
               → (∀ (w : Z) → F w l-t (Q ∪ [∃ x ⇒ _< w ∶ F x ]))
               →  Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
    wfr→Q {zero}   {suc w₂} w₁<w₂ rS σ satF fw→q∪f
      with soundness2 rS σ satF (fw→q∪f 0)
    ... | n , i<n , anyQ∨⊥
        with trans2 anyQ∨⊥
    ...   | inj₁ anyQ = n , i<n , anyQ
    ...   | inj₂ imp
          with witness rS imp
    ...     | ()
    wfr→Q {suc w₁} {suc w₂} (s≤s w₁<w₂) rS σ satF fw→q∪f
      with soundness2 rS σ satF (fw→q∪f (suc w₁))
    ... | n , i<n , anyQ∨F
        with trans2 anyQ∨F
    ...   | inj₁ satQ = n , i<n , satQ
    ...   | inj₂ satw
          with σ⊢Fw< satw
    ...     | w , w<sw₁ , satw<
            with wfr→Q {w₂ = w₂} (≤-trans w<sw₁ w₁<w₂) rS σ satw< fw→q∪f
    ...       | j , n<j , anyQ = j , ≤-trans i<n n<j , anyQ



    soundness2 : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
                → Reachable {sm = StMachine} st
                → (σ : Behavior st)
                → σ satisfies P at i
                → P l-t Q
                → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
    soundness2 {st} {P = P} rS σ (here ps) rule@(viaEvSet evSet wf c₁ c₂ c₃)
      with weak-fairness evSet wf σ
    ... | n , wfa
        with soundness-WF rS evSet σ n ps c₁ c₂ c₃
    ...   | inj₁ satQ   = satQ
    ...   | inj₂ allE∧P
          with ∀P∩Q⇒∀P∩∀Q n σ allE∧P
    ...     | allE , allP
            with wfa allE
    ...       | v
              with tail (proj₂ (drop n σ)) | inspect tail (proj₂ (drop n σ))
    ...         | inj₂ ¬enEv | _ = ⊥-elim v
    ...         | inj₁ (e₁ , enEv₁ , t) | Reveal[ t≡i₁ ]
                  = case c₁ e₁ v of
                    λ { (hoare p→q)
                        → let pSt = ∀Pn⇒PdropN n σ allP
                              q⊢1 = there 0 t≡i₁ (here (p→q pSt enEv₁))
                           in (suc n) , z≤n , dropNσsat⇒σsat n σ q⊢1 }

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
    ...   | inj₁ anyQ = n , z≤n , anyQ
    ...   | inj₂ anyR
          with soundness2 rS σ anyR x₃
    ...     | j , n≤j , anyQ  = j , ≤-trans 0<n n≤j , anyQ

    soundness2 rS σ (here ps) rule@(viaDisj x x₂ x₃)
      with x ps
    ... | inj₁ p₁S = soundness2 rS σ (here p₁S) x₂
    ... | inj₂ p₂S = soundness2 rS σ (here p₂S) x₃

    soundness2 rS σ (here ps) rule@(viaUseInv inv x₂)
      with soundness2 rS σ (here (ps , inv rS)) x₂
    ... | n , 0≤n , anyR⇒Q
        with useInv inv rS anyR⇒Q
    ... | anyQ = n , 0≤n , anyQ

    soundness2 rS σ (here ps) rule@(viaWFR F p→q∪f f→q∨f<)
      with soundness2 rS σ (here ps) p→q∪f
    ... | n , 0<n , q∪f
        with trans2 q∪f
    ...   | inj₁ anyQ = n , 0<n , anyQ
    ...   | inj₂ anyF
          with σ⊢Fw anyF
    ...     | w , fw
            with soundness2 rS σ fw (f→q∨f< w)
    ...       | j , n<j , anyQ∪F
              with trans2 anyQ∪F
    ...         | inj₁ anyQw  = j , z≤n , anyQw
    ...         | inj₂ anyFw
                with σ⊢Fw< anyFw
    ...           | w₁ , w₁<w , anyFw₁
                  with wfr→Q w₁<w rS σ anyFw₁ f→q∨f<
    ...             | k , j<k , anyQ = k , z≤n , anyQ

    soundness2 rS σ (here ps) rule@(viaStable x₂ p'→q stableS q'∧s→q)
      with soundness2 rS σ (here ps) x₂
    ... | n , 0<n , anyP'∧S
        with σ⊢P∧S⇒σ⊢P∧σ⊢S anyP'∧S
    ... | anyP' , anyS
          with soundness2 rS σ anyP' p'→q
    ...   | k , n<k , anyQ'
          with soundness2 rS σ (stableAux stableS anyS n<k anyQ') q'∧s→q
    ...     | j , k<j , anyQ = j , ≤-trans 0<n (≤-trans n<k k<j) , anyQ

    soundness2 rS σ (there {e} {enEv} {t} n eq x₁) x₂
        with soundness2 (step rS enEv) t x₁ x₂
    ... | j , j<i , tail⊢Q = suc j , s≤s j<i , (there j eq tail⊢Q)



  -- Soundness proof for all Behaviors that start in one initial state
  soundness : ∀ {st} {ℓ₃ ℓ₄} {P : Pred State ℓ₃} {Q : Pred State ℓ₄} {i : ℕ}
              → (initial StMachine st)
              → (σ : Behavior st)
              → σ satisfies P at i
              → P l-t Q
              → Σ[ j ∈ ℕ ] i ≤ j × σ satisfies Q at j
  soundness sᵢ σ σ⊢P p→q = soundness2 (init sᵢ) σ σ⊢P p→q

