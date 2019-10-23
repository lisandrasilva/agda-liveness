open import Data.Nat hiding (_⊔_)
open import Relation.Binary.PropositionalEquality renaming ([_] to Reveal[_] )
open import Relation.Unary
open import Level renaming (suc to lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Sum
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Product using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)

module StateMachineModel where

  record StateMachine {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      initial : Pred State 0ℓ
      enabled : Event → State → Set
      action  : ∀ {pre} {e} → enabled e pre → State
  open StateMachine


  data Reachable {ℓ₁ ℓ₂} {s : Set ℓ₁} {e : Set ℓ₂} {sm : StateMachine s e} : s → Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    init : ∀ {sᵢ} → initial sm sᵢ → Reachable sᵢ
    step : ∀ {ps}{ev} → Reachable {sm = sm} ps → (enEv : enabled sm ev ps) → Reachable (action sm enEv)


  Invariant : ∀  {ℓ₁ ℓ₂ ℓ'} {s : Set ℓ₁} {e : Set ℓ₂} (sm : StateMachine s e) (P : Pred s ℓ') → Set (ℓ' ⊔ lsuc (ℓ₁ ⊔ ℓ₂))
  Invariant sm P = ∀ {sr} (rs : Reachable {sm = sm} sr) → P sr

  postulate
    lemma-Imp→Inv : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {s : Set ℓ₁} {e : Set ℓ₂} (sm : StateMachine s e) {P : Pred s ℓ₃} {Q : Pred s ℓ₄}
                  → P ⊆ Q → Invariant sm (λ s → P s → Q s)

  record System {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
    field
      stateMachine : StateMachine State Event
      weakFairness : (Event → Set) → Set
  open System

  EventSet : ∀ {ℓ} {Event : Set ℓ} → Set (lsuc ℓ)
  EventSet {ℓ} {Event} = Event → Set ℓ

  -- TODO : genericize event level

  enabledSet : ∀ {ℓ₁ ℓ₂} {State : Set ℓ₁}{Event : Set ℓ₂} → (StateMachine State Event) → EventSet {Event = Event} → State → Set ℓ₂
  enabledSet sm es s = ∃[ e ] enabled sm e s

  data MyEvent : Set where
    inc  : MyEvent
    inc2 : MyEvent


  data MyEnabled : MyEvent → ℕ → Set where
    tt : ∀ {e} {n} → MyEnabled e n


  data MyWeakFairness2 : (MyEvent → Set) where
    mwf1 : MyWeakFairness2 inc
    mwf2 : MyWeakFairness2 inc2

  data MyWeakFairness : (MyEvent → Set) → Set where
    w0 : MyWeakFairness (MyWeakFairness2)


  myStateMachine : StateMachine ℕ MyEvent
  myStateMachine = record { initial = 2 ≡_ ; enabled = MyEnabled ; action = λ { {pre} {inc}  x → suc pre
                                                                              ; {pre} {inc2} x → suc (suc pre)} }

  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = myStateMachine ; weakFairness = MyWeakFairness }

  myInvariant : Invariant myStateMachine (2 ≤_)
  myInvariant (init x) =  ≤-reflexive x
  myInvariant (step {ps} {inc} rs enEv) = ≤-step (myInvariant rs)
  myInvariant (step {ps} {inc2} rs enEv) = ≤-step (≤-step (myInvariant rs))


  module LeadsTo {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) (sys : System State Event) where

   data [_]_[_] {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (e : Event) (Q : Pred State ℓ₄) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
      hoare : (∀ {ps} → P ps → (enEv : enabled (stateMachine sys) e ps) → Q (action (stateMachine sys) enEv )) → [ P ] e [ Q ]

   Z : Set
   Z = ℕ

   -- argument for the user
   -- F : ∀ {ℓ} → Z → Pred State ℓ

   data _l-t_ {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (Q : Pred State ℓ₄): Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))  where
     viaEvSet  : (eventSet : EventSet)
               → (∀ {e} → eventSet e → [ P ] e [ Q ])
               → (∀ {e} → ¬ (eventSet e) → [ P ] e [ P ∪ Q ])
               → Invariant (stateMachine sys) (λ s → ¬ (P s) ⊎ enabledSet (stateMachine sys) eventSet s)
               → P l-t Q
     viaInv    : Invariant (stateMachine sys) (λ s → P s → Q s)
               → P l-t Q
     viaTrans  : ∀ {R : Pred State ℓ₄}
               → P l-t R
               → R l-t Q
               → P l-t Q
     viaTrans2 : ∀ {R : Pred State ℓ₄}
               → P l-t (Q ∪ R)
               → R l-t Q
               → P l-t Q
     viaDisj   : ∀ {P₁ P₂ : Pred State ℓ₃}
               -- P = P₁ ∪ P₂ (from the paper)
               → P ⊆ (P₁ ∪ P₂)
               → P₁ l-t Q
               → P₂ l-t Q
               → P  l-t Q
     viaUseInv : ∀ {R : Pred State ℓ₄}
               → Invariant (stateMachine sys) R
               → (P ∩ R) l-t (λ s → R s → Q s)
               → P l-t Q
     viaWFR    : ∀ (F : Z → Pred State 0ℓ)
               → P l-t (Q ∪ λ s → ∃[ x ] F x s)
               → (∀ (w : Z) → F w l-t (Q ∪ (λ s → ∃[ x ] (x < w × F x s))))
               → P l-t Q


  open LeadsTo ℕ MyEvent mySystem

  myEventSet : EventSet {Event = MyEvent}
  myEventSet inc  = ⊤
  myEventSet inc2 = ⊤

  -- A state equals to n leads to a state equals to (1 + n) or equals to (2 + n)
  progressDumb : ∀ {n : ℕ} → (n ≡_) l-t ((1 + n ≡_) ∪ (2 + n ≡_))
  progressDumb = viaEvSet myEventSet
                           ( λ { {inc}  s → hoare λ { refl enEv → inj₁ refl}
                               ; {inc2} s → hoare λ { refl enEv → inj₂ refl} } )
                           ( λ { {inc}  s → ⊥-elim (s tt)
                               ; {inc2} s → ⊥-elim (s tt)} )
                           λ rs → inj₂ (inc , tt)

  n<m+n : ∀ {n m} → 0 < m → n < m + n
  n<m+n {zero}  {suc m} x = s≤s z≤n
  n<m+n {suc n} {suc m} x = s≤s (m≤n+m (suc n) m)

  progress-< : ∀ n → (n ≡_) l-t (n <_)
  progress-< n = viaTrans progressDumb (viaInv (λ { rs (inj₁ refl) → s≤s ≤-refl
                                                  ; rs (inj₂ refl) → s≤s (m≤n+m n 1)}))

  {- A predicate on states, parameterized by m (target).  The d parameter is the
     "distance" from the target m from state s.

     QUESTION : We are generalizing Z to be of a given type, however in myWFR
     we are using it knowing that is ℕ because we apply _≡_ and _+_
  -}
  myWFR : ∀ {m} → ℕ → Z → Set
  myWFR {m} d s = m ≡ s + d

  xx : ∀ m s → ¬ m ≤ s → m ≡ s + (m ∸ s)
  xx m s s<m with s ≤? m
  ...| yes s≤m = trans (sym (m∸n+n≡m {m} {s} s≤m)) (+-comm (m ∸ s) s)
  ...| no  m<s = ⊥-elim ( s<m ( ≤-pred (≤-step (≰⇒> m<s))))


  -- Or a State s is ≤ that a state m or there is a distance between m and s
  xx0 : ∀ {m} → (s : Z) → (_≤_ m ∪ (λ s₁ → ∃-syntax (λ x → myWFR {m} x s₁))) s
  xx0 {m} s with m ≤? s
  ...| yes yy  = inj₁ yy
  ...| no  s<m = inj₂ (m ∸ s , xx m s s<m)

  --
  progress0 : ∀ {n m} → (n ≡_) l-t ((m ≤_) ∪ (λ s → ∃[ x ] myWFR {m} x s))
  progress0 {n} {m} = viaEvSet myEventSet
                        (λ { {inc}  s → hoare λ {ps} x enEv → (xx0 {m} (suc ps))
                           ; {inc2} s → hoare λ {ps} x enEv → xx0 {m} (suc (suc ps))
                           })
                        (λ { {inc}  s → ⊥-elim (s tt)
                           ; {inc2} s → ⊥-elim (s tt)})
                         λ { {sr} rs → inj₂ (inc , tt)}

  progress1 : ∀ {m} → myWFR {m} 0 l-t (m ≤_)
  progress1 {m} = viaInv (lemma-Imp→Inv (stateMachine mySystem)
                                        λ {x₁} x → ≤-reflexive (trans x (+-comm x₁ 0)))

  progress1' : ∀ {m} → myWFR {m} 0 l-t ((m ≤_) ∪ (λ s → ∃[ x ] (x < 0 × myWFR {m} x s)))
  progress1' {m} = viaTrans {R = m ≤_}
                            (progress1 {m})
                            (viaInv (lemma-Imp→Inv (stateMachine mySystem)
                                                   {Q = (m ≤_) ∪ (λ s → ∃[ x ] (x < 0 × myWFR {m} x s))}
                                                   λ x → inj₁ x))

  xx2a : ∀ {m} → [ myWFR {m} 1 ] inc [ _≤_ m ∪ myWFR {m} 0 ]
  xx2a {m} = hoare λ {ps} x _ → inj₁ (≤-reflexive (trans x (+-comm ps 1)))

  xx2b : ∀ {m} → [ myWFR {m} 1 ] inc2 [ _≤_ m ∪ myWFR {m} 0 ]
  xx2b {m} = hoare λ {ps} → λ x _ → inj₁ (≤-step (≤-reflexive (trans x (+-comm ps 1))))

  progress2 : ∀ {m} → myWFR {m} 1 l-t ((m ≤_) ∪ (myWFR {m} 0))
  progress2 {m} = viaEvSet myEventSet (λ { {inc}  ⊤ → xx2a {m}
                                         ; {inc2} ⊤ → xx2b {m}
                                         }
                                      )
                                      (λ { {inc}  s → ⊥-elim (s tt)
                                         ; {inc2} s → ⊥-elim (s tt)
                                         }
                                      )
                                      λ {sr} rs → inj₂ (inc , tt)

  progress2' : ∀ {m} → myWFR {m} 1 l-t ((m ≤_) ∪ (λ s → ∃[ x ] (x < 1 × myWFR {m} x s)))
  progress2' {m} with progress2 {m}
  ...| xx = viaTrans {R = λ x → m ≤ x ⊎ m ≡ x + 0}
                     xx
                     (viaInv (lemma-Imp→Inv (stateMachine mySystem)
                                            {P = λ x → m ≤ x ⊎ m ≡ x + 0}
                                            {Q = ((m ≤_) ∪ (λ s → ∃[ x ] (x < 1 × myWFR {m} x s)))}
                                            (λ {x₁} → λ { (inj₁ x) → inj₁ x
                                                        ; (inj₂ x) → inj₂ (0 , (s≤s z≤n) , x)
                                                        })))

  xx3a : ∀ {m d} → [ myWFR {m} (suc (suc d)) ] inc  [ myWFR {m} (suc d) ∪ myWFR {m} d ]
  xx3a {m} {d} = hoare (λ {ps} x _ → inj₁ (trans x ((+-suc ps (suc d)))))

  xx3b : ∀ {m d} → [ myWFR {m} (suc (suc d)) ] inc2 [ myWFR {m} (suc d) ∪ myWFR {m} d ]
  xx3b {m} {d} = hoare λ {ps} x _ → inj₂ (trans x (trans (+-suc ps (suc d))
                                                         (cong suc (+-suc ps d))))

  progress3 : ∀ {m d} → myWFR {m} (suc (suc d)) l-t ((myWFR {m} (suc d)) ∪ (myWFR {m} d))
  progress3 {m} {d} = viaEvSet myEventSet ( λ { {inc}  ⊤ → xx3a {m} {d}
                                              ; {inc2} ⊤ → xx3b {m} {d}
                                              }
                                          )
                                          (λ { {inc}  s → ⊥-elim (s tt)
                                             ; {inc2} s → ⊥-elim (s tt)
                                             }
                                          )
                                          λ { {sr} rs → inj₂ (inc , tt) }

  progress3' : ∀ {m d} → myWFR {m} (suc (suc d)) l-t ((m ≤_) ∪ (λ s → ∃[ x ] (x < (suc (suc d)) × myWFR {m} x s)))
  progress3' {m} {d} with progress3 {m} {d}
  ...| xx = viaTrans {R = (λ x → m ≡ x + suc d ⊎ m ≡ x + d)}
                     xx
                     (viaInv (lemma-Imp→Inv (stateMachine mySystem)
                                            {λ x → m ≡ x + suc d ⊎ m ≡ x + d}
                                            {(λ x → m ≤ x ⊎ Σ ℕ (λ x₁ → Σ (suc x₁ ≤ suc (suc d)) (λ x₂ → m ≡ x + x₁)))}
                                            λ {x₃} →  λ { (inj₁ xx3) → inj₂ (suc d , (≤-reflexive refl) , xx3 )
                                                        ; (inj₂ xx3) → inj₂ (d , ((s≤s (n≤1+n d)) , xx3))
                                                        }))

  progress4 : ∀ {m d} → myWFR {m} d l-t ((m ≤_) ∪ (λ s → ∃[ x ] (x < d × myWFR {m} x s)))
  progress4 {m} {0}           = progress1' {m}
  progress4 {m} {suc 0}       = progress2' {m}
  progress4 {m} {suc (suc d)} = progress3' {m} {d}

  -- A state equals to n leads to a state greater or equal than m 
  progress5 : ∀ {n m : ℕ} → (n ≡_) l-t (m ≤_)
  progress5 {n} {m} = viaWFR (myWFR {m})
                             (progress0 {n} {m})
                             λ w → progress4 {m} {w}

