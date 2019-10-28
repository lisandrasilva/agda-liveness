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



  module LeadsTo {ℓ₁ ℓ₂} (State : Set ℓ₁) (Event : Set ℓ₂) (sys : System State Event) where

   data [_]_[_] {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (e : Event) (Q : Pred State ℓ₄) : Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
      hoare : (∀ {ps} → P ps → (enEv : enabled (stateMachine sys) e ps) → Q (action (stateMachine sys) enEv )) → [ P ] e [ Q ]

   Z : Set
   Z = ℕ

   -- argument for the user
   -- F : ∀ {ℓ} → Z → Pred State ℓ

   data _l-t_ {ℓ₃ ℓ₄} (P : Pred State ℓ₃) (Q : Pred State ℓ₄): Set (lsuc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄))  where
     viaEvSet  : (eventSet : EventSet)
               → (∀ {e} → eventSet e → [ P ] e [ Q ]) -- 'e' shouldn't be in the weakfairness??
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
