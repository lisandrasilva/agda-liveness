open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Level renaming (suc to lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties

module StateMachineModel where


  record StateMachine {ℓ} (State Event : Set ℓ) : Set (lsuc ℓ) where
    field
      initial : Pred {ℓ} State 0ℓ
      enabled : Event → State → Set
      action  : ∀ {pre} {e} → enabled e pre → State
  open StateMachine

{-
  data Invariant {ℓ} {s} {e} (sm : StateMachine {ℓ} s e) (P : Pred s 0ℓ) : Set (lsuc ℓ) where
     init : initial sm ⊆ P → Invariant sm P
     step : ∀ {pre}{ev} (enEv : enabled sm ev pre) → P pre → P (action sm enEv) → Invariant sm P
-}
  data Reachable {ℓ} {s} {e} {sm : StateMachine  {ℓ} s e} : s → Set (lsuc ℓ) where
    init : ∀ {sᵢ} → initial sm sᵢ → Reachable sᵢ
    step : ∀ {ps}{ev} → Reachable {ℓ} {sm = sm} ps → (enEv : enabled sm ev ps) → Reachable (action sm enEv)


  Invariant : ∀ {ℓ} {s} {e} (sm : StateMachine {ℓ} s e) (P : Pred s 0ℓ) → Set (lsuc ℓ)
  Invariant {ℓ} {s} {e} sm P = ∀ (sr : s) (rs : Reachable {sm = sm} sr) → P sr



  record System {ℓ} (State Event : Set ℓ) : Set (lsuc ℓ) where
    field
      stateMachine : StateMachine State Event
      weakFairness : (Event → Set) → Set


  data MyEvent : Set where
    inc : MyEvent
    inc2 : MyEvent


  data MyEnabled : MyEvent → ℕ → Set where
    tt : ∀ {e} {n} → MyEnabled e n


  data MyWeakFairness2 : (MyEvent → Set) where
    mwf1 : MyWeakFairness2 inc
    mwf2 : MyWeakFairness2 inc2

  data MyWeakFairness : (MyEvent → Set) → Set where
    w0 : MyWeakFairness (MyWeakFairness2)


  myStateMachine : StateMachine ℕ MyEvent
  myStateMachine = record { initial = 1 ≡_ ; enabled = MyEnabled ; action = λ {x} _ → suc x }


  mySystem : System ℕ MyEvent
  mySystem = record { stateMachine = myStateMachine ; weakFairness = MyWeakFairness }

  module _ {ℓ} (State Event : Set ℓ) (sys : System State Event) where


   data _l-t_ (P Q : Pred {ℓ} State 0ℓ): Set (lsuc ℓ)  where
     eventSet : ∀ {eventSet : Event → Set} →  {!!} --∀ {} {!P → Q → ?!} --(P → Q) → P l-t Q




