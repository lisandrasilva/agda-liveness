{-
  Copyright 2019 Lisandra Silva

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-}

open import Prelude
open import Data.Bool renaming (_≟_ to _B≟_)
open import Data.Fin renaming (_≟_ to _F≟_)
open import Agda.Builtin.Sigma
open import Relation.Nullary.Negation using (contradiction)


open import StateMachineModel

-- TODO : Add documentation about the model according to the paper
module Examples.Peterson where

  record State : Set where
    field
      thinking₁ : Bool
      thinking₂ : Bool
      turn      : Fin 2
      control₁  : Fin 4
      control₂  : Fin 4
  open State

  data MyEvent : Set where
    es₁ : MyEvent
    es₂ : MyEvent
    es₃ : MyEvent
    es₄ : MyEvent
    er₁ : MyEvent
    er₂ : MyEvent
    er₃ : MyEvent
    er₄ : MyEvent

  {-
  data MyEnabled (st : State) : MyEvent → Set where
    ees₁ : control₁ st ≡ 1 → MyEnabled st es₁
    ees₂ : control₁ st ≡ 2 → MyEnabled st es₂
    ees₃ : control₁ st ≡ 3 → MyEnabled st es₃
    ees₄ : control₁ st ≡ 4 → MyEnabled st es₄
  -}

  MyEnabled : MyEvent → State → Set
  MyEnabled es₁ st = control₁ st ≡ 0F
  MyEnabled es₂ st = control₁ st ≡ 1F
  MyEnabled es₃ st = control₁ st ≡ 2F × (thinking₂ st ≡ true ⊎ turn st ≡ 0F)
  MyEnabled es₄ st = control₁ st ≡ 3F
  MyEnabled er₁ st = control₂ st ≡ 0F
  MyEnabled er₂ st = control₂ st ≡ 1F
  MyEnabled er₃ st = control₂ st ≡ 2F × (thinking₁ st ≡ true ⊎ turn st ≡ 0F)
  MyEnabled er₄ st = control₂ st ≡ 3F



  MyAction : ∀ {preState} {event} → MyEnabled event preState → State
  MyAction {ps} {es₁} x = record
                            { thinking₁ = false
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 1F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₂} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = 1F
                            ; control₁  = 2F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₃} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 3F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {es₄} x = record
                            { thinking₁ = true
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = 0F
                            ; control₂  = control₂ ps
                            }
  MyAction {ps} {er₁} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = false
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 1F
                            }
  MyAction {ps} {er₂} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = 0F
                            ; control₁  = control₁ ps
                            ; control₂  = 2F
                            }
  MyAction {ps} {er₃} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = thinking₂ ps
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 3F
                            }
  MyAction {ps} {er₄} x = record
                            { thinking₁ = thinking₁ ps
                            ; thinking₂ = true
                            ; turn      = turn ps
                            ; control₁  = control₁ ps
                            ; control₂  = 0F
                            }

  initialState : State
  initialState = record
                   { thinking₁ = true
                   ; thinking₂ = true
                   ; turn      = 0F
                   ; control₁  = 0F
                   ; control₂  = 0F
                   }

  MyStateMachine : StateMachine State MyEvent
  MyStateMachine = record
                     { initial = λ state → state ≡ initialState
                     ; enabled = MyEnabled
                     ; action  = MyAction
                     }


  -- Each process has its own EventSet with its statements
  Proc1-EvSet : EventSet {Event = MyEvent}
  Proc1-EvSet ev = ev ≡ es₂ ⊎ ev ≡ es₃ ⊎ ev ≡ es₄

  Proc2-EvSet : EventSet {Event = MyEvent}
  Proc2-EvSet ev = ev ≡ er₂ ⊎ ev ≡ er₃ ⊎ ev ≡ er₄

  MyEventSet : EventSet {Event = MyEvent}
  MyEventSet ev = ⊤

  -- And both EventSets have weak-fairness
  data MyWeakFairness : EventSet → Set where
    wf-p1 : MyWeakFairness Proc1-EvSet
    wf-p2 : MyWeakFairness Proc2-EvSet
    wf-∀  : MyWeakFairness MyEventSet


  MySystem : System State MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }


   -----------------------------------------------------------------------------
   -- PROOFS
   -----------------------------------------------------------------------------

  open LeadsTo State MyEvent MySystem


  inv-c₁≡2⇒¬think₁ : Invariant
                       MyStateMachine
                       λ st → control₁ st ≡ 1F → thinking₁ st ≡ false


  inv-c₂≡2⇒¬think₂ : Invariant
                       MyStateMachine
                       λ st → control₂ st ≡ 1F → thinking₂ st ≡ false


  proc1-2-l-t-3 : (λ preSt → control₁ preSt ≡ 1F)
                  l-t
                  λ posSt →   control₁ posSt ≡ 2F
                            × thinking₁ posSt ≡ false
  proc1-2-l-t-3 =
    viaUseInv
      inv-c₁≡2⇒¬think₁
      ( viaEvSet
          Proc1-EvSet
          wf-p1
          ( λ { es₂ (inj₁ refl)
                    → hoare λ { (fst , snd) enEv x₁ → refl , snd enEv }
              ; es₃ (inj₂ (inj₁ refl))
                    → hoare λ { (refl , snd) (() , snd₁) x₁ }
              ; es₄ (inj₂ (inj₂ refl))
                    → hoare λ { (refl , snd) () x₁ }
              }
          )
          ( λ { es₁ x → hoare λ { () refl }
              ; es₂ x → ⊥-elim (x (inj₁ refl))
              ; es₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
              ; es₄ x → ⊥-elim (x (inj₂ (inj₂ refl)))
              ; er₁ x → hoare λ z enEv → inj₁ z
              ; er₂ x → hoare λ z enEv → inj₁ z
              ; er₃ x → hoare λ z enEv → inj₁ z
              ; er₄ x → hoare λ z enEv → inj₁ z
              }
          )
        λ {state} rs x → es₂ , inj₁ refl , fst x
      )


  P⊆P₁⊎P₂ : ∀ {ℓ} {A B : Set ℓ} (x : Fin 2)
            → A × B → A × B × x ≡ 0F ⊎ A × B × x ≡ 1F
  P⊆P₁⊎P₂ 0F (a , b) = inj₁ (a , b , refl)
  P⊆P₁⊎P₂ 1F (a , b) = inj₂ (a , b , refl)


  -- y4
  proc1-P₁-l-t-Q : ( λ preSt →  control₁ preSt ≡ 2F
                              × thinking₁ preSt ≡ false
                              × turn preSt ≡ 0F )
                   l-t
                   λ posSt → control₁ posSt ≡ 3F
  proc1-P₁-l-t-Q =
    viaEvSet
      Proc1-EvSet
      wf-p1
      ( λ { es₂ (inj₁ refl)        → hoare λ { () refl }
          ; es₃ (inj₂ (inj₁ refl)) → hoare λ _ _ → refl
          ; es₄ (inj₂ (inj₂ refl)) → hoare λ { () refl }
          }
      )
      ( λ { es₁ x → hoare λ { () refl }
          ; es₂ x → ⊥-elim (x (inj₁ refl))
          ; es₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
          ; es₄ x → ⊥-elim (x (inj₂ (inj₂ refl)))
          ; er₁ x → hoare (λ z enEv → inj₁ z)
          ; er₂ x → hoare (λ z enEv → inj₁ ( fst z , fst (snd z) , refl ) )
          ; er₃ x → hoare (λ z enEv → inj₁ z)
          ; er₄ x → hoare (λ z enEv → inj₁ z)
          }
      )
      λ {st} rs x → es₃ , (inj₂ (inj₁ refl)) , ((fst x) , (inj₂ (snd (snd x))))


  P⊆c₂≡r₁⊎c₂≢r₁ : ∀ {ℓ} {A : Set ℓ} (x : Fin 4)
                  → A
                  → A × x ≡ 0F ⊎ A × x ≢ 0F
  P⊆c₂≡r₁⊎c₂≢r₁ 0F a = inj₁ (a , refl)
  P⊆c₂≡r₁⊎c₂≢r₁ (suc x) a = inj₂ (a , (λ ()))


  P⊆c₂≡r₂⊎c₂≢r₂ : ∀ {ℓ} {A : Set ℓ} (x : Fin 4)
                  → A × x ≢ 0F
                  → A × x ≡ 1F ⊎ A × x ≢ 0F × x ≢ 1F
  P⊆c₂≡r₂⊎c₂≢r₂ 0F (a , x≢0) = ⊥-elim (x≢0 refl)
  P⊆c₂≡r₂⊎c₂≢r₂ 1F (a , x≢0) = inj₁ (a , refl)
  P⊆c₂≡r₂⊎c₂≢r₂ (suc (suc x)) (a , x≢0) = inj₂ (a , x≢0 , λ ())


  P⊆c₂≡r₃⊎c₂≡r₄ : ∀ {ℓ} {A : Set ℓ} (x : Fin 4)
                  → A × x ≢ 0F × x ≢ 1F
                  → A × x ≡ 2F ⊎ A × x ≡ 3F
  P⊆c₂≡r₃⊎c₂≡r₄ 0F (a , x≢0 , x≢1) = ⊥-elim (x≢0 refl)
  P⊆c₂≡r₃⊎c₂≡r₄ 1F (a , x≢0 , x≢1) = ⊥-elim (x≢1 refl)
  P⊆c₂≡r₃⊎c₂≡r₄ 2F (a , x≢0 , x≢1) = inj₁ (a , refl)
  P⊆c₂≡r₃⊎c₂≡r₄ 3F (a , x≢0 , x≢1) = inj₂ (a , refl)


  y2 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 0F)
       l-t
        λ posSt →   control₁ posSt ≡ 3F
                  ⊎ (( control₁ posSt ≡ 2F
                    × thinking₁ posSt ≡ false
                    × turn posSt ≡ 1F )
                    × control₂ posSt ≡ 1F )
  y2 =
    viaEvSet
      MyEventSet
      wf-∀
      ( λ { es₁ ⊤ → hoare λ { () refl }
          ; es₂ ⊤ → hoare λ { () refl }
          ; es₃ ⊤ → hoare λ _ _ → inj₁ refl -- control₁ posSt ≡ 3F
          ; es₄ ⊤ → hoare λ { () refl }
          ; er₁ ⊤ → hoare λ { (r , c₂≡0) refl → inj₂ (r , refl) }
          ; er₂ ⊤ → hoare λ { () refl }
          ; er₃ ⊤ → hoare λ { (fst , refl) () }
          ; er₄ ⊤ → hoare λ { () refl }
          }
      )
      ( λ e x → ⊥-elim (x tt) )
      λ rs x → er₁ , (tt , (snd x))



  y3 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 1F)
       l-t
        λ posSt →   control₁ posSt ≡ 2F
                  × thinking₁ posSt ≡ false
                  × turn posSt ≡ 0F
                  --× control₂ posSt ≡ 2F
  y3 =
    viaUseInv
      inv-c₂≡2⇒¬think₂
      ( viaEvSet
          Proc2-EvSet -- I think we can also prove with MyEventSet
          wf-p2
          ( λ { er₂ (inj₁ refl)
                    → hoare λ { ((x , _) , _) _ _ → fst x , fst (snd x) , refl }
              ; er₃ (inj₂ (inj₁ refl))
                    → hoare λ { () (refl , _) _ }
              ; er₄ (inj₂ (inj₂ refl)) → hoare λ { () refl x₁ }
              }
          )
          ( λ { es₁ x → hoare λ { () refl }
              ; es₂ x → hoare λ { () refl }
              ; es₃ x → hoare λ { ((_ , c₂≡2) , x) (_ , inj₁ refl)
                                                   → contradiction (x c₂≡2) λ ()
                                ; ((() , _) , _) (_ , inj₂ refl) }
              ; es₄ x → hoare λ { () refl }
              ; er₁ x → hoare λ { () refl }
              ; er₂ x → ⊥-elim (x (inj₁ refl))
              ; er₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
              ; er₄ x → ⊥-elim (x (inj₂ (inj₂ refl))) }
          )
          λ rs x → er₂ , (inj₁ refl) , (snd (fst x))
      )



  y5 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 2F)
       l-t
       (λ posSt → ( control₁ posSt ≡ 2F
                  × thinking₁ posSt ≡ false
                  × turn posSt ≡ 1F )
                  × control₂ posSt ≡ 3F)

  y6 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 3F)
       l-t
       (λ posSt → ( control₁ posSt ≡ 2F
                  × thinking₁ posSt ≡ false
                  × turn posSt ≡ 1F )
                  × control₂ posSt ≡ 0F)

  y7 :  (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 1F)
       l-t
        λ posSt → control₁ posSt ≡ 3F
  y7 =
    viaTrans
      y3
      proc1-P₁-l-t-Q


  y8 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 0F)
       l-t
        λ posSt → control₁ posSt ≡ 3F
  y8 =
    viaTrans2
      y2
      y7


  y9 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 3F)
        l-t
        λ posSt → control₁ posSt ≡ 3F
  y9 =
    viaTrans
      y6
      y8



  y10 : (λ preSt → ( control₁ preSt ≡ 2F
                  × thinking₁ preSt ≡ false
                  × turn preSt ≡ 1F )
                  × control₂ preSt ≡ 2F)
        l-t
        λ posSt → control₁ posSt ≡ 3F
  y10 =
    viaTrans
      y5
      y9


  proc1-P₂-l-t-Q : ( λ preSt →  control₁ preSt ≡ 2F
                              × thinking₁ preSt ≡ false
                              × turn preSt ≡ 1F )
                   l-t
                   λ posSt → control₁ posSt ≡ 3F
  proc1-P₂-l-t-Q =
    viaDisj
      ( λ {st} x → P⊆c₂≡r₁⊎c₂≢r₁ (control₂ st) x )
      y8
      ( viaDisj
          ( λ {st} x → P⊆c₂≡r₂⊎c₂≢r₂ (control₂ st) x )
          y7
          ( viaDisj
              ( λ {st} x → P⊆c₂≡r₃⊎c₂≡r₄ (control₂ st) x )
              y10
              y9
          )
      )



  proc1-3-l-t-4 : ( λ preSt →  control₁ preSt ≡ 2F
                             × thinking₁ preSt ≡ false )
                  l-t
                    λ posSt → control₁ posSt ≡ 3F
  proc1-3-l-t-4 =
    viaDisj
      (λ {st} x → P⊆P₁⊎P₂ (turn st) x )
      proc1-P₁-l-t-Q
      proc1-P₂-l-t-Q




  proc2-2-l-t-3 : (λ preSt → control₂ preSt ≡ 1F)
                  l-t
                  λ posSt →   control₂ posSt ≡ 2F
                            × thinking₂ posSt ≡ false
  proc2-2-l-t-3 =
    viaUseInv
      inv-c₂≡2⇒¬think₂
      ( viaEvSet
          Proc2-EvSet
          wf-p2
          ( λ { er₂ (inj₁ refl)
                    → hoare λ { (refl , snd) enEv x₁ → refl , snd refl }
              ; er₃ (inj₂ (inj₁ refl))
                    → hoare λ { (refl , snd₂) (() , snd₁) x₁ }
              ; er₄ (inj₂ (inj₂ refl))
                    → hoare λ { () refl x₁ }
              }
          )
          ( λ { es₁ x → hoare λ z enEv → inj₁ z
              ; es₂ x → hoare λ z enEv → inj₁ z
              ; es₃ x → hoare λ z enEv → inj₁ z
              ; es₄ x → hoare λ z enEv → inj₁ z
              ; er₁ x → hoare λ _ enEv → inj₁ (refl , (λ x → refl))
              ; er₂ x → ⊥-elim (x (inj₁ refl))
              ; er₃ x → ⊥-elim (x (inj₂ (inj₁ refl)))
              ; er₄ x → ⊥-elim (x (inj₂ (inj₂ refl)))
              }
          )
        λ {state} rs x → er₂ , inj₁ refl , fst x
      )


  proc2-3-l-t-4 : ( λ preSt →  control₂ preSt ≡ 2F
                             × thinking₂ preSt ≡ false )
                  l-t
                    λ posSt → control₂ posSt ≡ 3F
  proc2-3-l-t-4 = {!!}




  proc1-live : (λ preSt → control₁ preSt ≡ 1F) l-t (λ posSt → control₁ posSt ≡ 3F)
  proc1-live = viaTrans proc1-2-l-t-3 proc1-3-l-t-4


  proc2-live : (λ preSt → control₂ preSt ≡ 1F) l-t (λ posSt → control₂ posSt ≡ 3F)
  proc2-live = viaTrans proc2-2-l-t-3 proc2-3-l-t-4


  progress : (λ preSt → control₁ preSt ≡ 1F) l-t (λ posSt → control₁ posSt ≡ 3F)
           × (λ preSt → control₂ preSt ≡ 1F) l-t (λ posSt → control₂ posSt ≡ 3F)
  progress = proc1-live , proc2-live

