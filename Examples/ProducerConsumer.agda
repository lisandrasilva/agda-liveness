open import Prelude
open import Data.Vec.Bounded renaming ([] to Vec≤[])
open import Data.Vec renaming ( _++_ to _v++_
                              ; [_]  to v[_]
                              ; head to headV
                              ; _∷ʳ_ to _v∷ʳ_
                              ; tail to vTail)
open import Data.List

open import StateMachineModel


module Examples.ProducerConsumer
  {ℓ : Level}
  (Message : Set ℓ) -- Message type
  (Size : ℕ) -- Size of the bounded buffer
  where

  record State : Set (lsuc ℓ) where
    field
     buffer    : Vec≤ Message Size -- The numSpaces ≅ Vec≤.length
     produced  : List Message
     consumed  : List Message
  open State



  data MyEvent : Set ℓ where
    produce : Message → MyEvent
    consume : Message → MyEvent

  suc-vec : ∀ st → 0 < Vec≤.length (buffer st)
                 → Vec≤.vec (buffer st) ≡ {!Vec Message!}


  data MyEnabled : MyEvent → State → Set ℓ where
    prodEnabled : ∀ {st : State} {msg}
                  → Vec≤.length (buffer st) < Size
                  → MyEnabled (produce msg) st
    consEnabled : ∀ {st : State} {msg}
                  → 0 < Vec≤.length (buffer st)
                  → msg ≡ headV {!!}
                  → MyEnabled (consume msg) st




  MyAction : ∀ {preState : State} {event : MyEvent}
             → MyEnabled event preState
             → State
  MyAction {preSt} {produce m} (prodEnabled x) =
    record preSt
      { buffer    = Vec≤.vec (buffer preSt) v∷ʳ m , x
      ; produced  = produced preSt ++ [ m ]
      }
  MyAction {preSt} {consume m} enabled =
    record preSt
      { buffer    = (vTail (Vec≤.vec {!!})) , {!!}
      ; produced  = consumed preSt ++ [ m ]
      }


  initialState : State
  initialState = record
                   { buffer    = Vec≤[]
                   ; produced  = []
                   ; consumed  = []
                   }


  MyStateMachine : StateMachine State MyEvent
  MyStateMachine = record
                     { initial = λ state → state ≡ initialState
                     ; enabled = MyEnabled
                     ; action  = MyAction
                     }


  MyEventSet : EventSet {Event = MyEvent}
  MyEventSet ev = ∀ {msg} → ev ≡ consume msg


  data MyWeakFairness : EventSet → Set ℓ where
    wf : MyWeakFairness MyEventSet


  MySystem : System State MyEvent
  MySystem = record
             { stateMachine = MyStateMachine
             ; weakFairness = MyWeakFairness
             }
