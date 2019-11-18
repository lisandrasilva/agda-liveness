open import Prelude
open import Data.Vec.Bounded renaming ([] to Vec≤[])
open import Data.Vec renaming (_++_ to _v++_ ; [_] to v[_] ; head to headV)
open import Data.List

open import StateMachineModel


module Examples.ProducerConsumer
  {ℓ : Level}
  (Message : Set ℓ) -- Message type
  (Size : ℕ) -- Size of the bounded buffer
  where

  record State : Set (lsuc ℓ) where
    field
     buffer    : Vec≤ Message Size
     numSpaces : ℕ
     produced  : List Message
     consumed  : List Message
  open State



  data MyEvent : Set ℓ where
    produce : Message → MyEvent
    consume : Message → MyEvent



  data MyEnabled : MyEvent → State → Set ℓ where
    prodEnabled : ∀ {st : State} {msg}
                  → 1 ≤ numSpaces st
                  → MyEnabled (produce msg) st
    consEnabled : ∀ {st : State} {msg}
                  → msg ≡ {! headV (Vec≤.vec (buffer ?))!}
                  → MyEnabled (consume msg) st




  MyAction : ∀ {preState : State} {event : MyEvent}
             → MyEnabled event preState
             → State
  MyAction {preSt} {produce m} enabled = record preSt
                                          { buffer    = {!insert buffer preSt!}
                                          ; numSpaces = numSpaces preSt ∸ 1
                                          ; produced  = produced preSt ++ [ m ]
                                          }
  MyAction {preSt} {consume m} enabled = record preSt
                                          { buffer    = {!tail buffer preSt!}
                                          ; numSpaces = numSpaces preSt + 1
                                          ; produced  = consumed preSt ++ [ m ]
                                          }


  initialState : State
  initialState = record
                   { buffer    = Vec≤[]
                   ; numSpaces = Size
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
