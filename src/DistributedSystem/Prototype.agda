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
open import Data.Fin hiding (_≟_; _<_; _+_; pred; _≤_; lift)
open import Data.List
open import Data.List.Properties
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Bool hiding (_<_)


open import StateMachineModel
open import Stream


module DistributedSystem.Prototype
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
  (N : ℕ)
  (f : ℕ)
  (fta : N > 3 * f)
  --(RecordTree : Set ℓ₁)
  (ClientRequest : Set ℓ₂)
  (Block : Set ℓ₃)
  (mkBlock : ClientRequest → Block) -- It must also receive currView, ...
  (Vote : Set ℓ₄)
  (QC : Set ℓ₅)
  where


  -- Client can make a request at any moment

  {- Node:
       if (iAmLeader)
         0 - block = mkblock (getPoolReq req)
         1 - broadcast (mkBlock req)


         3 - vts = wait (n-f-1) votes
             vt = mkVote
             appendRT(block)
         4 - qc = mkQC (vts + vt)
         5 - broadcastQC qc
             appendQC(QC)
         6 - sendClientResponse
       else
         1 - wait for valid proposal from current leader
         2 - vt = mkVote proposal
         3 - wait for valid QC
             appendRT(QC)

       10 - b


  -}

    {- Questions
    -- With this approach I have a notion of send and receive as having weak-fairness
    -- If I introduce time, I need to be sure that the timeout period is big enough
    -- so the messages can be delivered
    -}


  -----------------------------------------------------------------------------
  -- SPECIFICATION
  -----------------------------------------------------------------------------

  data Message : Set (ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    block   : Block → Message
    vote    : Vote  → Message
    qc      : QC    → Message


  record NodeState : Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    field
      currNodeView : ℕ
      currProposal : Block
      msgBuffer    : List Message
      readMessages : ℕ

      control      : Fin 10

      -- id           : Node
      --recordTree    : RecordTree
      -- previousRound : ℕ
      -- lockedRound   : ℕ
      -- clock        : ℕ
      -- timeout      : ℕ
  open NodeState


  record State : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    field
     nodeStates    : Vec NodeState N
     leaderPerView : Stream (Fin N)
     poolRequests  : List ClientRequest
     committedReq  : ℕ
  open State


  data DSEvent : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newRequest   : ClientRequest → DSEvent -- A client add a request to the request pool
    getPoolReq   : Fin N → ClientRequest → DSEvent
    broadcastB   : Fin N → Block → DSEvent
    broadcastQC  : Fin N → QC → DSEvent
    wait         : Fin N → Message → DSEvent
    vote         : Fin N → Message → DSEvent
    receive      : Fin N → Message → DSEvent
    mkQC         : Fin N → DSEvent
    commit       : Fin N → DSEvent
    moveNextView : Fin N → DSEvent
    -- actDishonest : Fin N → DSEvent -- Think about it later
      -- An ideia is to separate the events instantiated my nodeId and then the act dishonest is allways enabled



  nodeState : Fin N → State → NodeState
  nodeState nId st = Vec.lookup (nodeStates st) nId

  -- Other option is to have a flag in the NodeState saying if it's leader or follower
  isLeader : State → Fin N → Set
  isLeader st nId = let nodeView  = currNodeView (nodeState nId st)
                    in get (leaderPerView st) nodeView ≡ nId


  {- Fin 10 is an abstraction for the number of intructions available for the node -}
  nextInstruction : State → Fin N → Fin 10
  nextInstruction st nId = control (Vec.lookup (nodeStates st) nId)




  data Enabled1 : DSEvent → State → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newReqEn     : ∀ {st req}
                   → Enabled1 (newRequest req) st
    getReqEn     : ∀ {st nId req}
                   → isLeader st nId
                   → nextInstruction st nId ≡ 0F
                   → (comm< : committedReq st < length (poolRequests st))
                   → req ≡ lookup (poolRequests st) (fromℕ≤ comm<)
                   → Enabled1 (getPoolReq nId req) st
    bcBlockEn    : ∀ {st nId}
                   → isLeader st nId
                   → nextInstruction st nId ≡ 1F
                   → Enabled1 (broadcastB nId (currProposal (nodeState nId st))) st



  Action1 : ∀ {preState} {event} → Enabled1 event preState → State
  Action1 {ps} {newRequest req} x =
    record ps { poolRequests = poolRequests ps ++ [ req ]}

  Action1 {ps} {getPoolReq nId req} x =
    let updateNode = λ old → record old
                               { control = 1F
                               ; currProposal = mkBlock req --nodeID , currView
                               }
    in record ps
         { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action1 {ps} {broadcastB nId b} x =
    let sendBlock = λ node → record node { msgBuffer = msgBuffer node ++ [ block b ] }
        sendToAll = Vec.map sendBlock (nodeStates ps)
        updaTeLeader = λ old → record old { control = 2F }
     in record ps
          { nodeStates = Vec.updateAt nId updaTeLeader sendToAll }



  Enabled : DSEvent → State → Set
  Enabled (newRequest req) st = ⊤
  Enabled (getPoolReq nId req) st = isLeader st nId
                                × nextInstruction st nId ≡ 1F
                                × {!req ≡ ?!}
  Enabled (broadcastB nId b) st = {!!}
  Enabled (broadcastQC nId q) st = {!!}
  Enabled (wait nId msg) st = {!!}
  Enabled (vote nId msg) st = {!!}
  Enabled (receive x x₁) st = {!!}
  Enabled (mkQC x) st = {!!}
  Enabled (commit x) st = {!!}
  Enabled (moveNextView x) st = {!!}
  --Enabled (actDishonest x) st = {!!}


