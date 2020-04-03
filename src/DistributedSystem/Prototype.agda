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
--open import Relation.Nullary.Negation using (contradiction ; contraposition)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Bool




open import StateMachineModel
open import Stream


module DistributedSystem.Prototype
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
  (N : ℕ)
  -- (f : ℕ)
  (RecordTree : Set ℓ₁)
  (ClientRequest : Set ℓ₂)
  (Block : Set ℓ₃)
  (Vote : Set ℓ₄)
  (QC : Set ℓ₅)
  where


  -- Client can make a request at any moment

  {- Node:
       if (iAmLeader)
         0 - wait (n-f) new-view messages
         1 - req = getPoolReq
         2 - broadcast (mkBlock req)


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
  record Request : Set ℓ₂ where
    constructor mkReq
    field
      req       : ClientRequest
      committed : Bool
  open Request


  record NodeState : Set (ℓ₁ ⊔ ℓ₂) where
    field
      -- id : Node
      currNodeView : ℕ
      recordTree : RecordTree
      --previousRound : ℕ
      --lockedRound : ℕ
      clock : ℕ
      timeout : ℕ
      control : Fin 10

      -- program Variables
      req : Request
  open NodeState


  record State : Set (ℓ₁ ⊔ ℓ₂) where
    field
     nodeStates : Vec NodeState N
     -- currView : ℕ
     leaderPerView : Stream (Fin N)
     poolRequests : List Request
  open State


  data Message : Set (ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newView :         Message
    block   : Block → Message
    vote    : Vote  → Message
    qc      : QC    → Message


  data DSEvent : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newRequest   : ClientRequest → DSEvent -- A client add a request to the request pool
    getPoolReq   : Fin N → DSEvent
    broadcast    : Fin N → Message → DSEvent
    wait         : Fin N → Message → DSEvent
    vote         : Fin N → Message → DSEvent
    receive      : Fin N → Message → DSEvent
    mkQC         : Fin N → DSEvent
    commit       : Fin N → ClientRequest → DSEvent --tirar request da pool
    moveNextView : Fin N → DSEvent
    actDishonest : Fin N → DSEvent -- Think about it later
      -- An ideia is to separate the events instantiated my nodeId and then the act dishonest is allways enabled


{-  data Enabled (st : State) : DSEvent → Set {!!} where
    mkReqEn      : ∀ {req : ClientRequest} → Enabled st (mkRequest req)
    getReqEn     : Enabled {!!} {!!}
    bcBlockEn    : Enabled {!!} {!!}
    waitVBlEn    : Enabled {!!} {!!}
    sendVoteBEn  : Enabled {!!} {!!}
    recVoteEn    : Enabled {!!} {!!}
    mkQCEn       : Enabled {!!} {!!}
    bcQCEn       : Enabled {!!} {!!}
    sendRespEn   : Enabled {!!} {!!}
    mvNextViewEn : Enabled {!!} {!!}
-}

  nodeState : Fin N → State → NodeState
  nodeState nId st = Vec.lookup (nodeStates st) nId

  -- Other option is to have a flag in the NodeState saying if it's leader or follower
  isLeader : State → Fin N → Set
  isLeader st nId = let nodeView  = currNodeView (nodeState nId st)
                    in get (leaderPerView st) nodeView ≡ nId


  {- Fin 10 is an abstraction for the number of intructions available for the node -}
  nextInstruction : State → Fin N → Fin 10
  nextInstruction st nId = control (Vec.lookup (nodeStates st) nId)


  Enabled : DSEvent → State → Set
  Enabled (newRequest req) st = ⊤
  Enabled (getPoolReq nId) st = isLeader st nId × nextInstruction st nId ≡ 1F
  Enabled (broadcast nId newView) st = {!!}
  Enabled (broadcast nId (block x)) st = {!!}
  Enabled (broadcast nId (vote x)) st = {!!}
  Enabled (broadcast nId (qc x)) st = {!!}
  Enabled (wait nId msg) st = {!!}
  Enabled (vote nId msg) st = {!!}
  Enabled (receive x x₁) st = {!!}
  Enabled (mkQC x) st = {!!}
  Enabled (commit x x₁) st = {!!}
  Enabled (moveNextView x) st = {!!}
  Enabled (actDishonest x) st = {!!}


  Action : ∀ {preState} {event} → Enabled event preState → State
  -- the new request event receives a new ClientRequest and adds the request to the list
  Action {ps} {newRequest req} x = let nReq = mkReq req false
                                   in record ps
                                      { poolRequests = nReq ∷ poolRequests ps }
  Action {ps} {getPoolReq nId} x = let req = any (λ r → not (committed r)) (poolRequests ps)
                                       nodeSt = nodeState nId ps
                                       newNodeSt = {!!}
                                    in record ps
                                       { poolRequests = {!Vec.updateAt!} }
  Action {ps} {broadcast x₁ x₂} x = {!!}
  Action {ps} {wait x₁ x₂} x = {!!}
  Action {ps} {vote x₁ x₂} x = {!!}
  Action {ps} {receive x₁ x₂} x = {!!}
  Action {ps} {mkQC x₁} x = {!!}
  Action {ps} {commit x₁ x₂} x = {!!}
  Action {ps} {moveNextView x₁} x = {!!}
  Action {ps} {actDishonest x₁} x = {!!}

