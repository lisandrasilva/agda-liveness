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
open import Data.Fin hiding (_≟_; _<?_; _≤?_ ;_+_; pred; lift)
                     renaming (_<_ to _<F_; _≤_ to _≤F_)
open import Data.List
open import Data.List.Properties
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Bool hiding (_<_ ; _<?_; _≤_; _≤?_)


open import StateMachineModel
open import Stream


module DistributedSystem.Prototype
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
  (N : ℕ)
  (f : ℕ)
  (fta : N > 3 * f)
  (ClientRequest : Set ℓ₂)
  (Block : Set ℓ₃)
  (mkBlock : ClientRequest → Block) -- It must also receive currView, ...
  (Vote : Set ℓ₄)
  (QC : Set ℓ₅)
  where


  -- Client can make a request at any moment

  {- Node:
       if (iAmLeader)
         0 - block = mkblock (getPoolReq req)  // getPoolReq
         1 - broadcast (mkBlock req)           // broadcastB


         2 - vts = wait (n-f-1) votes          // wait
             --appendRT(block)
         3 - qc = mkQC (vts + vt)

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
  NodeID = Fin N
  HonestID = Fin (N ∸ f)
  Instruction = Fin 10

  DishonestID : NodeID → Set
  DishonestID nId = N ∸ f ≤ toℕ nId



  data Message : Set (ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    blockM   : Block → Message
    voteM    : Vote  → Message
    qcM      : QC    → Message


  record NodeState : Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    field
      currNodeView : ℕ
      msgBuffer    : List Message
      readMessages : ℕ

      currProposal : Block
      votesforQC   : List Vote

      control      : Instruction

      -- id           : Node
      --recordTree    : RecordTree
      -- previousRound : ℕ
      -- lockedRound   : ℕ
      -- clock        : ℕ
      -- timeout      : ℕ
  open NodeState


  record State : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    field
     -- I am not sure that we don't need the faulty Node States
     -- because we may need to express that we have at least (N ∸ f)
     -- nodes on the same view and it may be that the f nodes behave normally
     nodeStates    : Vec NodeState (N ∸ f)
     leaderPerView : Stream (Fin N)
     poolRequests  : List ClientRequest
     committedReq  : ℕ
  open State


  Honest? : Decidable ((_< N ∸ f) ∘ toℕ {N})
  Honest? x = toℕ x <? N ∸ f

  Dishonest? : Decidable ((N ∸ f ≤_) ∘ toℕ {N})
  Dishonest? x = N ∸ f ≤? toℕ x

  mkQC : NodeState → QC
  mkQC = {!!}

  validVote : State → HonestID → Message → Set

  Receiver = HonestID


  data HonestEvent (nId : HonestID) : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    getPoolReq   : ClientRequest → HonestEvent nId
    broadcastB   : Block → HonestEvent nId
    broadcastQC  : QC → HonestEvent nId
    wait         : HonestEvent nId
    receive      : Message → HonestEvent nId

    sendMsg      : Message → Receiver → HonestEvent nId
    commit       : HonestEvent nId
    moveNextView : HonestEvent nId


  data DSEvent : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newRequest     : ClientRequest → DSEvent -- A client add a request to the request pool
    honestEvent    : ∀ {nId} → HonestEvent nId → DSEvent
    dishonestEvent : Message → Receiver → DSEvent



  nodeSt : HonestID → State → NodeState
  nodeSt nId st = Vec.lookup (nodeStates st) nId


  -- Other option is to have a flag in the NodeState saying if it's leader or follower
  isLeader : State → HonestID → Set
  isLeader st nId = let nodeView  = currNodeView (nodeSt nId st)
                    in get (leaderPerView st) nodeView ≡ inject≤ nId (n∸m≤n f N)


  {- Instruction is an abstraction for the number of intructions available for the node -}
  nextInstruction : State → HonestID → Instruction
  nextInstruction st nId = control (Vec.lookup (nodeStates st) nId)


  data HonestEnabled (nId : HonestID) (st : State) : HonestEvent nId
       → Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    getReqEn    :  ∀ {req}
                   → isLeader st nId
                   → nextInstruction st nId ≡ 0F
                   → (comm< : committedReq st < length (poolRequests st))
                   → req ≡ lookup (poolRequests st) (fromℕ≤ comm<)
                   → HonestEnabled nId st (getPoolReq req)

    broadcatBEn :  isLeader st nId
                   → nextInstruction st nId ≡ 1F
                   → HonestEnabled nId st (broadcastB (currProposal (nodeSt nId st)))

    waitVotesEn : isLeader st nId
                  → nextInstruction st nId ≡ 2F
                  → length (votesforQC (nodeSt nId st)) < N ∸ f
                  → HonestEnabled nId st wait

    receiveVote : ∀ {m} {v : Vote}
                  → isLeader st nId
                  → nextInstruction st nId ≡ 3F
                  → (i : readMessages (nodeSt nId st) < length (msgBuffer (nodeSt nId st)))
                  → m ≡ lookup (msgBuffer (nodeSt nId st)) (fromℕ≤ i)
                  → validVote st nId m
                  → HonestEnabled nId st (receive m)

    broadcastQC : isLeader st nId
                  → nextInstruction st nId ≡ 4F
                  → length (votesforQC (nodeSt nId st)) ≡ N ∸ f
                  → HonestEnabled nId st (broadcastQC (mkQC (nodeSt nId st)))




  data Enabled : DSEvent → State → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newReqEn      : ∀ {st req}
                    → Enabled (newRequest req) st

    honestEvEn    : ∀ {st hId hEv}
                    → HonestEnabled hId st hEv
                    → Enabled (honestEvent hEv) st

    dishonestEvEn : ∀ {st dId msg hId}
                    → DishonestID dId
                    → Enabled (dishonestEvent msg hId) st



  Action : ∀ {preState} {event} → Enabled event preState → State
  Action {ps} {newRequest req} x =
    record ps { poolRequests = poolRequests ps ++ [ req ]}

  Action {ps} {honestEvent {nId} (getPoolReq req)} x
    = let updateNode = λ old → record old
                               { control = 1F
                               ; currProposal = mkBlock req --nodeID , currView
                               }
      in record ps { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action {ps} {honestEvent {nId} (broadcastB b)} x
    = let sendBlock = λ node → record node { msgBuffer = msgBuffer node ++ [ blockM b ] }
          sendToAll = Vec.map sendBlock (nodeStates ps)
          updateLeader = λ old → record old { control = 2F }
       in record ps
          { nodeStates = Vec.updateAt nId updateLeader sendToAll }

  Action {ps} {honestEvent (broadcastQC qc)} x = {!!}

  Action {ps} {honestEvent wait} x = {!!}
  Action {ps} {honestEvent (receive x₁)} x = {!!}
  Action {ps} {honestEvent (sendMsg x₁ to)} x = {!!}
  Action {ps} {honestEvent commit} x = {!!}
  Action {ps} {honestEvent moveNextView} x = {!!}

  Action {ps} {dishonestEvent dEv hId} x = {!!}


