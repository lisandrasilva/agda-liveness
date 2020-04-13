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
open import Data.Bool hiding (_<_ ; _<?_; _≤_; _≤?_; _≟_)


open import StateMachineModel
open import Stream


module DistributedSystem.Prototype
  {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level}
  (N : ℕ)
  (f : ℕ)
  (fta : N > 3 * f)
  (ClientRequest : Set ℓ₂)
  (Block : Set ℓ₃)
  (Vote : Set ℓ₄)
  (QC : Set ℓ₅)
  where


  -- Client can make a request at any moment

{-
    0 - Set node role
               LEADER                 ||           LEADER & FOLLOWER
    1 - block = getPoolReq
    2 - broadcast block
                                      ||    3 - receive block
                                      ||    4 - vote for block
    5 - while (#votes < N-f-1)
    6 -    reveive vote
    5 - broadcast QC
                                      ||    7 - receive QC
                                      ||    8 - check commit rule
                                      ||    9 - movenextview
-}


  -- QUESTION:
  -- To prove the liveness not only the sequence of honest leaders per view must be
  -- long enough but also the length of the requests must be greater than 3.
  -- If the sequence is smaller we don't have enough requests to ensure the commit rule

  -- A dishonest leader can deliberately left honest nodes behind, and these nodes
  -- won't move to the next view, unless they timeout. However, t if these nodes have
  -- moved for the next view for timeout, they will be missing a block and a qc
  -- in the RecordStore, how to fix this?
  --     1 - Whisper of proposed blocks and Qc's
  --     2 - Whisper only of QC's (if they have attached the proposed block)
  --     3 - Mechanism of asking records missing in the record store


  -----------------------------------------------------------------------------
  -- SPECIFICATION
  -----------------------------------------------------------------------------

  NodeID = Fin N
  HonestID = Fin (N ∸ f)
  Instruction = Fin 10

  Receiver = Fin N

  DishonestID : NodeID → Set
  DishonestID nId = N ∸ f ≤ toℕ nId



  data Message : Set (ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    blockM   : Block → Message
    voteM    : Vote  → Message
    qcM      : QC    → Message


  data Role : Set where
    leader   : Role
    follower : Role


  record NodeState : Set (ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    field
      nodeRole     : Role
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

  mkBlock : ClientRequest → NodeState → Block

  mkQC : NodeState → QC

  mkVote : NodeState → Vote

  validVote  : State → HonestID → Vote  → Set

  validBlock : State → HonestID → Block → Set

  validQC : State → HonestID → QC → Set


  data HonestEvent (nId : HonestID) : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    setNodeRole  : HonestEvent nId
    getPoolReq   : ClientRequest → HonestEvent nId
    broadcastB   : Block → HonestEvent nId
    broadcastQC  : QC → HonestEvent nId
    wait         : HonestEvent nId
    receive      : Message → HonestEvent nId
    sendVote     : Vote → Receiver → HonestEvent nId
    commit       : HonestEvent nId
    moveNextView : HonestEvent nId




  data DSEvent : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newRequest     : ClientRequest → DSEvent -- A client add a request to the request pool
    honestEvent    : ∀ {nId} → HonestEvent nId → DSEvent
    dishonestEvent : Message → HonestID → DSEvent -- dishonest nodes can send any msg to honest nodes



  nodeSt : HonestID → State → NodeState
  nodeSt nId st = Vec.lookup (nodeStates st) nId


  -- Other option is to have a flag in the NodeState saying if it's leader or follower
  isLeader : State → HonestID → Set
  isLeader st nId = nodeRole (nodeSt nId st) ≡ leader


  getLeader : State → HonestID → Fin N
  getLeader st nId = get (leaderPerView st) (currNodeView (nodeSt nId st))


  {- Instruction is an abstraction for the number of intructions available for the node -}
  nextInstruction : State → HonestID → Instruction
  nextInstruction st nId = control (nodeSt nId st)


  data HonestEnabled (nId : HonestID) (st : State) : HonestEvent nId
       → Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    setRoleEn      :  nextInstruction st nId ≡ 0F
                    → HonestEnabled nId st setNodeRole

    getReqEn       :  ∀ {req}
                    → isLeader st nId
                    → nextInstruction st nId ≡ 1F
                    → (comm< : committedReq st < length (poolRequests st))
                    -- Maybe it's better to have a function:
                    -- fetchNextReq : List ClientRequests → Maybe (Index , Request)
                    → req ≡ lookup (poolRequests st) (fromℕ≤ comm<)
                    → HonestEnabled nId st (getPoolReq req)

    broadcastBEn   :  isLeader st nId
                    → nextInstruction st nId ≡ 2F
                    → HonestEnabled nId st (broadcastB (currProposal (nodeSt nId st)))

    receiveBlockEn :  ∀ {b : Block}
                    → nextInstruction st nId ≡ 3F
                    → (i : readMessages (nodeSt nId st) < length (msgBuffer (nodeSt nId st)))
                    → blockM b ≡ lookup (msgBuffer (nodeSt nId st)) (fromℕ≤ i)
                    → validBlock st nId b
                    → HonestEnabled nId st (receive (blockM b))

    voteBlockEn    :  nextInstruction st nId ≡ 4F
                    → HonestEnabled nId st (sendVote
                                            (mkVote (nodeSt nId st))
                                            (getLeader st nId))

    waitVotesEn    :  isLeader st nId
                    → nextInstruction st nId ≡ 5F
                    → length (votesforQC (nodeSt nId st)) < N ∸ f ∸ 1
                    → HonestEnabled nId st wait

    receiveVoteEn  :  ∀ {v : Vote}
                    → isLeader st nId
                    → nextInstruction st nId ≡ 6F
                    → (i : readMessages (nodeSt nId st) < length (msgBuffer (nodeSt nId st)))
                    → voteM v ≡ lookup (msgBuffer (nodeSt nId st)) (fromℕ≤ i)
                    → validVote st nId v
                    → HonestEnabled nId st (receive (voteM v))

    broadcastQCEn  :  isLeader st nId
                    → nextInstruction st nId ≡ 5F
                    → length (votesforQC (nodeSt nId st)) ≡ N ∸ f ∸ 1
                    → HonestEnabled nId st (broadcastQC (mkQC (nodeSt nId st)))

    receiveQCEn    :  ∀ {qc : QC}
                    → nextInstruction st nId ≡ 7F
                    → (i : readMessages (nodeSt nId st) < length (msgBuffer (nodeSt nId st)))
                    → qcM qc ≡ lookup (msgBuffer (nodeSt nId st)) (fromℕ≤ i)
                    → validQC st nId qc
                    → HonestEnabled nId st (receive (qcM qc))

    commitEn       :  nextInstruction st nId ≡ 8F
                    -- TODO: check commit rule
                    → HonestEnabled nId st commit

    moveNextViewEn :  nextInstruction st nId ≡ 8F ⊎ DishonestID (getLeader st nId)
                    → HonestEnabled nId st moveNextView




  data Enabled : DSEvent → State → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newReqEn      : ∀ {st req}
                    → Enabled (newRequest req) st

    honestEvEn    : ∀ {st hId hEv}
                    → HonestEnabled hId st hEv
                    → Enabled (honestEvent hEv) st

    dishonestEvEn : ∀ {st dId msg hId}
                    → DishonestID dId
                    → Enabled (dishonestEvent msg hId) st
                    -- Maybe I need to postulate that dishonest nodes cannot
                    -- forge signatures (Node (N ∸ f)) 

  sendMsgToNode : Message → NodeState → NodeState
  sendMsgToNode msg nodeSt = record nodeSt { msgBuffer = msgBuffer nodeSt ++ [ msg ] }

  broadcast : State → Message → Vec NodeState (N ∸ f)
  broadcast st msg = Vec.map (λ n → sendMsgToNode msg n) (nodeStates st)


  Action : ∀ {preState} {event} → Enabled event preState → State

  Action {ps} {newRequest req} x =
    record ps
    { poolRequests = poolRequests ps ++ [ req ] }

  Action {ps} {honestEvent {nId} setNodeRole} x
    with toℕ nId ≟ toℕ (getLeader ps nId)
  ... | yes p
        = let updateNode = λ old → record old
                                   { nodeRole = leader
                                   ; control = 1F
                                   }
          in record ps
             { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }
  ... | no ¬p
        = let updateNode = λ old → record old
                               { nodeRole = follower
                               ; control = 3F
                               }
          in record ps
             { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action {ps} {honestEvent {nId} (getPoolReq req)} x
    = let updateNode = λ old → record old
                               { control = 2F
                               ; currProposal = mkBlock req old
                               }
      in record ps
         { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  -- QUESTION:
  -- Not sure if it's a good approach to consider a broadcast atomically,
  -- or have a different state transition to send to each node
  Action {ps} {honestEvent {nId} (broadcastB b)} x
    = let sendToAll = broadcast ps (blockM b)
          updateLeader = λ old → record old { control = 3F }
      in record ps
         { nodeStates = Vec.updateAt nId updateLeader sendToAll }

  Action {ps} {honestEvent {nId} (receive (blockM b))} x
    -- TODO : update RecordTree
    =  let updateNode = λ old → record old { readMessages = 1 + readMessages old
                                           ; currProposal = b
                                           ; control = 4F }
       in record ps
          { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action {ps} {honestEvent {nId} (sendVote v receiver)} x
    with toℕ receiver <? N ∸ f | nodeRole (nodeSt nId ps)
  ... | no ¬p | leader
        = let updateNode = λ old → record old { readMessages = 1 + readMessages old
                                              ; control = 5F }
          in record ps
             { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }
  ... | no ¬p | follower
        = let updateNode = λ old → record old { readMessages = 1 + readMessages old
                                              ; control = 7F }
          in record ps
             { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }
  ... | yes p | leader
        = let updateReceiver = Vec.updateAt
                                 (fromℕ≤ p)
                                 (sendMsgToNode (voteM v))
                                 (nodeStates ps)
              updateNode = λ old → record old { readMessages = 1 + readMessages old
                                              ; control = 5F }
          in record ps
             { nodeStates = Vec.updateAt nId updateNode updateReceiver }
  ... | yes p | follower
        = let updateReceiver = Vec.updateAt
                                 (fromℕ≤ p)
                                 (sendMsgToNode (voteM v))
                                 (nodeStates ps)
              updateNode = λ old → record old { readMessages = 1 + readMessages old
                                              ; control = 7F }
          in record ps
             { nodeStates = Vec.updateAt nId updateNode updateReceiver }

  Action {ps} {honestEvent {nId} wait} x
    = let updateInst = λ old → record old { control = 6F }
      in record ps
         { nodeStates = Vec.updateAt nId updateInst (nodeStates ps) }

  Action {ps} {honestEvent {nId} (receive (voteM  v))} x
    = let updateNode = λ old → record old { control = 5F
                                          ; votesforQC =  v ∷ votesforQC old }
       in record ps
          { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action {ps} {honestEvent {nId} (broadcastQC q)} x
    = let sendToAll = broadcast ps (qcM q)
          updateLeader = λ old → record old { control = 7F }
       in record ps
          { nodeStates = Vec.updateAt nId updateLeader sendToAll }

  Action {ps} {honestEvent {nId} (receive (qcM qc))} x
    = let updateNode = λ old → record old { control = 8F }
      in record ps
         { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action {ps} {honestEvent commit} x = {!!}

  Action {ps} {honestEvent {nId} moveNextView} x
    = let updateNode = λ old → record old { currNodeView = 1 + currNodeView old
                                          ; control = 0F }
      in record ps
         { nodeStates = Vec.updateAt nId updateNode (nodeStates ps) }

  Action {ps} {dishonestEvent msg hId} x
    = record ps
      { nodeStates = Vec.updateAt hId (sendMsgToNode msg) (nodeStates ps) }


