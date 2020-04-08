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
open import Data.Fin hiding (_≟_; _<?_; _+_; pred; _≤_; lift) renaming (_<_ to _<F_)
open import Data.List
open import Data.List.Properties
open import Data.Maybe.Base as Maybe using (Maybe; nothing; just)
open import Data.Vec.Base as Vec using (Vec)
open import Data.Bool hiding (_<_ ; _<?_)


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
     nodeStates    : Vec NodeState (N ∸ f)
     leaderPerView : Stream (Fin N)
     poolRequests  : List ClientRequest
     committedReq  : ℕ

     -- God's information
  open State


  HonestID = Fin (N ∸ f)


  Honest? : Decidable ((_< N ∸ f) ∘ toℕ {N})
  Honest? x = toℕ x <? N ∸ f


  data HonestEvent (nId : HonestID) : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    getPoolReq   : ClientRequest → HonestEvent nId
    broadcastB   : Block → HonestEvent nId
    broadcastQC  : QC → HonestEvent nId
    wait         : Message → HonestEvent nId
    vote         : Message → HonestEvent nId
    receive      : Message → HonestEvent nId
    mkQC         : HonestEvent nId
    commit       : HonestEvent nId
    moveNextView : HonestEvent nId


  data DSEvent : Set (ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newRequest   : ClientRequest → DSEvent -- A client add a request to the request pool
    honestEvent  : ∀ {nId} → HonestEvent nId → DSEvent
    dishonestEvent : Message → DSEvent



  nodeSt : HonestID → State → NodeState
  nodeSt nId st = Vec.lookup (nodeStates st) nId


  -- Other option is to have a flag in the NodeState saying if it's leader or follower
  isLeader : State → HonestID → Set
  isLeader st nId = let nodeView  = currNodeView (nodeSt nId st)
                    in get (leaderPerView st) nodeView ≡ inject≤ nId (n∸m≤n f N)


  {- Fin 10 is an abstraction for the number of intructions available for the node -}
  nextInstruction : State → HonestID → Fin 10
  nextInstruction st nId = control (Vec.lookup (nodeStates st) nId)


  data HonestEnabled {nId : HonestID} (st : State) : HonestEvent nId
       → Set (ℓ₂ ⊔ ℓ₃) where
    getReqEn  :  ∀ {req}
                   → isLeader st nId
                   → nextInstruction st nId ≡ 0F
                   → (comm< : committedReq st < length (poolRequests st))
                   → req ≡ lookup (poolRequests st) (fromℕ≤ comm<)
                   → HonestEnabled st (getPoolReq req)

    bcBlockEn :      isLeader st nId
                   → nextInstruction st nId ≡ 1F
                   → HonestEnabled st (broadcastB (currProposal (nodeSt nId st)))




  data Enabled1 : DSEvent → State → Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ ℓ₅) where
    newReqEn     : ∀ {st req}
                   → Enabled1 (newRequest req) st
    {- getReqEn     : ∀ {st nId req}
                   → isLeader st nId
                   → nextInstruction st nId ≡ 0F
                   → (comm< : committedReq st < length (poolRequests st))
                   → req ≡ lookup (poolRequests st) (fromℕ≤ comm<)
                   → Enabled1 (getPoolReq {!!} req) st
    bcBlockEn    : ∀ {st nId}
                   → isLeader st nId
                   → nextInstruction st nId ≡ 1F
                   → Enabled1 (broadcastB {!!} (currProposal (nodeSt nId st))) st -}



  Action1 : ∀ {preState} {event} → Enabled1 event preState → State
  Action1 {ps} {newRequest req} x =
    record ps { poolRequests = poolRequests ps ++ [ req ]}

{-
  Action1 {ps} {getPoolReq nId req} x =
    let updateNode = λ old → record old
                               { control = 1F
                               ; currProposal = mkBlock req --nodeID , currView
                               }
    in record ps
         { nodeStates = Vec.updateAt {!!} updateNode (nodeStates ps) }

  Action1 {ps} {broadcastB nId b} x =
    let sendBlock = λ node → record node { msgBuffer = msgBuffer node ++ [ block b ] }
        sendToAll = Vec.map sendBlock (nodeStates ps)
        updaTeLeader = λ old → record old { control = 2F }
     in record ps
          { nodeStates = Vec.updateAt {!!} updaTeLeader sendToAll }

-}


