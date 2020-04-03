open import Data.Nat
open import Data.Product
open import Data.Empty
open import Relation.Binary.PropositionalEquality

module Stream where

  record Stream (A : Set) : Set where
    coinductive
    field
      head : A
      tail : Stream A
  open Stream public


  get : ∀ {A : Set} → Stream A → ℕ → A
  get s zero = head s
  get s (suc i) = get s i


{-
  natsFrom : ℕ → Stream ℕ
  head (natsFrom x) = x
  tail (natsFrom x) = natsFrom (suc x)

  nats : Stream ℕ
  nats = natsFrom 0

  complicated-way-to-say-2 : head (tail (tail nats)) ≡ 2
  complicated-way-to-say-2 = refl

  -- thread a relation R through the elements of a stream
  record Trans {A : Set}(R : A → A → Set)(as : Stream A) : Set where
    coinductive
    field
      trans-head : R (head as) (head (tail as))
      trans-tail : Trans R (tail as)
  open Trans

  -- We can prove our generation of natural numbers to be correct!
  nats-correct : (n : ℕ) → Trans (λ x y → suc x ≡ y) (natsFrom n)
  trans-head (nats-correct n) = refl
  trans-tail (nats-correct n) = nats-correct (suc n)

  -----------------------------
  -- Talking Distr. Systems! --

  -- I hope I got the names right
  postulate
    State   : Set
    Event   : Set
    Enabled : State → Event → Set
    
    action  : (s : State)(e : Event)
            → (enev : Enabled s e)
            → State

    _l-t_ : (State → Set) → (State → Set) → Set
      

  -- indicates a given post-state is a possible
  -- outcome from a given pre-state; witnesses the
  -- translation to the relational scheme I mentioned
  _⟶_ : State → State → Set  
  s ⟶ s' = ∃[ e ] (Σ (Enabled s e) (λ enev → action s e enev ≡ s'))

  -- A Behavior, then, is a stream of states
  -- such that it starts at s₀ and all states
  -- are linked through the _⟶_ relation.
  -- You might want to have this in a single Beh record
  -- instead of assembling it from primitives
  Beh : State → Set
  Beh s₀ = Σ (Stream State) 
             (λ st → head st ≡ s₀ × Trans _⟶_ st)

  
  module Absurd-DO-NOT-TRY-AT-HOME where

    data HeadOrTail {A : Set}(P : A → Set)(Q : Stream A → Set)
       : Stream A → Set where
     on-head : ∀{s} → P (head s) → HeadOrTail P Q s

     -- there might be a case for including (¬ P (head s)) here...
     on-tail : ∀{s} → Q (tail s) → HeadOrTail P Q s

    record Any {A : Set}(P : A → Set)(as : Stream A) : Set where
      coinductive
      field
        any : HeadOrTail P (Any P) as
    open Any public

    -- Witness is a proof by induction that places us 
    -- at the position where P 'holds'; but as we shall see,
    -- this might never be the case and; even though the
    -- 'recursive' call makes 'progress' by traversing to the tail,
    -- it is not enough and we broke math anyway
    --
    -- Exercise to the reader: mark this function as
    -- NON_TERMINATING instead to see how Agda would stop us
    -- from breaking math! NON_TERMINATING definitions never reduce
    -- during typechecking; rendering them almost useless. They are only used
    -- when doing actual user IO AFAIC
    {-# TERMINATING #-}
    witness : {A : Set}{P : A → Set}{as : Stream A}
            → Any P as → Stream A
    witness x with any x
    ...| on-head {s} _  = s
    ...| on-tail {s} x' = witness {as = tail s} x'

    {-# NON_TERMINATING #-}
    witness-satP : {A : Set}{P : A → Set}{as : Stream A}
                 → (x : Any P as) → P (head (witness x))
    witness-satP x with any x
    ...| on-head {s} p  = p
    ...| on-tail     x' = witness-satP x'

    never : {A : Set}(P : A → Set)(as : Stream A) → Any P as
    any (never P as) = on-tail (never P (tail as))

    -- This is why induction and coinduction can't be mixed! xD
    -- note that even marking one of them as non-terminating we still
    -- run into trouble
    oh-no! : ⊥
    oh-no! = witness-satP (never (λ _ → ⊥) nats)

  -----------------------------------------
  -- Trying Again; with naturals to help -- 

  mutual
    data AtF {A : Set}(P : A → Set)
       : Stream A → ℕ → Set where
     on-head : ∀{s} → P (head s) → AtF P s 0

     on-tail : ∀{s n} → At P (tail s) n → AtF P s (suc n)

    record At {A : Set}(P : A → Set)(as : Stream A)(i : ℕ) : Set where
      coinductive
      field
        α : AtF P as i

  open At

  _satisfies_at_ : ∀{s₀}(σ : Beh s₀)(P : State → Set) → ℕ → Set
  σ satisfies P at i = At P (proj₁ σ) i

  -- Now, we can prove that a for all finite prefixes
  -- of an infinite behaviour such that they satisfy P
  -- at some observable point, they will satisfy Q at
  -- some future obervable point.

  -- Note the use of the word observable here! I like to think of coinduction
  -- in terms of dominos-chain-reaction. Imagine we want to knock a domino
  -- x₀ and we want to reason whether or not it knocks over a domino x'.
  -- Now sawy we reason like this:
  -- that we x₀ will knock x₁; which in turn will knock x₂; ... and
  -- eventually will knock x'. Well; it is induction that guarantees
  -- this for us, and induction requires the number of dominoes between
  -- x and x' to be countable (isomorphic to ℕ).
  --
  -- If there truly is an infinite number of dominoes between x and x',
  -- it means that no matter how far we get, there will always be 
  -- at least one domino between where we are and x'; and the wave of
  -- knocks will never reach x', hence, that type of reasoning is plain invalid.
  --
  -- Behaviors are pottentially plain infinite; some systems never stop.
  -- We still want to guarantee certain invariants.
  -- 

  -- Soundness, as I see it, is a proof that given any behavior σ
  -- that eventually satisfy P; and given that P leads to Q;
  -- any behaviour that forks of the point where σ satisfied P
  -- must satisfy Q; A first sketch in agda could be: 
  soundness : {P Q : State → Set}  
            → ∀{s₀ i}(σ : Beh s₀)(prf : σ satisfies P at i)
            → P l-t Q
            → Σ ℕ (λ j → σ satisfies Q at (j + i)) -- j + i already guarantess it is the future
  soundness = {! may-the-force-be-with-us !}
-}
