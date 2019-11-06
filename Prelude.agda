-- This is a selection of useful function
-- from the standard library that we tend to use a lot.
module Prelude where

  open import Data.Nat
    hiding (_⊔_)
    public

  open import Level
    renaming (suc to lsuc; zero to ℓ0)
    public

  open import Relation.Binary.PropositionalEquality
    renaming ([_] to Reveal[_] )
    public

  open import Relation.Unary
    public

  open import Data.Unit
    using (⊤; tt)
    public

  open import Data.Sum
    public

  open import Data.Nat.Properties
    public

  open import Relation.Nullary
    hiding (Irrelevant)
    public

  open import Data.Product
    using (_×_; Σ; _,_; ∃; Σ-syntax; ∃-syntax)
    public

  open import Data.Empty
    using (⊥; ⊥-elim)
    public

  open import Function
    using (_∘_)
    public

