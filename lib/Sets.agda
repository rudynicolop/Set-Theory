module Sets where
  open import Data.Sum using (_⊎_;inj₁;inj₂)
  open import Relation.Binary.PropositionalEquality
    using (_≡_;refl;cong)
  open import Agda.Builtin.Unit using (⊤;tt)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬)

  module Ensembles where

    infix 4 _∈_
    infix 5 _∪_

    data Ensemble : Set where

      -- Empty set.
      ∅ : Ensemble

      -- Pairing.
      <_,_> : Ensemble → Ensemble → Ensemble

      -- Union.
      _∪_ : Ensemble → Ensemble → Ensemble
    

    _∈_ : Ensemble → Ensemble → Set
    A ∈ ∅ = ⊥
    A ∈ < B , C > = A ≡ B ⊎ A ≡ C
    A ∈ (B ∪ C) = A ∈ B ⊎ A ∈ C

  module MySet where

    infix 4 _∈_
    infix 4 _∉_
    infix 5
  
    data Ensemble : Set where
      ∅ : Ensemble

    _∈_ : Ensemble → Ensemble → Set
    _ ∈ ∅ = ⊥
    
    _∉_ : Ensemble → Ensemble → Set
    A ∉ B = ¬ (A ∈ B)
