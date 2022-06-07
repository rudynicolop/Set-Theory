module Axioms where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Sum.Base using (_⊎_;inj₁;inj₂)
  open import Data.Product
    using (proj₁;proj₂;Σ-syntax;∃-syntax;∄-syntax;_×_;Σ;∃;∄;_,_)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)

  infix 0 _↔_

  _↔_ : Set → Set → Set
  A ↔ B = (A → B) × (B → A)

  module Sets
    -- Abstract type for sets.
    (set : Set)

    -- Set membership.
    (_∈_ : set → set → Set)

    -- Set extensionality.
    (extensionality : ∀ (A B : set)
      → (∀ (x : set) → x ∈ A ↔ x ∈ B) → A ≡ B)

    -- Empty set.
    (∅ : Σ[ B ∈ set ] ∀ (x : set) → ¬ (x ∈ B))

    -- Paring axiom.
    (⟨_,_⟩ : ∀ (u v : set)
      → Σ[ B ∈ set ] ∀ (x : set) → x ∈ B ↔ x ≡ u ⊎ x ≡ v)

    -- Power set.
    (pow : ∀ (a : set)
      → Σ[ B ∈ set ] ∀ (x : set)
      → x ∈ B ↔ ({y : set} → y ∈ x → x ∈ a))

    -- Arbitray union.
    (⋃ : ∀ (A : set)
      → Σ[ B ∈ set ] ∀ (x : set)
      → x ∈ B ↔ ∃[ b ] b ∈ A × x ∈ b)

    -- Subset schema.
    (comprehension : ∀ (c : set) (ϕ : set → Set)
      → Σ[ B ∈ set ] ∀ (x : set) → x ∈ B ↔ x ∈ c × ϕ x)
    where

    infix 4 _∉_
    infix 4 _⊆_

    _∉_ : set → set → Set
    A ∉ B = ¬ (A ∈ B)

    -- Subsets.
    _⊆_ : set → set → Set
    A ⊆ B = ∀ {x : set} → x ∈ A → x ∈ B

      
    comp = comprehension

    infix 5 comp
    syntax comp c (λ x → ϕ) =  [ x ∈ c ∣ ϕ ]

    singleton : set → set
    singleton A = proj₁ ⟨ A , A ⟩

    theorem-2A : ∄[ A ] ∀ (z : set) → z ∈ A
    theorem-2A (A , h) with [ x ∈ A ∣ x ∉ x ]
    ... | B , H with H B
    ... | H₁ , H₂ with H₂ ((h B) , helper-B∉B)
      where
        helper-B∉B : B ∉ B
        helper-B∉B B∈B with H₁ B∈B
        ... | _ , B∉B = B∉B B∈B
    ... | B∈B with H₁ B∈B
    ... | _ , B∉B = B∉B B∈B

    infix 3 _∪_

    _∪_ : ∀ (a b : set) → Σ[ B ∈ set ] ∀ x → x ∈ B ↔ x ∈ a ⊎ x ∈ b
    a ∪ b = (proj₁ ⟨a,b⟩) , {!!}
      where
        ⟨a,b⟩ = ⟨ a , b ⟩
        ⋃⟨a,b⟩ = ⋃ (proj₁ ⟨a,b⟩)
        lemma : (x : set) → (x ∈ proj₁ ⟨a,b⟩) ↔ (x ∈ a) ⊎ (x ∈ b)
        lemma x = {!!} , {!!}
        lemma₁ : ∀ (x : set) → x ∈ proj₁ ⟨a,b⟩ → (x ∈ a) ⊎ (x ∈ b)
        lemma₁ x x∈⟨a,b⟩ with proj₂ ⟨a,b⟩
        ... | h with h = {!!}
