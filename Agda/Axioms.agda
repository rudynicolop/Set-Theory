module Axioms where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Sum.Base using (_⊎_;inj₁;inj₂;reduce)
  open import Data.Product
    using (proj₁;proj₂;_×_;Σ;∃;∄;_,_;
      Σ-syntax;∃-syntax;∄-syntax)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)

  infix 0 _↔_
  infix 4 _≢_

  _↔_ : Set → Set → Set
  A ↔ B = (A → B) × (B → A)

  _≢_ : ∀ {A : Set} → A → A → Set
  x ≢ y = ¬ (x ≡ y)

  module Sets
    -- Abstract type for sets.
    (set : Set)

    -- Set membership.
    (_∈_ : set → set → Set)

    -- Set extensionality.
    (extensionality : ∀ (A B : set)
      → (∀ (x : set) → x ∈ A ↔ x ∈ B) → A ≡ B)

    -- Empty set.
    (∅ : ∃[ B ] ∀ (x : set) → ¬ (x ∈ B))

    -- Paring axiom.
    (⟨_,_⟩ : ∀ (u v : set)
      → ∃[ B ] ∀ (x : set) → x ∈ B ↔ x ≡ u ⊎ x ≡ v)

    -- Power set.
    (pow : ∀ (a : set)
      → ∃[ B ] ∀ (x : set)
      → x ∈ B ↔ ({y : set} → y ∈ x → x ∈ a))

    -- Arbitray union.
    (⋃ : ∀ (A : set)
      → ∃[ B ] ∀ (x : set)
      → x ∈ B ↔ ∃[ b ] b ∈ A × x ∈ b)

    -- Subset schema.
    (comprehension : ∀ (c : set) (ϕ : set → Set)
      → ∃[ B ] ∀ (x : set) → x ∈ B ↔ x ∈ c × ϕ x)
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

    singleton : ∀ (A : set) → ∃[ B ] ∀ x → x ∈ B ↔ x ≡ A
    singleton A = proj₁ ⟨A,A⟩ , lemma
      where
        ⟨A,A⟩ = ⟨ A , A ⟩
        lemma→ : ∀ (x : set) → (x ∈ proj₁ ⟨A,A⟩) → x ≡ A
        lemma→ x x∈⟨A,A⟩ with proj₂ ⟨A,A⟩ x
        ... | x∈⟨A,A⟩→x≡A⊎x≡A , _ = reduce (x∈⟨A,A⟩→x≡A⊎x≡A x∈⟨A,A⟩)
        lemma← : ∀ (x : set) → x ≡ A → (x ∈ proj₁ ⟨A,A⟩)
        lemma← x refl with proj₂ ⟨A,A⟩ x
        ... | _ , h = h (inj₁ refl)
        lemma : ∀ (x : set) → (x ∈ proj₁ ⟨A,A⟩) ↔ x ≡ A
        lemma x = lemma→ x , lemma← x

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

    _∪_ : ∀ (a b : set) → ∃[ B ] ∀ x → x ∈ B ↔ x ∈ a ⊎ x ∈ b
    a ∪ b = (proj₁ ⋃⟨a,b⟩) , lemma
      where
        ⟨a,b⟩ = ⟨ a , b ⟩
        ⋃⟨a,b⟩ = ⋃ (proj₁ ⟨a,b⟩)
        lemma₁ : ∀ (x : set) → x ∈ proj₁ ⋃⟨a,b⟩ → (x ∈ a) ⊎ (x ∈ b)
        lemma₁ x x∈⋃⟨a,b⟩ with proj₂ ⋃⟨a,b⟩ x
        ... | h , _ with h x∈⋃⟨a,b⟩
        ... | z , z∈⟨a,b⟩ , x∈z with proj₂ ⟨a,b⟩ z
        ... | H , _ with H z∈⟨a,b⟩
        ... | inj₁ refl = inj₁ x∈z
        ... | inj₂ refl = inj₂ x∈z
        lemma₂ : ∀ (x : set) → (x ∈ a) ⊎ (x ∈ b) → x ∈ proj₁ ⋃⟨a,b⟩
        lemma₂ x (inj₁ x∈a) with proj₂ ⋃⟨a,b⟩ x
        ... | _ , h with proj₂ ⟨a,b⟩ a
        ... | _ , a≡a⊎a≡b→a∈⟨a,b⟩ = h (a , a≡a⊎a≡b→a∈⟨a,b⟩ (inj₁ refl) , x∈a)
        lemma₂ x (inj₂ x∈b) with proj₂ ⋃⟨a,b⟩ x
        ... | _ , h with proj₂ ⟨a,b⟩ b
        ... | _ , b≡a⊎b≡b→b∈⟨a,b⟩ = h (b , b≡a⊎b≡b→b∈⟨a,b⟩ (inj₂ refl) , x∈b)
        lemma : (x : set) → (x ∈ proj₁ ⋃⟨a,b⟩) ↔ (x ∈ a) ⊎ (x ∈ b)
        lemma x = lemma₁ x , lemma₂ x

    -- Theorem 2B, Arbitrary intersection.
    ⋂ : ∀ (A : set) → (∃[ a ] a ∈ A)
      → ∃[ B ] ∀ x → x ∈ B ↔ (∀ a → a ∈ A → x ∈ a)
    ⋂ A (c , c∈A) = (proj₁ cmp) , λ x → lemma→ x , lemma← x
      where
        cmp = [ x ∈ c ∣ (∀ a → a ∈ A → x ∈ a) ]
        lemma→ : ∀ x → x ∈ proj₁ cmp → (a : set) → a ∈ A → x ∈ a
        lemma→ x x∈cmp a a∈A with proj₂ cmp x
        ... | h , _ with h x∈cmp
        ... | _ , a∈A→x∈a = a∈A→x∈a a a∈A
        lemma← : ∀ x → (∀ a → a ∈ A → x ∈ a) → x ∈ proj₁ cmp
        lemma← x a∈A→x∈a with proj₂ cmp x
        ... | _ , h = h (a∈A→x∈a c c∈A , a∈A→x∈a)

    infix 3 _∩_

    _∩_ : ∀ (a b : set) → ∃[ B ] ∀ x → x ∈ B ↔ x ∈ a × x ∈ b
    a ∩ b = (proj₁ ⋂⟨a,b⟩) , λ x → lemma→ x , lemma← x
      where
        ⟨a,b⟩ = ⟨ a , b ⟩
        ∃z∈⟨a,b⟩ : ∃[ z ] z ∈ proj₁ ⟨a,b⟩
        ∃z∈⟨a,b⟩ with proj₂ ⟨a,b⟩ a
        ... | _ , a≡a⊎a≡b→a∈⟨a,b⟩ = a , a≡a⊎a≡b→a∈⟨a,b⟩ (inj₁ refl)
        ⋂⟨a,b⟩ = ⋂ (proj₁ ⟨a,b⟩) ∃z∈⟨a,b⟩
        lemma→ : ∀ x → x ∈ proj₁ ⋂⟨a,b⟩ → (x ∈ a) × (x ∈ b)
        lemma→ x x∈⋂⟨a,b⟩ with proj₂ ⋂⟨a,b⟩ x
        ... | h , _ with h x∈⋂⟨a,b⟩
        ... | ∀z∈⟨a,b⟩→x∈z with proj₂ ⟨a,b⟩ a | proj₂ ⟨a,b⟩ b
        ... | _ , a≡a⊎a≡b→a∈⟨a,b⟩
            | _ , b≡a⊎b≡b→b∈⟨a,b⟩
              = ∀z∈⟨a,b⟩→x∈z a (a≡a⊎a≡b→a∈⟨a,b⟩ (inj₁ refl))
              , ∀z∈⟨a,b⟩→x∈z b (b≡a⊎b≡b→b∈⟨a,b⟩ (inj₂ refl))
        lemma← : ∀ x → (x ∈ a) × (x ∈ b) → x ∈ proj₁ ⋂⟨a,b⟩
        lemma← x ( x∈a , x∈b ) with proj₂ ⋂⟨a,b⟩ x
        ... | _ , h = h ∀z∈⟨a,b⟩→x∈z
          where
            ∀z∈⟨a,b⟩→x∈z : ∀ z → z ∈ proj₁ ⟨ a , b ⟩ → x ∈ z
            ∀z∈⟨a,b⟩→x∈z z z∈⟨a,b⟩ with proj₂ ⟨a,b⟩ z
            ... | z∈⟨a,b⟩→z≡a⊎z≡b , _ with z∈⟨a,b⟩→z≡a⊎z≡b z∈⟨a,b⟩
            ... | inj₁ refl = x∈a
            ... | inj₂ refl = x∈b
        
