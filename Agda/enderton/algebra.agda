module enderton.algebra where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contraposition)
  open import Data.Sum.Base using (_⊎_;inj₁;inj₂;reduce)
  open import Data.Product
    using (proj₁;proj₂;_×_;Σ;∃;∄;_,_;
      Σ-syntax;∃-syntax;∄-syntax)
  open import enderton.Axioms using (set;_∈_;_∉_;_⊆_;⋃;pow
    ;extensionality;_↔_;_∩_;comprehension;⋂;_∪_
    ;comprehension-syntax;⟨_,_⟩;singleton;Theorem-2A;_─_;∅)

  A∪B─C≡A─C∪B─C : ∀ A B C
    → proj₁ ((proj₁ (A ∪ B)) ─ C) ≡ proj₁ (proj₁ (A ─ C) ∪ proj₁ (B ─ C))
  A∪B─C≡A─C∪B─C A B C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
    lemma→ : ∀ x → x ∈ proj₁ (proj₁ (A ∪ B) ─ C)
      → x ∈ proj₁ (proj₁ (A ─ C) ∪ proj₁ (B ─ C))
    lemma→ x x∈A∪B─C
      with proj₂ (proj₁ (A ∪ B) ─ C) x
        | proj₂ (A ∪ B) x
    ... | x∈A∪B─C→x∈A∪B×x∉C , _
        | x∈A∪B→x∈A⊎x∈B , _
          with x∈A∪B─C→x∈A∪B×x∉C x∈A∪B─C
            | proj₂ (proj₁ (A ─ C) ∪ proj₁ (B ─ C)) x
    ... | x∈A∪B , x∉C | _ , x∈A─C⊎x∈B─C→x∈A─C∪B─C
      with x∈A∪B→x∈A⊎x∈B x∈A∪B
    ... | inj₁ x∈A = x∈A─C⊎x∈B─C→x∈A─C∪B─C (inj₁ (proj₂ (proj₂ (A ─ C) x) (x∈A , x∉C)))
    ... | inj₂ x∈B = x∈A─C⊎x∈B─C→x∈A─C∪B─C (inj₂ (proj₂ (proj₂ (B ─ C) x) (x∈B , x∉C)))
    lemma← : ∀ x → x ∈ proj₁ (proj₁ (A ─ C) ∪ proj₁ (B ─ C))
      → x ∈ proj₁ (proj₁ (A ∪ B) ─ C)
    lemma← x x∈A─C∪B─C
      with proj₂ (proj₁ (A ─ C) ∪ proj₁ (B ─ C)) x
        | proj₂ (proj₁ (A ∪ B) ─ C) x
        | proj₂ (A ∪ B) x | proj₂ (A ─ C) x | proj₂ (B ─ C) x
    ... | x∈A─C∪B─C→x∈A─C⊎x∈B─C , _
        | _ , x∈A∪B×x∉C→x∈A∪B─C
        | _ , x∈A⊎x∈B→x∈A∪B
        | x∈A─C→x∈A×x∉C , _ | x∈B─C→x∈B×x∉C , _
          with x∈A─C∪B─C→x∈A─C⊎x∈B─C x∈A─C∪B─C
    ... | inj₁ x∈A─C = x∈A∪B×x∉C→x∈A∪B─C
      (x∈A⊎x∈B→x∈A∪B (inj₁ (proj₁ (x∈A─C→x∈A×x∉C x∈A─C)))
      , proj₂ (x∈A─C→x∈A×x∉C x∈A─C))
    ... | inj₂ x∈B─C with x∈B─C→x∈B×x∉C x∈B─C
    ... | x∈B , x∉C = x∈A∪B×x∉C→x∈A∪B─C (x∈A⊎x∈B→x∈A∪B (inj₂ x∈B) , x∉C)

  -- Commutatitve Laws.

  A∪B⊆B∪A : ∀ A B → proj₁ (A ∪ B) ⊆ proj₁ (B ∪ A)
  A∪B⊆B∪A A B {x} x∈A∪B
    with proj₂ (A ∪ B) x | proj₂ (B ∪ A) x
  ... | x∈A∪B→x∈A⊎x∈B , _
      | _ , x∈B⊎x∈A→x∈B∪A with x∈A∪B→x∈A⊎x∈B x∈A∪B
  ... | inj₁ x∈A = x∈B⊎x∈A→x∈B∪A (inj₂ x∈A)
  ... | inj₂ x∈B = x∈B⊎x∈A→x∈B∪A (inj₁ x∈B)
  
  A∪B≡B∪A : ∀ A B → proj₁ (A ∪ B) ≡ proj₁ (B ∪ A)
  A∪B≡B∪A A B = extensionality _ _ λ x → A∪B⊆B∪A A B {x} , A∪B⊆B∪A B A {x}

  A∩B⊆B∩A : ∀ A B → proj₁ (A ∩ B) ⊆ proj₁ (B ∩ A)
  A∩B⊆B∩A A B {x} x∈A∩B with proj₂ (A ∩ B) x | proj₂ (B ∩ A) x
  ... | x∈A∩B→x∈A×x∈B , _
      | _ , x∈B×x∈A→x∈B∩A with x∈A∩B→x∈A×x∈B x∈A∩B
  ... | x∈A , x∈B = x∈B×x∈A→x∈B∩A (x∈B , x∈A)

  A∩B≡B∩A : ∀ A B → proj₁ (A ∩ B) ≡ proj₁ (B ∩ A)
  A∩B≡B∩A A B = extensionality _ _ λ x → A∩B⊆B∩A A B {x} , A∩B⊆B∩A B A {x}

  -- Associative Laws.

  ∪-assoc : ∀ A B C
    → proj₁ (A ∪ proj₁ (B ∪ C)) ≡ proj₁ (proj₁ (A ∪ B) ∪ C)
  ∪-assoc A B C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (A ∪ proj₁ (B ∪ C)) → x ∈ proj₁ (proj₁ (A ∪ B) ∪ C)
      lemma→ x x∈A∪B∪C
        with proj₂ (A ∪ proj₁ (B ∪ C)) x
          | proj₂ (proj₁ (A ∪ B) ∪ C) x
      ... | x∈A∪B∪C→x∈A⊎x∈B∪C , _
          | _ , x∈A∪B⊎x∈C→x∈A∪B∪C
          with x∈A∪B∪C→x∈A⊎x∈B∪C x∈A∪B∪C
      ... | inj₁ x∈A = x∈A∪B⊎x∈C→x∈A∪B∪C (inj₁ (proj₂ (proj₂ (A ∪ B) x) (inj₁ x∈A)))
      ... | inj₂ x∈B∪C with proj₂ (B ∪ C) x
      ... | x∈B∪C→x∈B⊎x∈C , _ with x∈B∪C→x∈B⊎x∈C x∈B∪C
      ... | inj₁ x∈B = x∈A∪B⊎x∈C→x∈A∪B∪C (inj₁ (proj₂ (proj₂ (A ∪ B) x) (inj₂ x∈B)))
      ... | inj₂ x∈C = x∈A∪B⊎x∈C→x∈A∪B∪C (inj₂ x∈C)
      lemma← : ∀ x
        → x ∈ proj₁ (proj₁ (A ∪ B) ∪ C) → x ∈ proj₁ (A ∪ proj₁ (B ∪ C))
      lemma← x x∈A∪B∪C
        with proj₂ (proj₁ (A ∪ B) ∪ C) x
          | proj₂ (A ∪ proj₁ (B ∪ C)) x
      ... | x∈A∪B∪C→x∈A∪B⊎x∈C , _
          | _ , x∈A⊎x∈B∪C→x∈A∪B∪C
          with x∈A∪B∪C→x∈A∪B⊎x∈C x∈A∪B∪C
      ... | inj₂ x∈C = x∈A⊎x∈B∪C→x∈A∪B∪C (inj₂ (proj₂ (proj₂ (B ∪ C) x) (inj₂ x∈C)))
      ... | inj₁ x∈A∪B with proj₁ (proj₂ (A ∪ B) x) x∈A∪B
      ... | inj₁ x∈A = x∈A⊎x∈B∪C→x∈A∪B∪C (inj₁ x∈A)
      ... | inj₂ x∈B = x∈A⊎x∈B∪C→x∈A∪B∪C (inj₂ (proj₂ (proj₂ (B ∪ C) x) (inj₁ x∈B)))

  ∩-assoc : ∀ A B C
    → proj₁ (A ∩ proj₁ (B ∩ C)) ≡ proj₁ (proj₁ (A ∩ B) ∩ C)
  ∩-assoc A B C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (A ∩ proj₁ (B ∩ C))
        → x ∈ proj₁ (proj₁ (A ∩ B) ∩ C)
      lemma→ x x∈A∩B∩C
        with proj₂ (A ∩ proj₁ (B ∩ C)) x
          | proj₂ (proj₁ (A ∩ B) ∩ C) x
      ... | x∈A∩B∩C→x∈A×x∈xB∩C , _
          | _ , x∈A∩B×x∈C→x∈A∩B∩C
          with x∈A∩B∩C→x∈A×x∈xB∩C x∈A∩B∩C
      ... | x∈A , x∈B∩C with proj₂ (B ∩ C) x
      ... | x∈B∩C→x∈B×x∈C , _ with x∈B∩C→x∈B×x∈C x∈B∩C
      ... | x∈B , x∈C = x∈A∩B×x∈C→x∈A∩B∩C
        (proj₂ (proj₂ (A ∩ B) x) (x∈A , x∈B) , x∈C)
      lemma← : ∀ x
        → x ∈ proj₁ (proj₁ (A ∩ B) ∩ C)
        → x ∈ proj₁ (A ∩ proj₁ (B ∩ C))
      lemma← x x∈A∩B∩C
        with proj₂ (proj₁ (A ∩ B) ∩ C) x
          | proj₂ (A ∩ proj₁ (B ∩ C)) x
      ... | x∈A∩B∩C→x∈A∩B×x∈C , _
          | _ , x∈A×x∈xB∩C→x∈A∩B∩C
          with x∈A∩B∩C→x∈A∩B×x∈C x∈A∩B∩C
      ... | x∈A∩B , x∈C with proj₂ (A ∩ B) x
      ... | x∈A∩B→x∈A×x∈B , _
        with x∈A∩B→x∈A×x∈B x∈A∩B
      ... | x∈A , x∈B = x∈A×x∈xB∩C→x∈A∩B∩C
        (x∈A , proj₂ (proj₂ (B ∩ C) x) (x∈B , x∈C))

  -- Distributive Laws.

  ∩-distr-∪ : ∀ A B C
    → proj₁ (A ∩ proj₁ (B ∪ C)) ≡ proj₁ (proj₁ (A ∩ B) ∪ proj₁ (A ∩ C))
  ∩-distr-∪ A B C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (A ∩ proj₁ (B ∪ C))
        → x ∈ proj₁ (proj₁ (A ∩ B) ∪ proj₁ (A ∩ C))
      lemma→ x x∈A∩B∪C
        with proj₂ (A ∩ proj₁ (B ∪ C)) x
          | proj₂ (proj₁ (A ∩ B) ∪ proj₁ (A ∩ C)) x
      ... | x∈A∩B∪C→x∈A×x∈B∪C , _
          | _ , x∈A∩B⊎x∈A∩C→x∈A∩B∪A∩C
          with x∈A∩B∪C→x∈A×x∈B∪C x∈A∩B∪C
      ... | x∈A , x∈B∪C with proj₁ (proj₂ (B ∪ C) x) x∈B∪C
      ... | inj₁ x∈B = x∈A∩B⊎x∈A∩C→x∈A∩B∪A∩C
        (inj₁ (proj₂ (proj₂ (A ∩ B) x) (x∈A , x∈B)))
      ... | inj₂ x∈C = x∈A∩B⊎x∈A∩C→x∈A∩B∪A∩C
        (inj₂ (proj₂ (proj₂ (A ∩ C) x) (x∈A , x∈C)))
      lemma← : ∀ x
        → x ∈ proj₁ (proj₁ (A ∩ B) ∪ proj₁ (A ∩ C))
        → x ∈ proj₁ (A ∩ proj₁ (B ∪ C))
      lemma← x x∈A∩B∪A∩C
        with proj₂ (proj₁ (A ∩ B) ∪ proj₁ (A ∩ C)) x
          | proj₂ (A ∩ proj₁ (B ∪ C)) x
      ... | x∈A∩B∪A∩C→x∈A∩B⊎x∈A∩C , _
          | _ , x∈A×x∈B∪C→x∈A∩B∪C
          with x∈A∩B∪A∩C→x∈A∩B⊎x∈A∩C x∈A∩B∪A∩C
      ... | inj₁ x∈A∩B = x∈A×x∈B∪C→x∈A∩B∪C
        (proj₁ (proj₁ (proj₂ (A ∩ B) x) x∈A∩B)
        , proj₂ (proj₂ (B ∪ C) x) (inj₁ (proj₂ (proj₁ (proj₂ (A ∩ B) x) x∈A∩B))))
      ... | inj₂ x∈A∩C = x∈A×x∈B∪C→x∈A∩B∪C
        (proj₁ (proj₁ (proj₂ (A ∩ C) x) x∈A∩C)
        , proj₂ (proj₂ (B ∪ C) x) (inj₂ (proj₂ (proj₁ (proj₂ (A ∩ C) x) x∈A∩C))))

  ∪-distr-∩ : ∀ A B C
    → proj₁ (A ∪ proj₁ (B ∩ C)) ≡ proj₁ (proj₁ (A ∪ B) ∩ proj₁ (A ∪ C))
  ∪-distr-∩ A B C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (A ∪ proj₁ (B ∩ C))
        → x ∈ proj₁ (proj₁ (A ∪ B) ∩ proj₁ (A ∪ C))
      lemma→ x x∈A∪B∩C
        with proj₂ (A ∪ proj₁ (B ∩ C)) x
          | proj₂ (proj₁ (A ∪ B) ∩ proj₁ (A ∪ C)) x
      ... | x∈A∪B∩C→x∈A⊎x∈B∩C , _
          | _ , x∈A∪B×x∈A∪C→x∈A∪B∩A∪C
          with x∈A∪B∩C→x∈A⊎x∈B∩C x∈A∪B∩C
      ... | inj₁ x∈A = x∈A∪B×x∈A∪C→x∈A∪B∩A∪C
        (proj₂ (proj₂ (A ∪ B) x) (inj₁ x∈A)
        , proj₂ (proj₂ (A ∪ C) x) (inj₁ x∈A))
      ... | inj₂ x∈B∩C with proj₁ (proj₂ (B ∩ C) x) x∈B∩C
      ... | x∈B , x∈C = x∈A∪B×x∈A∪C→x∈A∪B∩A∪C
        (proj₂ (proj₂ (A ∪ B) x) (inj₂ x∈B)
        , proj₂ (proj₂ (A ∪ C) x) (inj₂ x∈C))
      lemma← : ∀ x
        → x ∈ proj₁ (proj₁ (A ∪ B) ∩ proj₁ (A ∪ C))
        → x ∈ proj₁ (A ∪ proj₁ (B ∩ C))
      lemma← x x∈A∪B∩A∪C
        with proj₁ (proj₂ (proj₁ (A ∪ B) ∩ proj₁ (A ∪ C)) x) x∈A∪B∩A∪C
        | proj₂ (A ∪ proj₁ (B ∩ C)) x
      ... | x∈A∪B , x∈A∪C
          | _ , x∈A⊎x∈B∩C→x∈A∪B∩C
        with proj₁ (proj₂ (A ∪ B) x) x∈A∪B
          | proj₁ (proj₂ (A ∪ C) x) x∈A∪C
      ... | inj₁ x∈A | _        = x∈A⊎x∈B∩C→x∈A∪B∩C (inj₁ x∈A)
      ... | inj₂ _   | inj₁ x∈A = x∈A⊎x∈B∩C→x∈A∪B∩C (inj₁ x∈A)
      ... | inj₂ x∈B | inj₂ x∈C = x∈A⊎x∈B∩C→x∈A∪B∩C
        (inj₂ (proj₂ (proj₂ (B ∩ C) x) (x∈B , x∈C)))

  -- De Morgan's Laws.

  x∉A∪B→x∉A : ∀ {A B x}
    → x ∉ proj₁ (A ∪ B) → x ∉ A
  x∉A∪B→x∉A {A} {B} {x} x∉A∪B x∈A = x∉A∪B
    (proj₂ (proj₂ (A ∪ B) x) (inj₁ x∈A))

  x∉A∪B→x∉B : ∀ {A B x}
    → x ∉ proj₁ (A ∪ B) → x ∉ B
  x∉A∪B→x∉B {A} {B} {x} x∉A∪B x∈B = x∉A∪B
    (proj₂ (proj₂ (A ∪ B) x) (inj₂ x∈B))

  x∉A∪B→x∉A×x∉B : ∀ {A B x}
    → x ∉ proj₁ (A ∪ B) → x ∉ A × x ∉ B
  x∉A∪B→x∉A×x∉B {A} {B} {x} x∉A∪B = x∉A∪B→x∉A x∉A∪B , x∉A∪B→x∉B x∉A∪B

  x∉A→x∉B→x∉A∪B : ∀ {A B x}
    → x ∉ A → x ∉ B → x ∉ proj₁ (A ∪ B)
  x∉A→x∉B→x∉A∪B {A} {B} {x} x∉A x∉B x∈A∪B
    with proj₁ (proj₂ (A ∪ B) x) x∈A∪B
  ... | inj₁ x∈A = x∉A x∈A
  ... | inj₂ x∈B = x∉B x∈B

  C─A∪B≡C─A∩C─B : ∀ A B C
    → proj₁ (C ─ proj₁ (A ∪ B)) ≡ proj₁ (proj₁ (C ─ A) ∩ proj₁ (C ─ B))
  C─A∪B≡C─A∩C─B A B C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (C ─ proj₁ (A ∪ B))
        → x ∈ proj₁ (proj₁ (C ─ A) ∩ proj₁ (C ─ B))
      lemma→ x x∈C─A∪B
        with proj₁ (proj₂ (C ─ proj₁ (A ∪ B)) x) x∈C─A∪B
      ... | x∈C , x∉A∪B with x∉A∪B→x∉A×x∉B x∉A∪B
      ... | x∉A , x∉B = proj₂
        (proj₂ (proj₁ (C ─ A) ∩ proj₁ (C ─ B)) x)
        (proj₂ (proj₂ (C ─ A) x) (x∈C , x∉A)
        , proj₂ (proj₂ (C ─ B) x) (x∈C , x∉B))
      lemma← : ∀ x
        → x ∈ proj₁ (proj₁ (C ─ A) ∩ proj₁ (C ─ B))
        → x ∈ proj₁ (C ─ proj₁ (A ∪ B))
      lemma← x x∈C─A∪C─B
        with proj₁ (proj₂ (proj₁ (C ─ A) ∩ proj₁ (C ─ B)) x) x∈C─A∪C─B
      ... | x∈C─A , x∈C─B
        with proj₁ (proj₂ (C ─ A) x) x∈C─A
          | proj₁ (proj₂ (C ─ B) x) x∈C─B
      ... | x∈C , x∉A | _ , x∉B = proj₂
        (proj₂ (C ─ proj₁ (A ∪ B)) x)
        (x∈C , x∉A→x∉B→x∉A∪B x∉A x∉B)

  -- Theorems that require excluded middle
  module de_morgan_exm
    (P⊎¬P : ∀ (P : Set) → P ⊎ ¬ P) where

    x∉A∩B→x∉A⊎x∉B : ∀ {A B x}
      → x ∉ proj₁ (A ∩ B) → x ∉ A ⊎ x ∉ B
    x∉A∩B→x∉A⊎x∉B {A} {B} {x} x∉A∩B with P⊎¬P (x ∈ A)
    ... | inj₂ x∉A = inj₁ x∉A
    ... | inj₁ x∈A with P⊎¬P (x ∈ B)
    ... | inj₂ x∉B = inj₂ x∉B
    ... | inj₁ x∈B = ⊥-elim (x∉A∩B (proj₂ (proj₂ (A ∩ B) x) (x∈A , x∈B)))

    C─A∩B≡C─A∪C─B : ∀ A B C
      → proj₁ (C ─ proj₁ (A ∩ B)) ≡ proj₁ (proj₁ (C ─ A) ∪ proj₁ (C ─ B))
    C─A∩B≡C─A∪C─B A B C = extensionality _ _ λ x → lemma→ x , lemma← x
      where
        lemma→ : ∀ x
          → x ∈ proj₁ (C ─ proj₁ (A ∩ B))
          → x ∈ proj₁ (proj₁ (C ─ A) ∪ proj₁ (C ─ B))
        lemma→ x x∈C─A∩B
          with proj₁ (proj₂ (C ─ (proj₁ (A ∩ B))) x) x∈C─A∩B
        ... | x∈C , x∉A∩B with x∉A∩B→x∉A⊎x∉B x∉A∩B
        ... | inj₁ x∉A = proj₂
          (proj₂ (proj₁ (C ─ A) ∪ proj₁ (C ─ B)) x)
          (inj₁ (proj₂ (proj₂ (C ─ A) x) (x∈C , x∉A)))
        ... | inj₂ x∉B = proj₂
          (proj₂ (proj₁ (C ─ A) ∪ proj₁ (C ─ B)) x)
          (inj₂ (proj₂ (proj₂ (C ─ B) x) (x∈C , x∉B)))
        lemma← : ∀ x
          → x ∈ proj₁ (proj₁ (C ─ A) ∪ proj₁ (C ─ B))
          → x ∈ proj₁ (C ─ proj₁ (A ∩ B))
        lemma← x x∈C─A∪C─B
          with proj₁
            (proj₂ (proj₁ (C ─ A) ∪ proj₁ (C ─ B)) x)
            x∈C─A∪C─B
        ... | inj₁ x∈C─A = proj₂
          (proj₂ (C ─ proj₁ (A ∩ B)) x)
          (proj₁ (proj₁ (proj₂ (C ─ A) x) x∈C─A)
          , contraposition
            (proj₁ (proj₂ (A ∩ B) x))
            λ { (x∈A , _) → proj₂ (proj₁ (proj₂ (C ─ A) x) x∈C─A) x∈A })
        ... | inj₂ x∈C─B = proj₂
          (proj₂ (C ─ proj₁ (A ∩ B)) x)
          (proj₁ (proj₁ (proj₂ (C ─ B) x) x∈C─B)
          , contraposition
            (proj₁ (proj₂ (A ∩ B) x))
            λ { (_ , x∈B) → proj₂ (proj₁ (proj₂ (C ─ B) x) x∈C─B) x∈B })

  -- Identities.

  A∪∅≡A : ∀ A → proj₁ (A ∪ proj₁ ∅) ≡ A
  A∪∅≡A A = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x → x ∈ proj₁ (A ∪ proj₁ ∅) → x ∈ A
      lemma→ x x∈A∪∅ with proj₁ (proj₂ (A ∪ proj₁ ∅) x) x∈A∪∅
      ... | inj₁ x∈A = x∈A
      ... | inj₂ x∈∅ = ⊥-elim (proj₂ ∅ x x∈∅)
      lemma← : ∀ x → x ∈ A → x ∈ proj₁ (A ∪ proj₁ ∅)
      lemma← x x∈A = proj₂ (proj₂ (A ∪ proj₁ ∅) x) (inj₁ x∈A)

  A∩∅≡∅ : ∀ A → proj₁ (A ∩ proj₁ ∅) ≡ proj₁ ∅
  A∩∅≡∅ A = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x → x ∈ proj₁ (A ∩ proj₁ ∅) → x ∈ proj₁ ∅
      lemma→ x x∈A∩∅
        with proj₁ (proj₂ (A ∩ proj₁ ∅) x) x∈A∩∅
      ... | _ , x∈∅ = x∈∅
      lemma← : ∀ x → x ∈ proj₁ ∅ → x ∈ proj₁ (A ∩ proj₁ ∅)
      lemma← x x∈∅ = ⊥-elim (proj₂ ∅ x x∈∅)

  A─∅≡A : ∀ A → proj₁ (A ─ proj₁ ∅) ≡ A
  A─∅≡A A = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x → x ∈ proj₁ (A ─ proj₁ ∅) → x ∈ A
      lemma→ x x∈A─∅ = proj₁ (proj₁ (proj₂ (A ─ proj₁ ∅) x) x∈A─∅)
      lemma← : ∀ x → x ∈ A → x ∈ proj₁ (A ─ proj₁ ∅)
      lemma← x x∈A = proj₂ (proj₂ (A ─ proj₁ ∅) x) (x∈A , proj₂ ∅ x)

  A∩C─A≡∅ : ∀ A C → proj₁ (A ∩ proj₁ (C ─ A)) ≡ proj₁ ∅
  A∩C─A≡∅ A C = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x → x ∈ proj₁ (A ∩ proj₁ (C ─ A)) → x ∈ proj₁ ∅
      lemma→ x x∈A∩C─A
        with proj₁ (proj₂ (A ∩ proj₁ (C ─ A)) x) x∈A∩C─A
      ... | x∈A , x∈C─A
        with  proj₁ (proj₂ (C ─ A) x) x∈C─A
      ... | _ , x∉A = ⊥-elim (x∉A x∈A)
      lemma← : ∀ x → x ∈ proj₁ ∅ → x ∈ proj₁ (A ∩ proj₁ (C ─ A))
      lemma← x x∈∅ = ⊥-elim (proj₂ ∅ x x∈∅)
