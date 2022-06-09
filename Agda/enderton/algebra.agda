module enderton.algebra where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)
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
  ∪-assoc A B C = {!!}

  ∩-assoc : ∀ A B C
    → proj₁ (A ∩ proj₁ (B ∩ C)) ≡ proj₁ (proj₁ (A ∩ B) ∩ C)
  ∩-assoc A B C = {!!}

  -- Distributive Laws.

  ∩-distr-∪ : ∀ A B C
    → proj₁ (A ∩ proj₁ (B ∪ C)) ≡ proj₁ (proj₁ (A ∩ B) ∪ proj₁ (A ∩ C))
  ∩-distr-∪ A B C = {!!}

  ∪-distr-∩ : ∀ A B C
    → proj₁ (A ∪ proj₁ (B ∩ C)) ≡ proj₁ (proj₁ (A ∪ B) ∩ proj₁ (A ∪ C))
  ∪-distr-∩ A B C = {!!}

  -- De Morgan's Laws.

  C─A∪B≡C─A∪C─B : ∀ A B C
    → proj₁ (C ─ proj₁ (A ∪ B)) ≡ proj₁ (proj₁ (C ─ A) ∪ proj₁ (C ─ B))
  C─A∪B≡C─A∪C─B A B C = {!!}

  C─A∩B≡C─A∩C─B : ∀ A B C
    → proj₁ (C ─ proj₁ (A ∩ B)) ≡ proj₁ (proj₁ (C ─ A) ∩ proj₁ (C ─ B))
  C─A∩B≡C─A∩C─B A B C = {!!}

  -- Identities.

  A∪∅≡A : ∀ A → proj₁ (A ∪ proj₁ ∅) ≡ A
  A∪∅≡A A = {!!}

  A∩∅≡A : ∀ A → proj₁ (A ∩ proj₁ ∅) ≡ proj₁ ∅
  A∩∅≡A A = {!!}

  A─∅≡A : ∀ A → proj₁ (A ─ proj₁ ∅) ≡ A
  A─∅≡A A = {!!}

  A∩C─A≡∅ : ∀ A C → proj₁ (proj₁ (A ∩ C) ─ A) ≡ proj₁ ∅
  A∩C─A≡∅ A C = {!!}
