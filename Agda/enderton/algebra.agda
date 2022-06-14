module enderton.algebra where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contraposition;¬∃⟶∀¬;∀⟶¬∃¬)
  open import Data.Sum.Base using (_⊎_;inj₁;inj₂;reduce)
  open import Data.Product
    using (proj₁;proj₂;_×_;Σ;∃;∄;_,_;
      Σ-syntax;∃-syntax;∄-syntax)
  open import enderton.axioms using (set;_∈_;_∉_;_⊆_;⋃;pow
    ;extensionality;_↔_;_∩_;comprehension;⋂;_∪_
    ;comprehension-syntax;⟨_,_⟩;singleton;Theorem-2A
    ;_─_;∅)
  open import enderton.exercises.ch2
    using (A∈powA;a∈A→a⊆⋃A)

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

  -- De Morgan's Laws.
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

  C─A∪C─B⊆C─A∩B : ∀ {A B C}
    → proj₁ (proj₁ (C ─ A) ∪ proj₁ (C ─ B))
      ⊆ proj₁ (C ─ proj₁ (A ∩ B))
  C─A∪C─B⊆C─A∩B {A} {B} {C} {x} x∈C─A∪C─B
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

  -- Properties of [_⊆_].

  -- Reflexivity.
  A⊆A : ∀ A → A ⊆ A
  A⊆A A {x} x∈A = x∈A

  -- Transitivity.
  A⊆B→B⊆C→A⊆C : ∀ {A B C}
    → A ⊆ B → B ⊆ C → A ⊆ C
  A⊆B→B⊆C→A⊆C A⊆B B⊆C {x} x∈A = B⊆C (A⊆B x∈A)

  -- Anti-symmetry.
  A⊆B→B⊆A→A≡B : ∀ {A B}
    → A ⊆ B → B ⊆ A → A ≡ B
  A⊆B→B⊆A→A≡B {A} {B} A⊆B B⊆A =
    extensionality _ _ λ x → A⊆B {x} , B⊆A {x}

  A⊆B→x∉B→x∉A : ∀ {A B x}
    → A ⊆ B → x ∉ B → x ∉ A
  A⊆B→x∉B→x∉A {A} {B} {x} A⊆B x∉B x∈A = x∉B (A⊆B x∈A)

  A⊆B→C─B⊆C─A : ∀ {A B C}
    → A ⊆ B → proj₁ (C ─ B) ⊆ proj₁ (C ─ A)
  A⊆B→C─B⊆C─A {A} {B} {C} A⊆B {x} x∈C─B
    with proj₁ (proj₂ (C ─ B) x) x∈C─B
  ... | x∈C , x∉B = proj₂ (proj₂ (C ─ A) x) (x∈C , A⊆B→x∉B→x∉A A⊆B x∉B)

  A⊆B→∃[a]a∈A→∃[b]b∈B : ∀ {A B}
    → A ⊆ B → (∃[ a ] a ∈ A) → ∃[ b ] b ∈ B
  A⊆B→∃[a]a∈A→∃[b]b∈B {A} {B} A⊆B (a , a∈A) = a , (A⊆B a∈A)

  A⊆B→⋂B⊆⋂A : ∀ {A B} (A⊆B : A ⊆ B) (∃a∈A : ∃[ a ] a ∈ A)
    → proj₁ (⋂ B (A⊆B→∃[a]a∈A→∃[b]b∈B A⊆B ∃a∈A)) ⊆ proj₁ (⋂ A ∃a∈A)
  A⊆B→⋂B⊆⋂A {A} {B} A⊆B ∃a∈A {x} x∈⋂B
    with proj₁
      (proj₂ (⋂ B (A⊆B→∃[a]a∈A→∃[b]b∈B A⊆B ∃a∈A)) x)
      x∈⋂B
  ... | b∈B→x∈b = proj₂
    (proj₂ (⋂ A ∃a∈A) x)
    λ a a∈A → b∈B→x∈b a (A⊆B a∈A)

  B⊆C→A∩B⊆A∩C : ∀ {A B C}
    → B ⊆ C → proj₁ (A ∩ B) ⊆ proj₁ (A ∩ C)
  B⊆C→A∩B⊆A∩C {A} {B} {C} B⊆C {x} x∈A∩B
    with proj₁ (proj₂ (A ∩ B) x) x∈A∩B
  ... | x∈A , x∈B = proj₂ (proj₂ (A ∩ C) x) (x∈A , (B⊆C x∈B))

  A⊆B→A∩C⊆B∩C : ∀ {A B C}
    → A ⊆ B → proj₁ (A ∩ C) ⊆ proj₁ (B ∩ C)
  A⊆B→A∩C⊆B∩C {A} {B} {C} A⊆B
    rewrite A∩B≡B∩A A C | A∩B≡B∩A B C = B⊆C→A∩B⊆A∩C A⊆B

  A⊆B→C⊆D→A∩C⊆B∩D : ∀ {A B C D}
    → A ⊆ B → C ⊆ D → proj₁ (A ∩ C) ⊆ proj₁ (B ∩ D)
  A⊆B→C⊆D→A∩C⊆B∩D {A} {B} {C} {D} A⊆B C⊆D =
    A⊆B→B⊆C→A⊆C {B = proj₁ (B ∩ C)}
      (A⊆B→A∩C⊆B∩C A⊆B) (B⊆C→A∩B⊆A∩C C⊆D)

  B⊆C→A∪B⊆A∪C : ∀ {A B C}
    → B ⊆ C → proj₁ (A ∪ B) ⊆ proj₁ (A ∪ C)
  B⊆C→A∪B⊆A∪C {A} {B} {C} B⊆C {x} x∈A∪B
    with proj₁ (proj₂ (A ∪ B) x) x∈A∪B
  ... | inj₁ x∈A = proj₂ (proj₂ (A ∪ C) x) (inj₁ x∈A)
  ... | inj₂ x∈B = proj₂ (proj₂ (A ∪ C) x) (inj₂ (B⊆C x∈B))

  A⊆B→A∪C⊆B⊆C : ∀ {A} {B} {C}
    → A ⊆ B → proj₁ (A ∪ C) ⊆ proj₁ (B ∪ C)
  A⊆B→A∪C⊆B⊆C {A} {B} {C} A⊆B
    rewrite A∪B≡B∪A A C | A∪B≡B∪A B C = B⊆C→A∪B⊆A∪C A⊆B

  A⊆B→C⊆D→A∪C⊆B∪D : ∀ {A} {B} {C} {D}
    → A ⊆ B → C ⊆ D → proj₁ (A ∪ C) ⊆ proj₁ (B ∪ D)
  A⊆B→C⊆D→A∪C⊆B∪D {A} {B} {C} {D} A⊆B C⊆D = A⊆B→B⊆C→A⊆C
    {B = proj₁ (B ∪ C)} (A⊆B→A∪C⊆B⊆C A⊆B) (B⊆C→A∪B⊆A∪C C⊆D)

  C─A⊆C : ∀ C A → proj₁ (C ─ A) ⊆ C
  C─A⊆C C A {x} x∈C─A = proj₁ (proj₁ (proj₂ (C ─ A) _) x∈C─A)

  -- General distributive laws.

  A∩⋃B≡⋃[t∈powA∩⋃B∣∃X∈B×t≡A∩X] : ∀ A B
    → proj₁ (A ∩ proj₁ (⋃ B))
      ≡ proj₁ (⋃ (proj₁
        [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
        ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ]))
  A∩⋃B≡⋃[t∈powA∩⋃B∣∃X∈B×t≡A∩X] A B =
    extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x →
        x ∈ (proj₁ (A ∩ proj₁ (⋃ B)))
          → x ∈ proj₁ (⋃ (proj₁
              [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
              ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ]))
      lemma→ x x∈A∩⋃B
        with proj₁ (proj₂ (A ∩ proj₁ (⋃ B)) x) x∈A∩⋃B
      ... | x∈A , x∈⋃B with proj₁ (proj₂ (⋃ B) x) x∈⋃B
      ... | y , y∈B , x∈y = proj₂
        (proj₂ (⋃ (proj₁
          [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ])) x)
          (proj₁ (A ∩ y)
          , proj₂ (proj₂ [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
            ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ] _)
            (proj₂ (proj₂ (pow (proj₁ (A ∩ proj₁ (⋃ B)))) _)
              (B⊆C→A∩B⊆A∩C (a∈A→a⊆⋃A _ _ y∈B))
            , y , y∈B , refl)
          , proj₂ (proj₂ (A ∩ y) x) (x∈A , x∈y))
      lemma← : ∀ x →
        x ∈ proj₁ (⋃ (proj₁
          [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ]))
          → x ∈ (proj₁ (A ∩ proj₁ (⋃ B)))
      lemma← x x∈⋃[t∈powA∩⋃B∣∃X∈B×t≡A∩X]
        with proj₁
          (proj₂ (⋃ (proj₁
          [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ])) x)
          x∈⋃[t∈powA∩⋃B∣∃X∈B×t≡A∩X]
      ... | a , a∈[t∈powA∩⋃B∣∃X∈B×t≡A∩X] , x∈a
        with proj₁
          (proj₂ [ t ∈ proj₁ (pow (proj₁ (A ∩ proj₁ (⋃ B))))
            ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∩ X) ] a)
          a∈[t∈powA∩⋃B∣∃X∈B×t≡A∩X]
      ... | a∈powA∩⋃B , b , b∈B , refl
        with proj₁ (proj₂ (A ∩ b) x) x∈a
      ... | x∈A , x∈b = proj₂
        (proj₂ (A ∩ proj₁ (⋃ B)) x)
        (x∈A , proj₂ (proj₂ (⋃ B) x) (b , b∈B , x∈b))

  ∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] : ∀ A B
    → (∃[ b ] b ∈ B)
    → ∃[ b ] b ∈ proj₁
        [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
        ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ]
  ∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A B (b , b∈B) =
    proj₁ (A ∪ b) , proj₂ (proj₂ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
      ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ] _)
      (proj₂ (proj₂ (pow (proj₁ (A ∪ proj₁ (⋃ B)))) _)
        (B⊆C→A∪B⊆A∪C (a∈A→a⊆⋃A _ _ b∈B))
      , b , b∈B , refl)

  A∪⋂B⊆⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X] : ∀ A B (∃b∈B : ∃[ b ] b ∈ B)
    → proj₁ (A ∪ proj₁ (⋂ B ∃b∈B))
      ⊆ proj₁ (⋂ (proj₁
        [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
        ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ])
        (∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A _ ∃b∈B))
  A∪⋂B⊆⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A B ∃b∈B {x} x∈A∪⋂B
    with proj₁ (proj₂ (A ∪ proj₁ (⋂ B ∃b∈B)) x) x∈A∪⋂B
  ... | inj₁ x∈A = proj₂
    (proj₂ (⋂ (proj₁
      [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
        ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ])
        (∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A _ ∃b∈B)) _) helper
   where
     helper : ∀ a
       → a ∈ proj₁ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
         ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ]
       → x ∈ a
     helper a a∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X]
       with proj₁
         (proj₂ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
           ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ] a)
         a∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X]
     ... | A∪b∈powA∪⋃B , b , b∈B , refl = proj₂ (proj₂ (A ∪ b) x) (inj₁ x∈A)
  ... | inj₂ x∈⋂B = proj₂ (proj₂ (⋂ (proj₁
    [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
      ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ])
        (∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A _ ∃b∈B)) _) helper
    where
      helper : ∀ a
        → a ∈ proj₁ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ]
        → x ∈ a
      helper a a∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X]
        with proj₁
          (proj₂ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
            ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ] a)
          a∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X]
         | proj₁ (proj₂ (⋂ B ∃b∈B) x) x∈⋂B
      ... | A∪b∈powA∪⋃B , b , b∈B , refl
          | b∈B→x∈b = proj₂ (proj₂ (A ∪ b) x) (inj₂ (b∈B→x∈b _ b∈B))

  x∉⋃A→a∈A→x∉a : ∀ {x A a}
    → x ∉ proj₁ (⋃ A) → a ∈ A → x ∉ a
  x∉⋃A→a∈A→x∉a {x} {A} {a} x∉proj₁⋃A a∈A x∈a =
    x∉proj₁⋃A (proj₂ (proj₂ (⋃ A) _) (a , a∈A , x∈a))

  ∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] : ∀ A C
    → (∃[ a ] a ∈ A)
    → ∃[ z ] z ∈ proj₁ [ t ∈ proj₁ (pow C) ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ]
  ∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] A C (a , a∈A) =
    proj₁ (C ─ a)
    , proj₂ (proj₂
      [ t ∈ proj₁ (pow C)
        ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ] _)
        (proj₂ (proj₂ (pow C) _) (C─A⊆C _ _) , a , a∈A , refl)

  -- General De Morgan.
  
  C─⋃A≡⋂[t∈powC∣∃X∈A×t≡C─X] : ∀ C A (∃a∈A : ∃[ a ] a ∈ A)
    → proj₁ (C ─ proj₁ (⋃ A))
      ≡ proj₁ (⋂ (proj₁ [ t ∈ proj₁ (pow C)
        ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ])
        (∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] _ _ ∃a∈A))
  C─⋃A≡⋂[t∈powC∣∃X∈A×t≡C─X] C A ∃a∈A = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (C ─ proj₁ (⋃ A))
        → x ∈ proj₁ (⋂ (proj₁
          [ t ∈ proj₁ (pow C)
          ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ])
          (∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] _ _ ∃a∈A))
      lemma→ x x∈C─⋃A
        with proj₁
          (proj₂ (C ─ proj₁ (⋃ A)) x)
          x∈C─⋃A
      ... | x∈C , x∉⋃A = proj₂
        (proj₂ (⋂ (proj₁
          [ t ∈ proj₁ (pow C)
          ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ])
          (∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] _ _ ∃a∈A)) _)
        λ c c∈[t∈powC∣∃X∈A×t≡C─X] → c∈[t∈powC∣∃X∈A×t≡C─X]→x∈c c∈[t∈powC∣∃X∈A×t≡C─X]
        where
          c∈[t∈powC∣∃X∈A×t≡C─X]→x∈c : ∀ {c}
            → c ∈ proj₁ [ t ∈ proj₁ (pow C) ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ]
            → x ∈ c
          c∈[t∈powC∣∃X∈A×t≡C─X]→x∈c {c} c∈[t∈powC∣∃X∈A×t≡C─X]
            with proj₁
              (proj₂
                [ t ∈ proj₁ (pow C)
                  ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ] c)
              c∈[t∈powC∣∃X∈A×t≡C─X]
          ... | c∈powC , a , a∈A , refl = proj₂
            (proj₂ (C ─ a) _) (x∈C , x∉⋃A→a∈A→x∉a x∉⋃A a∈A)
      lemma← : ∀ x
        → x ∈ proj₁ (⋂ (proj₁
          [ t ∈ proj₁ (pow C)
            ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ])
            (∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] _ _ ∃a∈A))
        → x ∈ proj₁ (C ─ proj₁ (⋃ A))
      lemma← x x∈⋂[t∈powC∣∃X∈A×t≡C─X]
        with proj₁
          (proj₂ (⋂ (proj₁
          [ t ∈ proj₁ (pow C)
          ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ])
          (∃a∈A→∃z∈[t∈powC∣∃X∈A×t≡C─X] _ _ ∃a∈A)) x)
          x∈⋂[t∈powC∣∃X∈A×t≡C─X]
      ... | ∀z∈[t∈powC∣∃X∈A×t≡C─X]→x∈z = proj₂
          (proj₂ (C ─ proj₁ (⋃ A)) _) (x∈C ∃a∈A , x∉⋃A)
        where
          ∀a∈A→x∈C─a : ∀ {a}
            → a ∈ A → x ∈ proj₁ (C ─ a)
          ∀a∈A→x∈C─a {a} a∈A = ∀z∈[t∈powC∣∃X∈A×t≡C─X]→x∈z
            (proj₁ (C ─ a))
            (proj₂ (proj₂
              [ t ∈ proj₁ (pow C)
                ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X) ] _)
                (proj₂ (proj₂ (pow C) _) (C─A⊆C _ _)
                , a , (a∈A , refl)))
          x∈C : (∃[ a ] a ∈ A) → x ∈ C
          x∈C (a , a∈A)
            with proj₁ (proj₂ (C ─ a) _) (∀a∈A→x∈C─a a∈A)
          ... | x∈C , _ = x∈C
          x∉⋃A : x ∉ proj₁ (⋃ A)
          x∉⋃A x∈⋃A with proj₁ (proj₂ (⋃ A) _) x∈⋃A
          ... | a , a∈A , x∈a with proj₁ (proj₂ (C ─ a) _) (∀a∈A→x∈C─a a∈A)
          ... | _ , x∉a = x∉a x∈a

  ⋃[t∈powC∣∃X∈A×t≡C─A]⊆C─⋂A : ∀ {C A} {∃a∈A : ∃[ a ] a ∈ A}
    → proj₁ (⋃ (proj₁ [ t ∈ proj₁ (pow C) ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)]))
      ⊆ proj₁ (C ─ proj₁ (⋂ A ∃a∈A))
  ⋃[t∈powC∣∃X∈A×t≡C─A]⊆C─⋂A {C} {A} {∃a∈A} {x} x∈⋃[t∈powC∣∃X∈A×t≡C─X]
    with proj₁
      (proj₂ (⋃ (proj₁ [ t ∈ proj₁ (pow C)
        ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)])) x)
      x∈⋃[t∈powC∣∃X∈A×t≡C─X]
  ... | c , c∈[t∈powC∣∃X∈A×t≡C─A] , x∈c
    with proj₁
      (proj₂ [ t ∈ proj₁ (pow C)
        ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)] c)
      c∈[t∈powC∣∃X∈A×t≡C─A]
  ... | c∈powC , a , a∈A , refl = proj₂
    (proj₂ (C ─ proj₁ (⋂ A ∃a∈A)) _)
    (proj₁ (proj₂ (pow C) _) c∈powC x∈c , λ x∈⋂A → help x∈⋂A)
    where
      help : x ∉ proj₁ (⋂ A ∃a∈A)
      help x∈⋂A with proj₁ (proj₂ (⋂ A ∃a∈A) _) x∈⋂A
      ... | ∀a∈A→x∈a with proj₁ (proj₂ (C ─ a) _) x∈c
      ... | _ , x∉a = x∉a (∀a∈A→x∈a _ a∈A)

  -- Theorems that require excluded middle.
  module lemmas-rem
    (P⊎¬P : ∀ (P : Set) → P ⊎ ¬ P) where
    open import enderton.exm
    open enderton.exm.rem (P⊎¬P) using (¬∀→∃¬;¬P→Q⟶P×¬Q)

    x∉A∩B→x∉A⊎x∉B : ∀ {A B x}
      → x ∉ proj₁ (A ∩ B) → x ∉ A ⊎ x ∉ B
    x∉A∩B→x∉A⊎x∉B {A} {B} {x} x∉A∩B with P⊎¬P (x ∈ A)
    ... | inj₂ x∉A = inj₁ x∉A
    ... | inj₁ x∈A with P⊎¬P (x ∈ B)
    ... | inj₂ x∉B = inj₂ x∉B
    ... | inj₁ x∈B = ⊥-elim (x∉A∩B (proj₂ (proj₂ (A ∩ B) x) (x∈A , x∈B)))

    x∉⋂A→∃a∈A×x∉a : ∀ {A x} {∃a∈A : ∃[ a ] a ∈ A}
      → x ∉ proj₁ (⋂ A ∃a∈A) → ∃[ a ] a ∈ A × x ∉ a
    x∉⋂A→∃a∈A×x∉a {A} {x} {∃a∈A} x∉⋂A
      with contraposition (proj₂ (proj₂ (⋂ A ∃a∈A) x)) x∉⋂A
    ... | ¬∀a∈A→a∈A with ¬∀→∃¬ ¬∀a∈A→a∈A
    ... | a , ¬a∈A→x∈a = a , ¬P→Q⟶P×¬Q ¬a∈A→x∈a

    -- De Morgan's Laws.
    C─A∩B≡C─A∪C─B : ∀ A B C
      → proj₁ (C ─ proj₁ (A ∩ B)) ≡ proj₁ (proj₁ (C ─ A) ∪ proj₁ (C ─ B))
    C─A∩B≡C─A∪C─B A B C = extensionality _ _ λ x → lemma→ x , C─A∪C─B⊆C─A∩B {x = x}
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

    -- General distributive law.
    A∪⋂B≡⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X] : ∀ A B (∃b∈B : ∃[ b ] b ∈ B)
      → proj₁ (A ∪ proj₁ (⋂ B ∃b∈B))
        ≡ proj₁ (⋂ (proj₁
          [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ])
          (∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A _ ∃b∈B))
    A∪⋂B≡⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A B ∃b∈B = extensionality
      _ _ λ x → A∪⋂B⊆⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A B ∃b∈B {x} , lemma← x
      where
        lemma← : ∀ x
          → x ∈ proj₁ (⋂ (proj₁
            [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
              ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ])
            (∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A _ ∃b∈B))
          → x ∈ proj₁ (A ∪ proj₁ (⋂ B ∃b∈B))
        lemma← x x∈⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X]
          with proj₁
            (proj₂ (⋂ (proj₁
              [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
              ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ])
            (∃b∈B→∃b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] A _ ∃b∈B)) x)
            x∈⋂[t∈powA∪⋂B∣∃X∈B×t≡A∪X]
        ... | ∀a∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X]→x∈a = proj₂
          (proj₂ (A ∪ proj₁ (⋂ B ∃b∈B)) _)
          x∈A⊎x∈⋂B
          where
            x∈A⊎x∈⋂B : x ∈ A ⊎ x ∈ proj₁ (⋂ B ∃b∈B)
            x∈A⊎x∈⋂B with P⊎¬P (x ∈ A)
            ... | inj₁ x∈A = inj₁ x∈A
            ... | inj₂ x∉A = inj₂ (proj₂ (proj₂ (⋂ B ∃b∈B) _) ∀b∈B→x∈b)
              where
                ∀b∈B→x∈b : ∀ b → b ∈ B → x ∈ b
                ∀b∈B→x∈b b b∈B = x∈b
                  where
                    A∪b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] :
                      proj₁ (A ∪ b) ∈
                        proj₁ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
                          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ]
                    A∪b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X] = proj₂
                      (proj₂ [ t ∈ proj₁ (pow (proj₁ (A ∪ proj₁ (⋃ B))))
                          ∣ ∃[ X ] X ∈ B × t ≡ proj₁ (A ∪ X) ] _)
                      (proj₂
                        (proj₂ (pow (proj₁ (A ∪ proj₁ (⋃ B)))) _)
                        (B⊆C→A∪B⊆A∪C (a∈A→a⊆⋃A _ _ b∈B))
                      , b , b∈B , refl)
                    x∈b : x ∈ b
                    x∈b with
                      proj₁ (proj₂ (A ∪ b) _)
                      (∀a∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X]→x∈a _
                        A∪b∈[t∈powA∪⋂B∣∃X∈B×t≡A∪X])
                    ... | inj₁ x∈A = ⊥-elim (x∉A x∈A)
                    ... | inj₂ x∈b = x∈b

    -- General De Morgan's Law.
    C─⋂A≡⋃[t∈powC∣∃X∈A×t≡C─A] : ∀ C A (∃a∈A : ∃[ a ] a ∈ A)
      → proj₁ (C ─ proj₁ (⋂ A ∃a∈A))
        ≡ proj₁ (⋃ (proj₁ [ t ∈ proj₁ (pow C) ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)]))
    C─⋂A≡⋃[t∈powC∣∃X∈A×t≡C─A] C A ∃a∈A =
      extensionality _ _ λ x → lemma→ x
        , ⋃[t∈powC∣∃X∈A×t≡C─A]⊆C─⋂A {∃a∈A = ∃a∈A} {x = x}
      where
        lemma→ : ∀ x
          → x ∈ proj₁ (C ─ proj₁ (⋂ A ∃a∈A))
          → x ∈ proj₁ (⋃ (proj₁ [ t ∈ proj₁ (pow C)
            ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)]))
        lemma→ x x∈C─⋂A
          with proj₁
            (proj₂ (C ─ proj₁ (⋂ A ∃a∈A)) x)
            x∈C─⋂A
        ... | x∈C , x∉⋂A with x∉⋂A→∃a∈A×x∉a {∃a∈A = ∃a∈A} x∉⋂A
        ... | a , a∈A , x∉a = proj₂
          (proj₂
            (⋃ (proj₁ [ t ∈ proj₁ (pow C)
              ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)])) _)
          (_ , proj₂ (proj₂ [ t ∈ proj₁ (pow C)
             ∣ ∃[ X ] X ∈ A × t ≡ proj₁ (C ─ X)] (proj₁ (C ─ a)))
               (proj₂ (proj₂ (pow C) _) (C─A⊆C _ _) , a , a∈A , refl)
               , proj₂ (proj₂ (C ─ a) _) (x∈C , x∉a))
