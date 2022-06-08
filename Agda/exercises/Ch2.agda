module exercises.Ch2 where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Data.Product
    using (proj₁;proj₂;_×_;Σ;∃;∄;_,_;
      Σ-syntax;∃-syntax;∄-syntax)
  open import Axioms using (set;_∈_;_⊆_;⋃;pow
    ;extensionality;_↔_;_∩_)

  {-
  exer-2 : ¬ (∀ A B → (proj₁ (⋃ A) ≡ proj₁ (⋃ B)) → A ≡ B)
  exer-2 h = {!!}
  Consider ⋃ {{1,2},{3}} ≡ ⋃ {{1},{2,3}},
  but {{1,2},{3}} ≢ {{1},{2,3}}. -}

  -- Exercise 3.
  a∈A→a⊆⋃A : ∀ A a → a ∈ A → a ⊆ proj₁ (⋃ A)
  a∈A→a⊆⋃A A a a∈A {x} x∈a with proj₂ (⋃ A) x
  ... | _ , h = h (a , a∈A , x∈a)

  -- Exercise 4.
  A⊆B→⋃A⊆⋃B : ∀ A B → A ⊆ B → proj₁ (⋃ A) ⊆ proj₁ (⋃ B)
  A⊆B→⋃A⊆⋃B A B A⊆B {z} a∈⋃A
    with proj₂ (⋃ A) z | proj₂ (⋃ B) z
  ... | hA , _ | _ , hB with hA a∈⋃A
  ... | a , a∈A , z∈a = hB (a , A⊆B a∈A , z∈a)

  -- Exercise 5.
  ⋃A⊆B : ∀ A B → (∀ a → a ∈ A → a ⊆ B) → proj₁ (⋃ A) ⊆ B
  ⋃A⊆B A B a∈A→a⊆B {z} z∈⋃A with proj₂ (⋃ A) z
  ... | h , _ with h z∈⋃A
  ... | y , y∈A , z∈y = a∈A→a⊆B _ y∈A z∈y

  A⊆A : ∀ A → A ⊆ A
  A⊆A A a∈A = a∈A

  A∈powA : ∀ A → A ∈ proj₁ (pow A)
  A∈powA A with proj₂ (pow A) A
  ... | _ , A⊆A→A∈powA = A⊆A→A∈powA λ x⊆A → x⊆A

  -- Exercise 6.
  ⋃powA≡A : ∀ A → proj₁ (⋃ (proj₁ (pow A))) ≡ A
  ⋃powA≡A A = extensionality _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x → x ∈ proj₁ (⋃ (proj₁ (pow A))) → x ∈ A
      lemma→ x x∈⋃powA with proj₂ (⋃ (proj₁ (pow A))) x
      ... | h , _ with h x∈⋃powA
      ... | z , z∈powA , x∈z with proj₂ (pow A) z
      ... | z∈powA→x∈z→x∈A , _ = z∈powA→x∈z→x∈A z∈powA x∈z
      lemma← : ∀ x → x ∈ A → x ∈ proj₁ (⋃ (proj₁ (pow A)))
      lemma← x x∈A with proj₂ (⋃ (proj₁ (pow A))) x
      ... | _ , h = h (A , A∈powA A , x∈A)

  A⊆pow⋃A : ∀ A → A ⊆ proj₁ (pow (proj₁ (⋃ A)))
  A⊆pow⋃A A {a} a∈A with proj₂ (pow (proj₁ (⋃ A))) a
  ... | _ , h = h x∈a→x∈⋃A
    where
      x∈a→x∈⋃A : ∀ {x} → x ∈ a → x ∈ proj₁ (⋃ A)
      x∈a→x∈⋃A {x} x∈a with proj₂ (⋃ A) x
      ... | _ , H = H (a , a∈A , x∈a)

  -- Exercise 7
  powA∩powB≡powA∩B : ∀ A B → proj₁ (proj₁ (pow A) ∩ proj₁ (pow B)) ≡ proj₁ (pow (proj₁ (A ∩ B)))
  powA∩powB≡powA∩B A B = {!!}
