module enderton.exercises.Ch2 where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Data.Sum.Base using (_⊎_;inj₁;inj₂;reduce)
  open import Data.Product
    using (proj₁;proj₂;_×_;Σ;∃;∄;_,_;
      Σ-syntax;∃-syntax;∄-syntax)
  open import enderton.Axioms using (set;_∈_;_⊆_;⋃;pow
    ;extensionality;_↔_;_∩_;comprehension;⋂;_∪_
    ;comprehension-syntax;⟨_,_⟩;singleton;Theorem-2A)

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

  -- Exercise 6.a
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

  -- Exercise 6.b
  A⊆pow⋃A : ∀ A → A ⊆ proj₁ (pow (proj₁ (⋃ A)))
  A⊆pow⋃A A {a} a∈A with proj₂ (pow (proj₁ (⋃ A))) a
  ... | _ , h = h x∈a→x∈⋃A
    where
      x∈a→x∈⋃A : ∀ {x} → x ∈ a → x ∈ proj₁ (⋃ A)
      x∈a→x∈⋃A {x} x∈a with proj₂ (⋃ A) x
      ... | _ , H = H (a , a∈A , x∈a)

  -- Exercise 7.a
  powA∩powB≡powA∩B : ∀ A B
    → proj₁ (proj₁ (pow A) ∩ proj₁ (pow B))
      ≡ proj₁ (pow (proj₁ (A ∩ B)))
  powA∩powB≡powA∩B A B = extensionality
    _ _ λ x → lemma→ x , lemma← x
    where
      lemma→ : ∀ x
        → x ∈ proj₁ (proj₁ (pow A) ∩ proj₁ (pow B))
        → x ∈ proj₁ (pow (proj₁ (A ∩ B)))
      lemma→ x x∈powA∩powB
        with proj₂ (proj₁ (pow A) ∩ proj₁ (pow B)) x
      ... | h , _ with h x∈powA∩powB
      ... | x∈powA , x∈powB with proj₂ (pow (proj₁ (A ∩ B))) x
      ... | _ , H = H help
        where
          help : ∀ {y} → y ∈ x → y ∈ proj₁ (A ∩ B)
          help {y} y∈x
            with proj₂ (A ∩ B) y | proj₂ (pow A) x | proj₂ (pow B) x
          ... | _ , hyp | x∈powA→y∈A , _ | x∈powB→y∈B , _
            = hyp (x∈powA→y∈A x∈powA y∈x , x∈powB→y∈B x∈powB y∈x)
      lemma← : ∀ x
        → x ∈ proj₁ (pow (proj₁ (A ∩ B)))
        → x ∈ proj₁ (proj₁ (pow A) ∩ proj₁ (pow B))
      lemma← x x∈powA∩B
        with proj₂ (pow (proj₁ (A ∩ B))) x
          | proj₂ (proj₁ (pow A) ∩ proj₁ (pow B)) x
          | proj₂ (pow A) x | proj₂ (pow B) x
      ... | h , _ | _ , H
          | _ , x⊆A→x∈powA | _ , x⊆B→x∈powB with h x∈powA∩B
      ... | x⊆A∩B = H (x⊆A→x∈powA x⊆A , x⊆B→x∈powB x⊆B)
        where
          x⊆A : x ⊆ A
          x⊆A {y} y∈x with x⊆A∩B y∈x | proj₂ (A ∩ B) y
          ... | y∈A∩B | y∈A∩B→y∈A×y∈B , _ = proj₁ (y∈A∩B→y∈A×y∈B y∈A∩B)
          x⊆B : x ⊆ B
          x⊆B {y} y∈x with x⊆A∩B y∈x | proj₂ (A ∩ B) y
          ... | y∈A∩B | y∈A∩B→y∈A×y∈B , _ = proj₂ (y∈A∩B→y∈A×y∈B y∈A∩B)

  -- Exercise 7.b
  powA∪powB⊆powA∪B : ∀ A B
    → proj₁ (proj₁ (pow A) ∪ proj₁ (pow B))
      ⊆ proj₁ (pow (proj₁ (A ∪ B)))
  powA∪powB⊆powA∪B A B {y} y∈powA∪powB
    with proj₂ (proj₁ (pow A) ∪ proj₁ (pow B)) y
      | proj₂ (pow (proj₁ (A ∪ B))) y
  ... | y∈powA∪powB→y∈powA⊎y∈powB , _
      | _ , y⊆A∪B→y∈powA∪B = y⊆A∪B→y∈powA∪B y⊆A∪B
      where
        y⊆A∪B : y ⊆ proj₁ (A ∪ B)
        y⊆A∪B {x} x∈y with proj₂ (A ∪ B) x | y∈powA∪powB→y∈powA⊎y∈powB y∈powA∪powB
        ... | _ , x∈A⊎x∈B→x∈A∪B | inj₁ y∈powA
          = x∈A⊎x∈B→x∈A∪B (inj₁ (proj₁ (proj₂ (pow A) y) y∈powA x∈y))
        ... | _ , x∈A⊎x∈B→x∈A∪B | inj₂ y∈powB with proj₂ (pow B) y
        ... | y∈powB→y⊆B , _ = x∈A⊎x∈B→x∈A∪B (inj₂ (y∈powB→y⊆B y∈powB x∈y))

  {- Exercise 8.
  Will take the union of the set to
  get the universal set, which will
  contradict Theorem 2A. -}
  ∄∀singleton : ∄[ A ] ∀ a → a ∈ A ↔ ∃[ x ] a ≡ proj₁ (singleton x)
  ∄∀singleton (A , a∈A↔∃[x]a≡singletonx) = Theorem-2A (proj₁ (⋃ A) , ∀z∈⋃A)
    where
      ∀z∈⋃A : ∀ z → z ∈ proj₁ (⋃ A)
      ∀z∈⋃A z with proj₂ (⋃ A) z
      ... | _ , ∃[b]b∈⋃A×z∈b→z∈⋃A
        = ∃[b]b∈⋃A×z∈b→z∈⋃A (proj₁ (singleton z) , singletonz∈A , z∈singletonz)
        where
          singletonz∈A : proj₁ (singleton z) ∈ A
          singletonz∈A with a∈A↔∃[x]a≡singletonx (proj₁ (singleton z))
          ... | _ , ∃[x]singletonz≡singletonx→singletonz∈A
            = ∃[x]singletonz≡singletonx→singletonz∈A (z , refl)
          z∈singletonz : z ∈ proj₁ (singleton z)
          z∈singletonz with proj₂ (singleton z) z
          ... | _ , z≡z→z∈⟨z,z⟩ = z≡z→z∈⟨z,z⟩ refl

  -- Exercise 10.
  a∈B→powa∈powpow⋃B : ∀ a B
    → a ∈ B
    → proj₁ (pow a)
      ∈ proj₁ (pow (proj₁ (pow (proj₁ (⋃ B)))))
  a∈B→powa∈powpow⋃B a B a∈B
    with proj₂ (pow (proj₁ (pow (proj₁ (⋃ B))))) (proj₁ (pow a))
  ... | _ , powa⊆powpow⋃B→powa∈powpow⋃B = powa⊆powpow⋃B→powa∈powpow⋃B powa⊆pow⋃B
    where
      powa⊆pow⋃B : proj₁ (pow a) ⊆ proj₁ (pow (proj₁ (⋃ B)))
      powa⊆pow⋃B {x} x∈powa
        with proj₂ (pow (proj₁ (⋃ B))) x | proj₂ (pow a) x
      ... | _ , x⊆⋃B→x∈powB | x∈powa→x⊆a , _ = x⊆⋃B→x∈powB x⊆⋃B
        where
          x⊆⋃B : x ⊆ proj₁ (⋃ B)
          x⊆⋃B {y} y∈x with proj₂ (⋃ B) y
          ... | _ , ∃[b]b∈x×y∈b→y∈⋃B =
            ∃[b]b∈x×y∈b→y∈⋃B (a , a∈B , x∈powa→x⊆a x∈powa y∈x)
