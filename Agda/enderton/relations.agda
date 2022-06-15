module enderton.relations where
  open import Agda.Builtin.Equality using (_≡_;refl)
  open import Relation.Binary.PropositionalEquality.Core using (_≢_;sym;cong)
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

  A≡B→x∈A↔x∈B : ∀ {A B}
    → A ≡ B → ∀ x → x ∈ A ↔ x ∈ B
  A≡B→x∈A↔x∈B {A} {.A} refl x = (λ x∈A → x∈A) , λ x∈A → x∈A

  -- Ordered pairs (Kazimierz Kuratowski).
  <_,_> : set → set → set
  < A , B > = proj₁ ⟨ proj₁ (singleton A) , proj₁ ⟨ A , B ⟩ ⟩

  singletonA∈<A,B> : ∀ A B
    → proj₁ (singleton A) ∈ < A , B >
  singletonA∈<A,B> A B = proj₂ (proj₂
    ⟨ proj₁ (singleton A) , proj₁ ⟨ A , B ⟩ ⟩ _) (inj₁ refl)

  ⟨A,B⟩∈<A,B> : ∀ A B
    → proj₁ ⟨ A , B ⟩ ∈ < A , B >
  ⟨A,B⟩∈<A,B> A B = proj₂ (proj₂
    ⟨ proj₁ (singleton A) , proj₁ ⟨ A , B ⟩ ⟩ _) (inj₂ refl)

  x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ : ∀ {A B x}
    → x ∈ < A , B > → x ≡ proj₁ (singleton A) ⊎ x ≡ proj₁ ⟨ A , B ⟩
  x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ {A} {B} {x} x∈<A,B> =
    proj₁ (proj₂ ⟨ proj₁ (singleton A) , proj₁ ⟨ A , B ⟩ ⟩ _) x∈<A,B>

  singletonA≡singletonB→A≡B : ∀ {A B}
    → proj₁ (singleton A) ≡ proj₁ (singleton B) → A ≡ B
  singletonA≡singletonB→A≡B {A} {B} singletonA≡singletonB = A≡B
    where
      A∈singletonA = proj₂ (proj₂ (singleton A) A) refl
      B∈singletonB = proj₂ (proj₂ (singleton B) B) refl
      A∈singletonB = proj₁ (A≡B→x∈A↔x∈B singletonA≡singletonB A) A∈singletonA
      A≡B : A ≡ B
      A≡B with proj₁ (proj₂ (singleton B) _) A∈singletonB
      ... | refl = refl

  ⟨A,B⟩⊆⟨B,A⟩ : ∀ A B → proj₁ ⟨ A , B ⟩ ⊆ proj₁ ⟨ B , A ⟩
  ⟨A,B⟩⊆⟨B,A⟩ A B {x} x∈⟨A,B⟩
    with proj₁ (proj₂ ⟨ A , B ⟩ _) x∈⟨A,B⟩
  ... | inj₁ refl = proj₂ (proj₂ ⟨ B , A ⟩ _) (inj₂ refl)
  ... | inj₂ refl = proj₂ (proj₂ ⟨ B , A ⟩ _) (inj₁ refl)

  ⟨A,B⟩≡⟨B,A⟩ : ∀ A B → proj₁ ⟨ A , B ⟩ ≡ proj₁ ⟨ B , A ⟩
  ⟨A,B⟩≡⟨B,A⟩ A B = extensionality
    _ _ λ x → (⟨A,B⟩⊆⟨B,A⟩ A B {x}) , (⟨A,B⟩⊆⟨B,A⟩ B A {x})

  singletonA≡⟨B,C⟩→A≡B×A≡C : ∀ {A B C}
    → proj₁ (singleton A) ≡ proj₁ ⟨ B , C ⟩ → A ≡ B × A ≡ C
  singletonA≡⟨B,C⟩→A≡B×A≡C {A} {B} {C} singletonA≡⟨B,C⟩ = A≡B , A≡C
    where
      B∈⟨B,C⟩ = proj₂ (proj₂ ⟨ B , C ⟩ B) (inj₁ refl)
      C∈⟨B,C⟩ = proj₂ (proj₂ ⟨ B , C ⟩ C) (inj₂ refl)
      B∈singletonA = proj₂ (A≡B→x∈A↔x∈B singletonA≡⟨B,C⟩ B) B∈⟨B,C⟩
      C∈singletonA = proj₂ (A≡B→x∈A↔x∈B singletonA≡⟨B,C⟩ C) C∈⟨B,C⟩
      A≡B : A ≡ B
      A≡B with proj₁ (proj₂ (singleton A) B) B∈singletonA
      ... | refl = refl
      A≡C : A ≡ C
      A≡C with proj₁ (proj₂ (singleton A) C) C∈singletonA
      ... | refl = refl
    
  ⟨A,B⟩≡⟨C,D⟩→A≡C×B≡D⊎A≡D×B≡C : ∀ {A B C D}
    → proj₁ ⟨ A , B ⟩ ≡ proj₁ ⟨ C , D ⟩ → A ≡ C × B ≡ D ⊎ A ≡ D × B ≡ C
  ⟨A,B⟩≡⟨C,D⟩→A≡C×B≡D⊎A≡D×B≡C {A} {B} {C} {D} ⟨A,B⟩≡⟨C,D⟩ = help
    where
      A∈⟨A,B⟩ = proj₂ (proj₂ ⟨ A , B ⟩ A) (inj₁ refl)
      A∈⟨C,D⟩ = proj₁ (A≡B→x∈A↔x∈B ⟨A,B⟩≡⟨C,D⟩ A) A∈⟨A,B⟩
      B∈⟨A,B⟩ = proj₂ (proj₂ ⟨ A , B ⟩ B) (inj₂ refl)
      B∈⟨C,D⟩ = proj₁ (A≡B→x∈A↔x∈B ⟨A,B⟩≡⟨C,D⟩ B) B∈⟨A,B⟩
      C∈⟨C,D⟩ = proj₂ (proj₂ ⟨ C , D ⟩ C) (inj₁ refl)
      C∈⟨A,B⟩ = proj₂ (A≡B→x∈A↔x∈B ⟨A,B⟩≡⟨C,D⟩ C) C∈⟨C,D⟩
      D∈⟨C,D⟩ = proj₂ (proj₂ ⟨ C , D ⟩ D) (inj₂ refl)
      D∈⟨A,B⟩ = proj₂ (A≡B→x∈A↔x∈B ⟨A,B⟩≡⟨C,D⟩ D) D∈⟨C,D⟩
      help : A ≡ C × B ≡ D ⊎ A ≡ D × B ≡ C
      help with proj₁ (proj₂ ⟨ C , D ⟩ _)  A∈⟨C,D⟩
        | proj₁ (proj₂ ⟨ C , D ⟩ _) B∈⟨C,D⟩
        | proj₁ (proj₂ ⟨ A , B ⟩ _) C∈⟨A,B⟩
        | proj₁ (proj₂ ⟨ A , B ⟩ _ ) D∈⟨A,B⟩
      ... | inj₁ refl | inj₁ refl | inj₁ refl | inj₁ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₁ refl | inj₁ refl | inj₂ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₁ refl | inj₂ refl | inj₁ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₁ refl | inj₂ refl | inj₂ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₂ refl | inj₁ refl | inj₁ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₂ refl | inj₁ refl | inj₂ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₂ refl | inj₂ refl | inj₁ refl = inj₁ (refl , refl)
      ... | inj₁ refl | inj₂ refl | inj₂ refl | inj₂ refl = inj₁ (refl , refl)
      ... | inj₂ refl | inj₁ refl | inj₁ refl | inj₁ refl = inj₁ (refl , refl)
      ... | inj₂ refl | inj₁ refl | inj₁ refl | inj₂ refl = inj₁ (refl , refl)
      ... | inj₂ refl | inj₁ refl | inj₂ refl | inj₁ refl = inj₂ (refl , refl)
      ... | inj₂ refl | inj₁ refl | inj₂ refl | inj₂ refl = inj₂ (refl , refl)
      ... | inj₂ refl | inj₂ refl | inj₁ refl | inj₁ refl = inj₂ (refl , refl)
      ... | inj₂ refl | inj₂ refl | inj₁ refl | inj₂ refl = inj₂ (refl , refl)
      ... | inj₂ refl | inj₂ refl | inj₂ refl | inj₁ refl = inj₂ (refl , refl)
      ... | inj₂ refl | inj₂ refl | inj₂ refl | inj₂ refl = inj₂ (refl , refl)
      
  <u,v>≡<x,y>→u≡x : ∀ {u v x y}
    → < u , v > ≡ < x , y > → u ≡ x
  <u,v>≡<x,y>→u≡x {u} {v} {x} {y} <u,v>≡<x,y> = u≡x
    where
      singletonu∈<u,v> = singletonA∈<A,B> u v
      singletonu∈<x,y> = proj₁
        (A≡B→x∈A↔x∈B <u,v>≡<x,y> (proj₁ (singleton u))) singletonu∈<u,v>
      u≡x : u ≡ x
      u≡x with x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ singletonu∈<x,y>
      ... | inj₁ singletonu≡singletonx =
        singletonA≡singletonB→A≡B singletonu≡singletonx
      ... | inj₂ singletonu≡⟨x,y⟩ = proj₁ (singletonA≡⟨B,C⟩→A≡B×A≡C singletonu≡⟨x,y⟩)
          
  <u,v>≡<x,y>→v≡y : ∀ {u v x y}
    → < u , v > ≡ < x , y > → v ≡ y
  <u,v>≡<x,y>→v≡y {u} {v} {x} {y} <u,v>≡<x,y> = v≡y
    where
      ⟨u,v⟩∈<u,v> = ⟨A,B⟩∈<A,B> u v
      ⟨u,v⟩∈<x,y> = proj₁
        (A≡B→x∈A↔x∈B <u,v>≡<x,y> (proj₁ ⟨ u , v ⟩))
        ⟨u,v⟩∈<u,v>
      v≡y : v ≡ y
      v≡y with x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ ⟨u,v⟩∈<x,y>
      ... | inj₁ ⟨u,v⟩≡singletonx = v≡y'
        where
          v≡y' : v ≡ y
          v≡y' with singletonA≡⟨B,C⟩→A≡B×A≡C (sym ⟨u,v⟩≡singletonx)
          ... | refl , refl = u≡y
            where
              ⟨u,y⟩∈<u,y> = ⟨A,B⟩∈<A,B> u y
              ⟨u,y⟩∈<u,u> = proj₂
                (A≡B→x∈A↔x∈B <u,v>≡<x,y> _)
                ⟨u,y⟩∈<u,y>
              u≡y : u ≡ y
              u≡y with x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ ⟨u,y⟩∈<u,u>
              ... | inj₁ ⟨u,y⟩≡singletonu = proj₂
                (singletonA≡⟨B,C⟩→A≡B×A≡C (sym ⟨u,y⟩≡singletonu))
              ... | inj₂ ⟨u,y⟩≡⟨u,u⟩
                with ⟨A,B⟩≡⟨C,D⟩→A≡C×B≡D⊎A≡D×B≡C ⟨u,y⟩≡⟨u,u⟩
              ... | inj₁ (refl , refl) = refl
              ... | inj₂ (refl , refl) = refl
      ... | inj₂ ⟨u,v⟩≡⟨x,y⟩
        with ⟨A,B⟩≡⟨C,D⟩→A≡C×B≡D⊎A≡D×B≡C ⟨u,v⟩≡⟨x,y⟩
      ... | inj₁ (_ , v≡y) = v≡y
      ... | inj₂ (refl , refl) = v≡u
        where
          singletonu∈<u,v> = singletonA∈<A,B> u v
          singletonu∈<v,u> = proj₁ (A≡B→x∈A↔x∈B <u,v>≡<x,y> _) singletonu∈<u,v>
          v≡u : v ≡ u
          v≡u with x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ singletonu∈<v,u>
          ... | inj₁ singletonu≡singletonv =
            sym (singletonA≡singletonB→A≡B singletonu≡singletonv)
          ... | inj₂ singletonu≡⟨v,u⟩
            with singletonA≡⟨B,C⟩→A≡B×A≡C singletonu≡⟨v,u⟩
          ... | refl , refl = refl

  <u,v>≡<x,y>→u≡x×v≡y : ∀ {u v x y}
    → < u , v > ≡ < x , y > → u ≡ x × v ≡ y
  <u,v>≡<x,y>→u≡x×v≡y {u} {v} {x} {y} <u,v>≡<x,y>
    with <u,v>≡<x,y>→u≡x <u,v>≡<x,y>
      | <u,v>≡<x,y>→v≡y <u,v>≡<x,y>
  ... | u≡x | v≡y = u≡x , v≡y

  <u,v>≡<x,y>↔u≡x×v≡y : ∀ u v x y
    → < u , v > ≡ < x , y > ↔ u ≡ x × v ≡ y
  <u,v>≡<x,y>↔u≡x×v≡y u v x y =
    <u,v>≡<x,y>→u≡x×v≡y , (λ { (refl , refl) → refl })

  x∈C→singletonx⊆C : ∀ {C x}
    → x ∈ C → proj₁ (singleton x) ⊆ C
  x∈C→singletonx⊆C {C} {x} x∈C {z} z∈singletonx
    with proj₁ (proj₂ (singleton x) _) z∈singletonx
  ... | refl = x∈C

  x∈C→y∈C→⟨x,y⟩⊆C : ∀ {C x y}
    → x ∈ C → y ∈ C → proj₁ ⟨ x , y ⟩ ⊆ C
  x∈C→y∈C→⟨x,y⟩⊆C {C} {x} {y} x∈C y∈C {z} z∈⟨x,y⟩
    with proj₁ (proj₂ ⟨ x , y ⟩ _) z∈⟨x,y⟩
  ... | inj₁ refl = x∈C
  ... | inj₂ refl = y∈C

  -- Lemma 3B.
  x∈C→y∈C→<x,y>∈powpowC : ∀ {x y C}
    → x ∈ C → y ∈ C → < x , y > ∈ proj₁ (pow (proj₁ (pow C)))
  x∈C→y∈C→<x,y>∈powpowC {x} {y} {C} x∈C y∈C = proj₂
    (proj₂ (pow (proj₁ (pow C))) _)
    λ z∈<x,y> → z∈<x,y>→z∈powC z∈<x,y>
      where
        z∈<x,y>→z∈powC : ∀ {z}
          → z ∈ < x , y > → z ∈ proj₁ (pow C)
        z∈<x,y>→z∈powC {z} z∈<x,y>
          with x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ z∈<x,y>
        ... | inj₁ refl = proj₂ (proj₂ (pow C) _) (x∈C→singletonx⊆C x∈C)
        ... | inj₂ refl = proj₂ (proj₂ (pow C) _) (x∈C→y∈C→⟨x,y⟩⊆C x∈C y∈C)

  -- Corallary 3C. Cartesian Product
  [_×_] : ∀ A B → ∃[ C ] ∀ c → c ∈ C ↔ ∃[ x ] ∃[ y ] x ∈ A × y ∈ B × c ≡ < x , y >
  [ A × B ] = (proj₁ [w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B])
    , λ c → lemma→ c , lemma← c
    where
      [w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B] =
        [ w ∈ proj₁ (pow (proj₁ (pow (proj₁ (A ∪ B)))))
          ∣ ∃[ x ] ∃[ y ] w ≡ < x , y > × x ∈ A × y ∈ B ]
      lemma→ : ∀ c
        → c ∈ proj₁ [w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B]
        → ∃[ x ] ∃[ y ] x ∈ A × y ∈ B × c ≡ < x , y >
      lemma→ c c∈[w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B]
        with proj₁
          (proj₂ [w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B] _)
          c∈[w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B]
      ... | c∈powpowA∪B , a , b , refl , a∈A , b∈B = a , (b , a∈A , b∈B , refl)
      lemma← : ∀ c
        → ∃[ x ] ∃[ y ] x ∈ A × y ∈ B × c ≡ < x , y >
        → c ∈ proj₁ [w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B]
      lemma← .(proj₁ ⟨ proj₁ ⟨ a , a ⟩ , proj₁ ⟨ a , b ⟩ ⟩) (a , b , a∈A , b∈B , refl) =
        proj₂ (proj₂ [w∈powpowA∪B∣w≡<x,y>×x∈A×y∈B] _)
          (x∈C→y∈C→<x,y>∈powpowC
            (proj₂ (proj₂ (A ∪ B) _) (inj₁ a∈A))
            (proj₂ (proj₂ (A ∪ B) _) (inj₂ b∈B))
          , a , (b , (refl , (a∈A , b∈B))))

  -- Lemma 3D.
  <x,y>∈A→x∈⋃⋃A×y∈⋃⋃A : ∀ {A x y}
    → < x , y > ∈ A
    → x ∈ proj₁ (⋃ (proj₁ (⋃ A))) × y ∈ proj₁ (⋃ (proj₁ (⋃ A)))
  <x,y>∈A→x∈⋃⋃A×y∈⋃⋃A {A} {x} {y} <x,y>∈A =
    proj₂
      (proj₂ (⋃ (proj₁ (⋃ A))) _)
      (proj₁ (singleton x)
      , proj₂ (proj₂ (⋃ A) _) (< x , y > , <x,y>∈A , singletonA∈<A,B> _ _)
      , proj₂ (proj₂ (singleton x) _) refl)
    , proj₂
      (proj₂ (⋃ (proj₁ (⋃ A))) _)
      (proj₁ ⟨ x , y ⟩
      , proj₂ (proj₂ (⋃ A) _) (< x , y > , <x,y>∈A , ⟨A,B⟩∈<A,B> _ _)
      , proj₂ (proj₂ ⟨ x , y ⟩ _) (inj₂ refl))
