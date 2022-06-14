module enderton.relations where
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
  ⟨A,B⟩≡⟨C,D⟩→A≡C×B≡D⊎A≡D×B≡C {A} {B} {C} {D} ⟨A,B⟩≡⟨C,D⟩ = {!!}
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
  <u,v>≡<x,y>→v≡y {u} {v} {x} {y} <u,v>≡<x,y> = {!!}
    where
      ⟨u,v⟩∈<u,v> = ⟨A,B⟩∈<A,B> u v
      ⟨u,v⟩∈<x,y> = proj₁
        (A≡B→x∈A↔x∈B <u,v>≡<x,y> (proj₁ ⟨ u , v ⟩))
        ⟨u,v⟩∈<u,v>
      v≡y : v ≡ y
      v≡y with x∈<A,B>→x≡singletonA⊎x≡⟨A,B⟩ ⟨u,v⟩∈<x,y>
      ... | inj₁ ⟨u,v⟩≡singletonx = {!!}
      ... | inj₂ ⟨u,v⟩≡⟨x,y⟩
        with ⟨A,B⟩≡⟨C,D⟩→A≡C×B≡D⊎A≡D×B≡C ⟨u,v⟩≡⟨x,y⟩
      ... | inj₁ (_ , v≡y) = v≡y
      ... | inj₂ (refl , refl) = {!!}

  <u,v>≡<x,y>→u≡x×v≡y : ∀ {u v x y}
    → < u , v > ≡ < x , y > → u ≡ x × v ≡ y
  <u,v>≡<x,y>→u≡x×v≡y {u} {v} {x} {y} <u,v>≡<x,y> = {!!}
  {-
     (extensionality _ _ λ z → {!!} , {!!})
     , (extensionality _ _ λ z → {!!} , {!!})
        where
          z∈u→z∈x : ∀ z → z ∈ u → z ∈ x
          z∈u→z∈x z z∈u
            with A≡B→x∈A↔x∈B <u,v>≡<x,y> <u,v>≡<x,y> = {!!}
          z∈x→z∈u : ∀ z → z ∈ x → z ∈ u
          z∈x→z∈u z z∈x = {!!}
          z∈v→z∈y : ∀ z → z ∈ v → z ∈ y
          z∈v→z∈y z z∈v = {!!}
          z∈y→z∈v : ∀ z → z ∈ y → z ∈ v
          z∈y→z∈v z z∈y = {!!} -}

  <u,v>≡<x,y>↔u≡x×v≡y : ∀ u v x y
    → < u , v > ≡ < x , y > ↔ u ≡ x × v ≡ y
  <u,v>≡<x,y>↔u≡x×v≡y u v x y = {!!} , (λ { (refl , refl) → refl })
      
