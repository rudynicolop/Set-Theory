-- Excluded middle results.
module enderton.exm where
  open import Data.Empty using (⊥;⊥-elim)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Negation using (contraposition;¬∃⟶∀¬;∀⟶¬∃¬)
  open import Data.Sum.Base using (_⊎_;inj₁;inj₂;reduce)
  open import Data.Product
    using (proj₁;proj₂;_×_;Σ;∃;∄;_,_;
      Σ-syntax;∃-syntax;∄-syntax)

  -- Lemmas assuiming the rule of excluded middle.
  module rem
    (P⊎¬P : ∀ (P : Set) → P ⊎ ¬ P) where

    ¬¬P→P : ∀ {P : Set} → ¬ ¬ P → P
    ¬¬P→P {P} ¬¬P with P⊎¬P P
    ... | inj₁ p = p
    ... | inj₂ ¬P = ⊥-elim (¬¬P ¬P)

    ¬P→¬Q⟶Q→P : ∀ {P Q : Set}
      → (¬ P → ¬ Q) → Q → P
    ¬P→¬Q⟶Q→P {P} {Q} ¬P→¬Q q
      with P⊎¬P P
    ... | inj₁ p = p
    ... | inj₂ ¬P = ⊥-elim (¬P→¬Q ¬P q)

    ¬P→Q⟶P×¬Q : ∀ {P Q : Set}
      → ¬ (P → Q) → P × ¬ Q
    ¬P→Q⟶P×¬Q {P} {Q} ¬P→Q
      with P⊎¬P P | P⊎¬P Q
    ... | inj₁ p | inj₁ q = ⊥-elim (¬P→Q λ _ → q)
    ... | inj₁ p | inj₂ ¬Q = p , ¬Q
    ... | inj₂ ¬P | inj₁ q = ⊥-elim (¬P→Q λ _ → q)
    ... | inj₂ ¬P | inj₂ ¬Q = ⊥-elim (¬P→Q (¬P→¬Q⟶Q→P λ _ → ¬P))

    ¬∀→∃¬ : ∀ {X : Set} {P : X → Set}
      → (¬ (∀ (x : X) → P x)) → ∃[ x ] ¬ P x
    ¬∀→∃¬ {X} {P} ¬∀ with P⊎¬P (∃[ x ] ¬ P x)
    ... | inj₁ ∃¬P = ∃¬P
    ... | inj₂ ¬∃¬P with ¬∃⟶∀¬ ¬∃¬P
    ... | ∀¬P = ⊥-elim (¬∀ λ x → ¬¬P→P (∀¬P x))
