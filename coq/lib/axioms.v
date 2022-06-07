Require Import Setoid.

(** * Axiomatic Set Theory. *)

(** Definition of sets. *)
Module Type SetDataType.
(** Data-type for sets. *)
Parameter set : Set.

(** Set membership: [A ∈ B] *)
Parameter member : set -> set -> Prop.

(** The axioms to construct sets
    use functions in the meta-language (gallina)
    to represent them.*)

(** Empty set. *)
Parameter empty : set.

(** Pairing. *)
Parameter pair : set -> set -> set.

(** Power-set. *)
Parameter power : set -> set.

(** Subset satisfying property. *)
Parameter comprehension : (set -> Prop) -> set -> set.

(** Abitrary union. *)
Parameter Union : set -> set.
End SetDataType.

(** Auxiliary definitions for sets. *)
Module SetAuxiliary (SetDefinition : SetDataType).
  Import SetDefinition.
  Notation "A '∈' B" := (member A B) (at level 80, no associativity) : type_scope.
  Notation "A '∉' B" := (~ (A ∈ B)) (at level 80, no associativity) : type_scope.
  
  (** The subset relation. *)
  Definition subset (A B : set) : Prop :=
    forall x, x ∈ A -> x ∈ B.

  Notation "A '⊆' B" := (subset A B) (at level 80, no associativity) : type_scope.

  Notation "'∅'" := empty (at level 0).
  
  Notation "⟨ A , B ⟩" := (pair A B) (no associativity).

  Notation "'{{' x '`∈' c '|' P '}}'"
    := (comprehension (fun x => P) c) (no associativity).

  Notation "'⋃'" := Union (at level 0).

  Definition union A B := ⋃ ⟨ A , B ⟩.

  Notation "A ∪ B" := (union A B) (at level 30, right associativity).
End SetAuxiliary.

(** Axioms of set theory. *)
Module Type SetAxioms (SetDefinition : SetDataType).
  Module SetAux := SetAuxiliary SetDefinition.
  Import SetDefinition SetAux.

  Axiom set_extensionality : forall A B x,
      (x ∈ A <-> x ∈ B) -> A = B.

  (** These axioms are specifications
      for the constructor functions
      in the meta-language (gallina). *)
  
  Axiom empty_set : forall x, x ∉ ∅.
  
  Axiom pairing : forall u v x, x ∈ ⟨ u , v ⟩ <-> x = u \/ x = v.
  
  Axiom power_set : forall a x, x ∈ power a <-> x ⊆ a.

  Axiom subset_schema : forall P c x,
      x ∈ {{ x `∈ c | P x }} <-> P x /\ x ∈ c.

  Axiom Union_axiom : forall A x,
      x ∈ ⋃ A <-> (exists b, b ∈ A /\ x ∈ b).
End SetAxioms.

(** Constructing sets. *)
Module SetConstruction
       (SetDefinition : SetDataType)
       (MakeAxioms : SetAxioms).
  Module SetAux := SetAuxiliary SetDefinition.
  Module SetAx := MakeAxioms SetDefinition.
  Import SetDefinition SetAux SetAx.
  
  Lemma empty_set_unique : forall A, (forall x, x ∉ A) -> A = ∅.
  Proof.
    intros A h.
    pose proof empty_set as H.
    pose proof set_extensionality as ext.
    specialize ext with A ∅ A.
    specialize h with A.
    specialize H with A. intuition.
  Qed.

  Definition singleton (x : set) : set := pair x x.
  
  Lemma singleton_single : forall x y, y ∈ singleton x <-> x = y.
  Proof.
    intros x y; unfold singleton.
    pose proof pairing x x y as [A h].
    intuition.
  Qed.

  (** Set intersection. *)
  Definition intersection A B := {{ x `∈ A | x ∈ B }}.

  Notation "A ∩ B" := (intersection A B) (at level 30, right associativity).
  
  Lemma intersection_intersects : forall A B x,
      x ∈ A ∩ B <-> x ∈ A /\ x ∈ B.
  Proof.
    intros A B x; unfold "_ ∩ _".
    pose proof subset_schema (fun x => member x B) A x as h;
      cbn in *; intuition.
  Qed.
  
  Theorem two_A : ~ exists A, forall x, x ∈ A.
  Proof.
    intros [A h].
    specialize h with {{ x `∈ A | x ∉ x }}.
    pose proof subset_schema
         (fun x => x ∉ x) A {{ x `∈ A | x ∉ x }} as H;
      cbn in *.
    intuition.
  Qed.

  Print two_A.

  Lemma Union_union : forall A B x,
      x ∈ A ∪ B <-> x ∈ A \/ x ∈ B.
  Proof.
    intros A B x; unfold "_ ∪ _".
    rewrite (Union_axiom ⟨A,B⟩ x).
    split; intros h.
    - destruct h as (b & hb & h).
      pose proof pairing A B b as H.
      rewrite H in hb.
      destruct hb; subst; auto.
    - destruct h as [h | h]; eexists; split;
        eauto; rewrite pairing; auto.
  Qed.

  (** Abitrary intersection. *)
  Definition Intersection_spec : Set :=
    forall (A : set), (exists x, x ∈ A) -> { y : set | forall x, x ∈ A -> y ∈ x }.

  Lemma Intersection_spec_inhabited :
    inhabited Intersection_spec.
  Proof.
    constructor; unfold Intersection_spec.
    Fail intros A [z h].
    (** Maybe everything 
        needs to be in [Set]
        rather than [Prop]
        so I can extract
        an intersection operator. *)
  Abort.
End SetConstruction.
