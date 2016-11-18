(* -*- coding: utf-8 -*- *)
(*      This file is distributed under the terms of the      *)
(*       GNU Lesser General Public License Version 2.1       *)
(* Author: Sosuke Moriguchi *)
(* Extended interface from MSetInterface *)

(** * Finite set library with extension *)

(** This file has the modules in MSetInterface, except for S. *)
(* Module Type S is no make sence. It is just Sets.
   It saves three letters, but loses its purpose from the name. Why do you want? *)

Require Export Bool SetoidList RelationClasses Morphisms
 RelationPairs Equalities Orders OrdersFacts.
Require MSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.



Module Type TypElt := MSetInterface.TypElt.

Module Type HasWOps := MSetInterface.HasWOps.

Module Type WOps := MSetInterface.WOps.


(** ** Functorial signature for weak sets

    Weak sets are sets without ordering on base elements, only
    a decidable equality. filter_spec', partition_spec1', partition_spec2' are added. *)

Module Type WSetsOn (E : DecidableType).
  Include MSetInterface.WSetsOn E.

  (** Added specifications *)

  Section Spec.
  Variable s : t.
  Variable x : elt.
  Variable f : elt -> bool.

  Parameter filter_spec' : In x (filter f s) -> In x s.
  Parameter partition_spec1' : In x (fst (partition f s)) -> In x s.
  Parameter partition_spec2' : In x (snd (partition f s)) -> In x s.

  End Spec.

End WSetsOn.

(** ** Static signature for weak sets

    Similar to the functorial signature [WSetsOn], except that the
    module [E] of base elements is incorporated in the signature. *)

Module Type WSets.
  Declare Module E : DecidableType.
  Include WSetsOn E.
End WSets.

(** ** Functorial signature for sets on ordered elements *)

Module Type HasOrdOps := MSetInterface.HasOrdOps.

Module Type Ops (E : OrderedType) := WOps E <+ HasOrdOps.


Module Type SetsOn (E : OrderedType).
  Include MSetInterface.SetsOn E.

  (** Added specifications *)

  Section Spec.
  Variable s : t.
  Variable x : elt.
  Variable f : elt -> bool.

  Parameter filter_spec' : In x (filter f s) -> In x s.
  Parameter partition_spec1' : In x (fst (partition f s)) -> In x s.
  Parameter partition_spec2' : In x (snd (partition f s)) -> In x s.

  End Spec.

End SetsOn.


(** ** Static signature for sets on ordered elements

    Similar to the functorial signature [SetsOn], except that the
    module [E] of base elements is incorporated in the signature. *)

Module Type Sets.
  Declare Module E : OrderedType.
  Include SetsOn E.
End Sets.


(** ** Some subtyping tests
<<
Module S_WS (M : Sets) <: WSets := M.
Module Sfun_WSfun (E:OrderedType)(M : SetsOn E) <: WSetsOn E := M.
Module S_Sfun (M : Sets) <: SetsOn M.E := M.
Module WS_WSfun (M : WSets) <: WSetsOn M.E := M.
>>
XSets are always MSets.
<<
Module WX_WM (M : WSets) <: MSetInterface.WSets := M.
Module X_M (M : Sets) <: MSetInterface.Sets := M.
>>
*)



(** ** Signatures for set representations with ill-formed values.

   Extension:
   Motivation is the same as MSets, but this module requires weaker parameters than the one in MSets.
   Some parameters in one in MSets (f.g., filter_spec) do not get Ok.
*)


Module Type WRawSets (E : DecidableType).
  (** First, we ask for all the functions *)
  Include WOps E.

  (** Is a set well-formed or ill-formed ? *)

  Parameter IsOk : t -> Prop.
  Class Ok (s:t) : Prop := ok : IsOk s.

  (** In order to be able to validate (at least some) particular sets as
      well-formed, we ask for a boolean function for (semi-)deciding
      predicate [Ok]. If [Ok] isn't decidable, [isok] may be the
      always-false function. *)
  Parameter isok : t -> bool.

  Declare Instance isok_Ok s `(isok s = true) : Ok s | 10.

  (** Logical predicates *)
  Parameter In : elt -> t -> Prop.
  Declare Instance In_compat : Proper (E.eq==>eq==>iff) In.

  Definition Equal s s' := forall a : elt, In a s <-> In a s'.
  Definition Subset s s' := forall a : elt, In a s -> In a s'.
  Definition Empty s := forall a : elt, ~ In a s.
  Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
  Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

  Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
  Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

  Definition eq : t -> t -> Prop := Equal.
  Declare Instance eq_equiv : Equivalence eq.

  (** First, all operations are compatible with the well-formed predicate. *)

  Declare Instance empty_ok : Ok empty.
  Declare Instance add_ok s x `(Ok s) : Ok (add x s).
  Declare Instance remove_ok s x `(Ok s) : Ok (remove x s).
  Declare Instance singleton_ok x : Ok (singleton x).
  Declare Instance union_ok s s' `(Ok s, Ok s') : Ok (union s s').
  Declare Instance inter_ok s s' `(Ok s, Ok s') : Ok (inter s s').
  Declare Instance diff_ok s s' `(Ok s, Ok s') : Ok (diff s s').
  Declare Instance filter_ok s f `(Ok s) : Ok (filter f s).
  Declare Instance partition_ok1 s f `(Ok s) : Ok (fst (partition f s)).
  Declare Instance partition_ok2 s f `(Ok s) : Ok (snd (partition f s)).

  (** Now, the specifications, with constraints on the input sets. *)

  Section Spec.
  Variable s s': t.
  Variable x y : elt.
  Variable f : elt -> bool.
  Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

  Parameter mem_spec : forall `{Ok s}, mem x s = true <-> In x s.
  Parameter equal_spec : forall `{Ok s, Ok s'},
    equal s s' = true <-> s[=]s'.
  Parameter subset_spec : forall `{Ok s, Ok s'},
    subset s s' = true <-> s[<=]s'.
  Parameter empty_spec : Empty empty.
  Parameter is_empty_spec : forall `{Ok s},
    is_empty s = true <-> Empty s.
  Parameter add_spec : forall `{Ok s},
    In y (add x s) <-> E.eq y x \/ In y s.
  Parameter remove_spec : forall `{Ok s},
    In y (remove x s) <-> In y s /\ ~E.eq y x.
  Parameter singleton_spec : In y (singleton x) <-> E.eq y x.
  Parameter union_spec : forall `{Ok s, Ok s'},
    In x (union s s') <-> In x s \/ In x s'.
  Parameter inter_spec : forall `{Ok s, Ok s'},
    In x (inter s s') <-> In x s /\ In x s'.
  Parameter diff_spec : forall `{Ok s, Ok s'},
    In x (diff s s') <-> In x s /\ ~In x s'.
  Parameter fold_spec : forall `{Ok s} (A : Type) (i : A) (f : elt -> A -> A),
    fold f s i = fold_left (flip f) (elements s) i.
  Parameter cardinal_spec : forall `{Ok s},
    cardinal s = length (elements s).
  Parameter filter_spec : forall `{Ok s}, compatb f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Parameter filter_spec' : forall `{Ok s},
    In x (filter f s) -> In x s.
  Parameter for_all_spec : forall `{Ok s}, compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Parameter exists_spec : forall `{Ok s}, compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Parameter partition_spec1 : forall `{Ok s}, compatb f ->
    fst (partition f s) [=] filter f s.
  Parameter partition_spec2 : forall `{Ok s}, compatb f ->
    snd (partition f s) [=] filter (fun x => negb (f x)) s.
  Parameter partition_spec1' : forall `{Ok s},
    In x (fst (partition f s)) -> In x s.
  Parameter partition_spec2' : forall `{Ok s},
    In x (snd (partition f s)) -> In x s.
  Parameter elements_spec1 : forall `{Ok s},
    InA E.eq x (elements s) <-> In x s.
  Parameter elements_spec2w : forall `{Ok s}, NoDupA E.eq (elements s).
  Parameter choose_spec1 : forall `{Ok s}, choose s = Some x -> In x s.
  Parameter choose_spec2 : forall `{Ok s}, choose s = None -> Empty s.

  End Spec.

End WRawSets.

(** From weak raw sets to weak usual sets *)

Module WRaw2SetsOn (E:DecidableType)(M:WRawSets E) <: WSetsOn E.

 (** We avoid creating induction principles for the Record *)
 Local Unset Elimination Schemes.

 Definition elt := E.t.

 Record t_ := Mkt {this :> M.t; is_ok : M.Ok this}.
 Definition t := t_.
 Arguments Mkt this {is_ok}.
 Hint Resolve is_ok : typeclass_instances.

 Definition In (x : elt)(s : t) := M.In x s.(this).
 Definition Equal (s s' : t) := forall a : elt, In a s <-> In a s'.
 Definition Subset (s s' : t) := forall a : elt, In a s -> In a s'.
 Definition Empty (s : t) := forall a : elt, ~ In a s.
 Definition For_all (P : elt -> Prop)(s : t) := forall x, In x s -> P x.
 Definition Exists (P : elt -> Prop)(s : t) := exists x, In x s /\ P x.

 Definition mem (x : elt)(s : t) := M.mem x s.
 Definition add (x : elt)(s : t) : t := Mkt (M.add x s).
 Definition remove (x : elt)(s : t) : t := Mkt (M.remove x s).
 Definition singleton (x : elt) : t := Mkt (M.singleton x).
 Definition union (s s' : t) : t := Mkt (M.union s s').
 Definition inter (s s' : t) : t := Mkt (M.inter s s').
 Definition diff (s s' : t) : t := Mkt (M.diff s s').
 Definition equal (s s' : t) := M.equal s s'.
 Definition subset (s s' : t) := M.subset s s'.
 Definition empty : t := Mkt M.empty.
 Definition is_empty (s : t) := M.is_empty s.
 Definition elements (s : t) : list elt := M.elements s.
 Definition choose (s : t) : option elt := M.choose s.
 Definition fold (A : Type)(f : elt -> A -> A)(s : t) : A -> A := M.fold f s.
 Definition cardinal (s : t) := M.cardinal s.
 Definition filter (f : elt -> bool)(s : t) : t := Mkt (M.filter f s).
 Definition for_all (f : elt -> bool)(s : t) := M.for_all f s.
 Definition exists_ (f : elt -> bool)(s : t) := M.exists_ f s.
 Definition partition (f : elt -> bool)(s : t) : t * t :=
   let p := M.partition f s in (Mkt (fst p), Mkt (snd p)).

 Instance In_compat : Proper (E.eq==>eq==>iff) In.
 Proof. repeat red. intros; apply M.In_compat; congruence. Qed.

 Definition eq : t -> t -> Prop := Equal.

 Instance eq_equiv : Equivalence eq.
 Proof. firstorder. Qed.

 Definition eq_dec : forall (s s':t), { eq s s' }+{ ~eq s s' }.
 Proof.
  intros (s,Hs) (s',Hs').
  change ({M.Equal s s'}+{~M.Equal s s'}).
  destruct (M.equal s s') eqn:H; [left|right];
   rewrite <- M.equal_spec; congruence.
 Defined.


 Section Spec.
  Variable s s' : t.
  Variable x y : elt.
  Variable f : elt -> bool.
  Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

  Lemma mem_spec : mem x s = true <-> In x s.
  Proof. exact (@M.mem_spec _ _ _). Qed.
  Lemma equal_spec : equal s s' = true <-> Equal s s'.
  Proof. exact (@M.equal_spec _ _ _ _). Qed.
  Lemma subset_spec : subset s s' = true <-> Subset s s'.
  Proof. exact (@M.subset_spec _ _ _ _). Qed.
  Lemma empty_spec : Empty empty.
  Proof. exact M.empty_spec. Qed.
  Lemma is_empty_spec : is_empty s = true <-> Empty s.
  Proof. exact (@M.is_empty_spec _ _). Qed.
  Lemma add_spec : In y (add x s) <-> E.eq y x \/ In y s.
  Proof. exact (@M.add_spec _ _ _ _). Qed.
  Lemma remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
  Proof. exact (@M.remove_spec _ _ _ _). Qed.
  Lemma singleton_spec : In y (singleton x) <-> E.eq y x.
  Proof. exact (@M.singleton_spec _ _). Qed.
  Lemma union_spec : In x (union s s') <-> In x s \/ In x s'.
  Proof. exact (@M.union_spec _ _ _ _ _). Qed.
  Lemma inter_spec : In x (inter s s') <-> In x s /\ In x s'.
  Proof. exact (@M.inter_spec _ _ _ _ _). Qed.
  Lemma diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
  Proof. exact (@M.diff_spec _ _ _ _ _). Qed.
  Lemma fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
      fold f s i = fold_left (fun a e => f e a) (elements s) i.
  Proof. exact (@M.fold_spec _ _). Qed.
  Lemma cardinal_spec : cardinal s = length (elements s).
  Proof. exact (@M.cardinal_spec s _). Qed.
  Lemma filter_spec : compatb f ->
    (In x (filter f s) <-> In x s /\ f x = true).
  Proof. exact (@M.filter_spec _ _ _ _). Qed.
  Lemma filter_spec' : In x (filter f s) -> In x s.
  Proof. exact (@M.filter_spec' _ _ _ _). Qed.
  Lemma for_all_spec : compatb f ->
    (for_all f s = true <-> For_all (fun x => f x = true) s).
  Proof. exact (@M.for_all_spec _ _ _). Qed.
  Lemma exists_spec : compatb f ->
    (exists_ f s = true <-> Exists (fun x => f x = true) s).
  Proof. exact (@M.exists_spec _ _ _). Qed.
  Lemma partition_spec1 : compatb f -> Equal (fst (partition f s)) (filter f s).
  Proof. exact (@M.partition_spec1 _ _ _). Qed.
  Lemma partition_spec2 : compatb f ->
      Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
  Proof. exact (@M.partition_spec2 _ _ _). Qed.
  Lemma partition_spec1' : In x (fst (partition f s)) -> In x s.
  Proof. exact (@M.partition_spec1' _ _ _ _). Qed.
  Lemma partition_spec2' : In x (snd (partition f s)) -> In x s.
  Proof. exact (@M.partition_spec2' _ _ _ _). Qed.
  Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
  Proof. exact (@M.elements_spec1 _ _ _). Qed.
  Lemma elements_spec2w : NoDupA E.eq (elements s).
  Proof. exact (@M.elements_spec2w _ _). Qed.
  Lemma choose_spec1 : choose s = Some x -> In x s.
  Proof. exact (@M.choose_spec1 _ _ _). Qed.
  Lemma choose_spec2 : choose s = None -> Empty s.
  Proof. exact (@M.choose_spec2 _ _). Qed.

 End Spec.

End WRaw2SetsOn.

Module WRaw2Sets (D:DecidableType)(M:WRawSets D) <: WSets with Module E := D.
  Module E := D.
  Include WRaw2SetsOn D M.
End WRaw2Sets.

(** Same approach for ordered sets *)

Module Type RawSets (E : OrderedType).
  Include WRawSets E <+ HasOrdOps <+ HasLt <+ IsStrOrder.

  Section Spec.
  Variable s s': t.
  Variable x y : elt.

  (** Specification of [compare] *)
  Parameter compare_spec : forall `{Ok s, Ok s'}, CompSpec eq lt s s' (compare s s').

  (** Additional specification of [elements] *)
  Parameter elements_spec2 : forall `{Ok s}, sort E.lt (elements s).

  (** Specification of [min_elt] *)
  Parameter min_elt_spec1 : forall `{Ok s}, min_elt s = Some x -> In x s.
  Parameter min_elt_spec2 : forall `{Ok s}, min_elt s = Some x -> In y s -> ~ E.lt y x.
  Parameter min_elt_spec3 : forall `{Ok s}, min_elt s = None -> Empty s.

  (** Specification of [max_elt] *)
  Parameter max_elt_spec1 : forall `{Ok s}, max_elt s = Some x -> In x s.
  Parameter max_elt_spec2 : forall `{Ok s}, max_elt s = Some x -> In y s -> ~ E.lt x y.
  Parameter max_elt_spec3 : forall `{Ok s}, max_elt s = None -> Empty s.

  (** Additional specification of [choose] *)
  Parameter choose_spec3 : forall `{Ok s, Ok s'},
    choose s = Some x -> choose s' = Some y -> Equal s s' -> E.eq x y.

  End Spec.

End RawSets.

(** From Raw to usual sets *)

Module Raw2SetsOn (O:OrderedType)(M:RawSets O) <: SetsOn O.
  Include WRaw2SetsOn O M.

  Definition compare (s s':t) := M.compare s s'.
  Definition min_elt (s:t) : option elt := M.min_elt s.
  Definition max_elt (s:t) : option elt := M.max_elt s.
  Definition lt (s s':t) := M.lt s s'.

  (** Specification of [lt] *)
  Instance lt_strorder : StrictOrder lt.
  Proof. constructor ; unfold lt; red.
    unfold complement. red. intros. apply (irreflexivity H).
    intros. transitivity y; auto.
  Qed.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
  repeat red. unfold eq, lt.
  intros (s1,p1) (s2,p2) E (s1',p1') (s2',p2') E'; simpl.
  change (M.eq s1 s2) in E.
  change (M.eq s1' s2') in E'.
  rewrite E,E'; intuition.
  Qed.

  Section Spec.
  Variable s s' s'' : t.
  Variable x y : elt.

  Lemma compare_spec : CompSpec eq lt s s' (compare s s').
  Proof. unfold compare; destruct (@M.compare_spec s s' _ _); auto. Qed.

  (** Additional specification of [elements] *)
  Lemma elements_spec2 : sort O.lt (elements s).
  Proof. exact (@M.elements_spec2 _ _). Qed.

  (** Specification of [min_elt] *)
  Lemma min_elt_spec1 : min_elt s = Some x -> In x s.
  Proof. exact (@M.min_elt_spec1 _ _ _). Qed.
  Lemma min_elt_spec2 : min_elt s = Some x -> In y s -> ~ O.lt y x.
  Proof. exact (@M.min_elt_spec2 _ _ _ _). Qed.
  Lemma min_elt_spec3 : min_elt s = None -> Empty s.
  Proof. exact (@M.min_elt_spec3 _ _). Qed.

  (** Specification of [max_elt] *)
  Lemma max_elt_spec1 : max_elt s = Some x -> In x s.
  Proof. exact (@M.max_elt_spec1 _ _ _). Qed.
  Lemma max_elt_spec2 : max_elt s = Some x -> In y s -> ~ O.lt x y.
  Proof. exact (@M.max_elt_spec2 _ _ _ _). Qed.
  Lemma max_elt_spec3 : max_elt s = None -> Empty s.
  Proof. exact (@M.max_elt_spec3 _ _). Qed.

  (** Additional specification of [choose] *)
  Lemma choose_spec3 :
    choose s = Some x -> choose s' = Some y -> Equal s s' -> O.eq x y.
  Proof. exact (@M.choose_spec3 _ _ _ _ _ _). Qed.

  End Spec.

End Raw2SetsOn.

Module Raw2Sets (O:OrderedType)(M:RawSets O) <: Sets with Module E := O.
  Module E := O.
  Include Raw2SetsOn O M.
End Raw2Sets.


(** * Other modules in MSetInterface *)


Module Type IN := MSetInterface.IN.

Module MakeSetOrdering := MSetInterface.MakeSetOrdering.


Module MakeListOrdering := MSetInterface.MakeListOrdering.
