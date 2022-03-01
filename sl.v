Require Import Nat.
Require Import Arith.
From Coq Require Export Lia.

(* Idea: make a eval function operate over a WFF datatype and prove properties of eval 
   on arbitrary WFFs (e.g. soundness).
   
   Since PHIL 454 defines connectives via truth tables on atomic propositions, 
   this is the most faithful way to do a shallow embedding. Also, truth is decidable in this logic
   so we're fine here.

   I will also make minimal use of external automation -- just vanilla Coq.
*)

(* two-valued logic *)
Inductive SLProp := 
| True
| False
.

(* Our connectives *)
Definition NotC (a : SLProp) : SLProp :=
match a with 
| False => True
| True => False
end.

Definition Implies (a b : SLProp) : SLProp :=
match a with 
| False => True
| True => match b with 
  | False => False
  | True => True
  end
end.

Definition OrC (a b : SLProp) : SLProp :=
match a with 
| True => True
| False => match b with 
  | False => False
  | True => True
  end
end.

Definition AndC (a b : SLProp) : SLProp :=
match a with 
| False => False
| True => match b with 
  | False => False
  | True => True
  end
end.

Definition ThenC (a b : SLProp) : SLProp :=
match a with 
| False => True
| True => match b with 
  | False => False
  | True => True
  end
end.

(* demo on the eagerly evaluating system, just to make sure stuff works *)
Theorem a_implies_a (a: SLProp): Implies a a = True.
Proof.
destruct a; reflexivity.
Qed.


(* this are very needed/used later on *)
Theorem demorgan_or (a b: SLProp): OrC (NotC a) (NotC b) = NotC (AndC a b).
Proof.
destruct a; destruct b; reflexivity.
Qed.

Theorem demorgan_and (a b: SLProp): AndC (NotC a) (NotC b) = NotC (OrC a b).
Proof.
destruct a; destruct b; reflexivity.
Qed.

Theorem double_negation_elim (a: SLProp): NotC (NotC a) = a.
Proof.
destruct a; reflexivity.
Qed.


(* defining the lazily evaluating system, which I will prove properties about*)

Inductive SLPropSt : Set :=
| Atomic: SLProp -> SLPropSt
| Not: SLPropSt -> SLPropSt
| Or: SLPropSt -> SLPropSt -> SLPropSt
| And: SLPropSt -> SLPropSt -> SLPropSt
| Then: SLPropSt -> SLPropSt -> SLPropSt
.

Check Not (Atomic False).

Check Not (Atomic True).

Fixpoint eval (m: SLPropSt) : SLProp := 
match m with 
| Atomic a => a
| Not p => NotC (eval p)
| Or p q => OrC (eval p) (eval q)
| And p q => AndC (eval p) (eval q)
| Then p q => ThenC (eval p) (eval q)
end.

Fixpoint double_negation_rewrites (m: SLPropSt) : SLPropSt :=
match m with 
| Atomic p => Atomic p (* atomic *)

(* nested *)
| Not (Not p) => double_negation_rewrites p
| Not (Atomic p) => Not (Atomic p)
| Not (And p q) => Not (And (double_negation_rewrites p) (double_negation_rewrites q))
| Not (Or p q) => Not (Or (double_negation_rewrites p) (double_negation_rewrites q))
| Not (Then p q) => Not (Then (double_negation_rewrites p) (double_negation_rewrites q))

| Or p q => Or (double_negation_rewrites p) (double_negation_rewrites q)
| And p q => And (double_negation_rewrites p) (double_negation_rewrites q)
| Then p q => Then (double_negation_rewrites p) (double_negation_rewrites q)
end.

Theorem notc_not_eval (m: SLPropSt) : NotC (eval m) = eval (Not m).
Proof.
induction m; simpl; reflexivity.
Qed.

Theorem size' : SLPropSt -> nat.
Proof.
intros m. induction m.
- apply 0.
- apply S. apply IHm.
- apply S. exact (IHm1 + IHm2).
- apply S. exact (IHm1 + IHm2).
- apply S. exact (IHm1 + IHm2).
Defined.

Fixpoint size (m: SLPropSt) : nat := 
match m with 
| Atomic a => 0
| Not p => S (size p)
| Or p q => S (size p) + (size q)
| And p q => S (size p) + (size q)
| Then p q => S (size p) + (size q)
end.

Print size.
Print size'.
Check size.

Theorem size_same (m: SLPropSt): size' = size. (* they are equiv! *)
reflexivity.
Qed.

Compute (size (Atomic True)).
Compute (size (Not (Atomic True))).
(* something to induct over *)

(* lemmas to prove strong induction *)

Lemma atomic_equals (s: SLProp): exists atom : SLProp, Atomic s = Atomic atom.
Proof.
exists s. reflexivity.
Qed.

Lemma size_greater_not (q: SLPropSt): size q < size (Not q).
Proof.
induction q; simpl; try auto.
Qed.

Lemma size_greater_not_2 (q: SLPropSt): size q < size (Not (Not q)).
Proof.
induction q; simpl; try auto.
Qed.

Lemma size_greater_not_or (p q: SLPropSt): ((size p) < size (Not (Or p q))) /\ ((size q) < size (Not (Or p q))).
Proof.
split.
- induction p; simpl; destruct size; try lia.
- induction q; simpl; destruct size; try lia.
Qed.

Lemma size_not_equal (q: SLPropSt): size (Not q) = size (Not q).
Proof.
reflexivity.
Qed.

Lemma size_greater_or (p: SLPropSt) (q: SLPropSt): size p < size (Or p q) /\ size q < size (Or p q).
Proof.
induction q; simpl; try auto; destruct size; try lia.
Qed.

Lemma size_or_equal (p: SLPropSt) (q: SLPropSt): size (Or p q) = size (Or p q).
Proof.
reflexivity.
Qed.

Lemma size_greater_and (p: SLPropSt) (q: SLPropSt): size p < size (And p q) /\ size q < size (And p q).
Proof.
induction q; simpl; try auto; destruct size; try lia.
Qed.

Lemma size_and_equal (p: SLPropSt) (q: SLPropSt): size (And p q) = size (And p q).
Proof.
reflexivity.
Qed.

Lemma size_greater_then (p: SLPropSt) (q: SLPropSt): size p < size (Then p q) /\ size q < size (Then p q).
Proof.
induction q; simpl; try auto; destruct size; try lia.
Qed.

Lemma size_then_equal (p: SLPropSt) (q: SLPropSt): size (Then p q) = size (Then p q).
Proof.
reflexivity.
Qed.

Theorem strong_induction_base (p: SLPropSt -> Prop) : 
  (forall (m: SLPropSt), (exists (atom: SLProp), m = (Atomic atom)) -> (p m)) ->
  (forall (n: nat) (s: SLPropSt), forall (r: SLPropSt), ((size r) < n) -> (p r) -> (((size s) = n) -> (p s))) -> 
  (forall (q: SLPropSt), (p q)).
Proof.
intros.
induction q.
- specialize (H (Atomic s)) as Ha. exact (Ha (atomic_equals s)).
- specialize (H0 (size (Not q)) (Not q) q).
  exact (((H0 (size_greater_not q)) IHq) (size_not_equal q)). (* lots of pain *)
- specialize (H0 (size (Or q1 q2)) (Or q1 q2) q1).
  pose proof (size_greater_or q1 q2).
  destruct H1.
  exact (((H0 H1) IHq1) (size_or_equal q1 q2)).
- specialize (H0 (size (And q1 q2)) (And q1 q2) q1).
  pose proof (size_greater_and q1 q2).
  destruct H1.
  exact (((H0 H1) IHq1) (size_and_equal q1 q2)).
- specialize (H0 (size (Then q1 q2)) (Then q1 q2) q1).
  pose proof (size_greater_then q1 q2).
  destruct H1.
  exact (((H0 H1) IHq1) (size_then_equal q1 q2)).
Qed.

Theorem strong_induction (p: SLPropSt -> Prop) : 
  (forall (m: SLPropSt), (exists (atom: SLProp), m = (Atomic atom)) -> (p m)) ->
  (forall (n: nat), (forall (r: SLPropSt), ((size r) < n) -> (p r)) -> 
    forall (s: SLPropSt), (((size s) = n) -> (p s))) ->
  (forall (t: SLPropSt), (p t)).
Proof.
intros.
apply strong_induction_base.
- auto.
- intro. assert (forall n : nat, forall s : SLPropSt, size s = n -> p s).
  * intro. induction n0 using lt_wf_ind. (* key insight *)
    + specialize (H0 n0) as Hn0. assert (forall r : SLPropSt, size r < n0 -> p r).
      -- intro. specialize (H1 (size r)). eauto. (* TODO: how does eauto do this? *)
      -- exact (Hn0 H2).
  * intros. specialize (H1 n s). auto.
Qed.

Ltac slprop_autodestruct := 
match goal with 
  | H: SLProp |- _ => destruct H
end.

Ltac slprop_rewrite :=
match goal with
  | H: ?m = Atomic _ |- _ = eval ?m => try rewrite H
  | H: ?m = Atomic _ |- eval ?m = _ => try rewrite H
end.

Ltac slprop_exhaust := repeat try slprop_autodestruct; repeat try slprop_rewrite.

Ltac sl_ineq_size_rewrite :=
match goal with
  | H1: size _ = ?n, H2: size _ < ?n -> _, H: _ |- _ => rewrite <- H1 in H2
end.

Ltac sl_induction_base_case :=
match goal with 
  | H: exists _: SLProp, _ = Atomic _ |- _ => destruct H; slprop_exhaust; auto
end.

Ltac sl_induction_done m := (* broken *)
match goal with
  | m: SLPropSt, H1: size m < _ -> _, 
    H: _ |- _ => fail
  | H: _ |- _ => idtac
end.

Ltac sl_induction_spec m := 
match goal with
  | H: forall _ : SLPropSt, size _ < _ -> _
    |- _ => let x := fresh in specialize (H m) as x
end.

Ltac sl_induction_autospec :=
multimatch goal with
  | m1: SLPropSt, H: _ |- _ => sl_induction_spec m1
end.

Ltac auto_apply :=
match goal with 
  | H1: ?a -> ?b, H2: ?a, H: _ |- _ => pose proof (H1 H2); clear H1
end.

Theorem double_negation_sound (m: SLPropSt) : eval (double_negation_rewrites m) = eval m.
Proof.
induction m using @strong_induction.
- sl_induction_base_case. (* base case *)
- destruct m; auto; simpl. (* inductive step *)
  { 
    destruct m; simpl; auto.
    { 
      sl_induction_spec m. rewrite double_negation_elim. sl_ineq_size_rewrite.
      auto using size_greater_not_2. 
    }
    all: sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
    pose proof (size_greater_not_or m1 m2) as H3; destruct H3;
    repeat auto_apply;
    congruence.
  }
  all: sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
      pose proof (size_greater_or m1 m2) as H3; destruct H3;
      repeat auto_apply;
      congruence.
Qed.

(* maybe custom tactics here would be nice *)

Fixpoint demorgan_rewrites (m: SLPropSt) : SLPropSt :=
match m with 
| Not (Atomic p) => Not (Atomic p)
| Not (Not p) => p
| Not (And p q) => Or (Not (demorgan_rewrites p)) (Not (demorgan_rewrites q))
| Not (Or p q) => And (Not (demorgan_rewrites p)) (Not (demorgan_rewrites q))
| Not (Then p q) => Not (Then (demorgan_rewrites p) (demorgan_rewrites q))
| Or p q => Or (demorgan_rewrites p) (demorgan_rewrites q)
| And p q => And (demorgan_rewrites p) (demorgan_rewrites q)
| Then p q => Then (demorgan_rewrites p) (demorgan_rewrites q)
| Atomic p => Atomic p (* atomic *)
end.

Theorem demorgan (m1 m2: SLProp) : AndC (NotC m1) (NotC m2) = NotC (OrC m1 m2).
slprop_exhaust; auto.
Qed.


Theorem demorgan_sound (m: SLPropSt) : eval (demorgan_rewrites m) = eval m.
Proof.
induction m using @strong_induction.
- sl_induction_base_case.
- destruct m; auto; simpl. (* inductive step *)
  { 
    destruct m; simpl; auto.
    { 
      sl_induction_spec m. rewrite double_negation_elim. sl_ineq_size_rewrite.
      auto using size_greater_not_2. 
    }
    all: sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
    pose proof (size_greater_not_or m1 m2) as H3; destruct H3;
    repeat auto_apply;
    pose proof demorgan_and;
    pose proof demorgan_or;
    congruence.
  }
  all: sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
      pose proof (size_greater_or m1 m2) as H3; destruct H3;
      repeat auto_apply;
      congruence.
Defined.

Theorem demorgan_sound' (m: SLPropSt) : eval (demorgan_rewrites m) = eval m.
Proof.
induction m using @strong_induction.
- sl_induction_base_case.
- destruct m; auto; simpl.
  + destruct m; auto; simpl.
    * specialize (H m). simpl. rewrite double_negation_elim. auto.
    * specialize (H m1) as H1. specialize (H m2) as H2. rewrite <- H0 in H1. rewrite <- H0 in H2.
      pose proof (size_greater_not_or m1 m2). destruct H3.
      pose proof (H1 H3).
      pose proof (H2 H4).
      pose proof demorgan_and.
      congruence.
    * specialize (H m1) as H1. specialize (H m2) as H2. rewrite <- H0 in H1. rewrite <- H0 in H2.
      pose proof (size_greater_not_or m1 m2). destruct H3.
      pose proof (H1 H3).
      pose proof (H2 H4).
      pose proof demorgan_or.
      congruence.
    * specialize (H m1) as H1. specialize (H m2) as H2. rewrite <- H0 in H1. rewrite <- H0 in H2.
      pose proof (size_greater_not_or m1 m2). destruct H3.
      pose proof (H1 H3).
      pose proof (H2 H4).
      congruence.
  + specialize (H m1) as H1. specialize (H m2) as H2. rewrite <- H0 in H1. rewrite <- H0 in H2.
      pose proof (size_greater_or m1 m2). destruct H3.
      pose proof (H1 H3).
      pose proof (H2 H4).
      congruence.
  + specialize (H m1) as H1. specialize (H m2) as H2. rewrite <- H0 in H1. rewrite <- H0 in H2.
      pose proof (size_greater_or m1 m2). destruct H3.
      pose proof (H1 H3).
      pose proof (H2 H4).
      congruence.
  + specialize (H m1) as H1. specialize (H m2) as H2. rewrite <- H0 in H1. rewrite <- H0 in H2.
      pose proof (size_greater_then m1 m2). destruct H3.
      pose proof (H1 H3).
      pose proof (H2 H4).
      congruence.
Defined.

Definition drive_negations (m: SLPropSt): SLPropSt := double_negation_rewrites (demorgan_rewrites m).

Theorem drive_negations_sound (m: SLPropSt) : eval (drive_negations m) = eval m.
unfold drive_negations.
pose proof double_negation_sound.
pose proof demorgan_sound.
congruence.
Defined.