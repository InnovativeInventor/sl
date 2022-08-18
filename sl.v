Require Import Nat.
Require Import Arith.
From Coq Require Export Lia.

(* Idea: make a eval function operate over a WFF datatype and prove properties of eval 
   on arbitrary WFFs (e.g. soundness). De Morgan and double negation elimination are formalized
   as rewrite rules. This file shows that composition of the DeMorgan and double negation rewrite rules are
    a) correct (as in, they "drive" all negations inwards and the only negations that appear are on Atomic sentences)
    b) sound
   
   Since PHIL 454 defines connectives via truth tables on atomic propositions, 
   this is the most faithful way to do a shallow embedding. Also, truth is decidable in this logic
   so we're fine here.

   I will also make minimal use of external automation -- just vanilla Coq.
*)

(* two-valued logic; truth is decidable *)
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
destruct a; reflexivity. (* case analysis *)
Qed.

Print a_implies_a.


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

Theorem negated_conditional_elim (a b: SLProp) : NotC (ThenC a b) = AndC a (NotC b).
destruct a; destruct b; reflexivity.
Qed.

(* specify the lazily evaluating system, which I will prove properties about and define rewrite rules on*)

Inductive SLPropSt : Set :=
| Atomic: SLProp -> SLPropSt
| Not: SLPropSt -> SLPropSt
| Or: SLPropSt -> SLPropSt -> SLPropSt
| And: SLPropSt -> SLPropSt -> SLPropSt
| Then: SLPropSt -> SLPropSt -> SLPropSt
.

Check Not (Atomic False). (* example *)

Check Not (Atomic True). (* example *)

Fixpoint eval (m: SLPropSt) : SLProp := (* evaluates our lazily evaluating system *)
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

(* size gives us something to induct over *)
Theorem size' : SLPropSt -> nat.
Proof.
intros m. induction m.
- apply 0.
- apply S. apply IHm.
- apply S. exact (IHm1 + IHm2).
- apply S. exact (IHm1 + IHm2).
- apply S. exact (IHm1 + IHm2).
Defined.

Fixpoint size (m: SLPropSt) : nat := (* equivalent; proofs are programs *)
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

Theorem size_same (m: SLPropSt): size' = size. (* proof that they are equiv! *)
reflexivity.
Qed.

Compute (size (Atomic True)).
Compute (size (Not (Atomic True))).

(* lemmas needed for proof of strong induction *)
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

Lemma size_greater_not_and (p q: SLPropSt): ((size p) < size (Not (And p q))) /\ ((size q) < size (Not (And p q))).
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

(* this is not quite the strong induction I want, but it gets very close *)
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

(* powerful strong induction! yay! *)
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

(* ltac proof tactics to make the following proofs less tedious *)
Ltac slprop_autodestruct := 
match goal with 
  | H: SLProp |- _ => destruct H
end.

Ltac slprop_rewrite :=
match goal with
  | H: ?m = Atomic _ |- _ = _ ?m => try rewrite H
  | H: ?m = Atomic _ |- _ ?m = _ => try rewrite H
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

(* custom tactics here are nice *)

Fixpoint demorgan_rewrites (m: SLPropSt) : SLPropSt :=
match m with 
| Not (Atomic p) => Not (Atomic p)
| Not (Not p) => Not (Not (demorgan_rewrites p))
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
      sl_induction_spec m. repeat rewrite double_negation_elim. sl_ineq_size_rewrite.
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

(* equivalent proof, but without custom tatics *)
Theorem demorgan_sound' (m: SLPropSt) : eval (demorgan_rewrites m) = eval m.
Proof.
induction m using @strong_induction.
- sl_induction_base_case.
- destruct m; auto; simpl.
  + destruct m; auto; simpl.
    * specialize (H m). simpl. repeat rewrite double_negation_elim. pose proof (size_greater_not_2 m). 
      rewrite <- H0 in H. auto.
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

Fixpoint negated_conditional (m: SLPropSt) : SLPropSt :=
match m with 
| Not (Atomic p) => Not (Atomic p)
| Not (Not p) => Not (Not (negated_conditional p))
| Not (And p q) => Not (And (negated_conditional p) (negated_conditional q))
| Not (Or p q) => Not (Or (negated_conditional p) (negated_conditional q))
| Not (Then p q) => (And (negated_conditional p) (Not (negated_conditional q)))
| Or p q => Or (negated_conditional p) (negated_conditional q)
| And p q => And (negated_conditional p) (negated_conditional q)
| Then p q => Then (negated_conditional p) (negated_conditional q)
| Atomic p => Atomic p (* atomic *)
end.

Theorem negated_conditional_sound (m: SLPropSt): eval (negated_conditional m) = eval m.
Proof.
induction m using @strong_induction.
- sl_induction_base_case.
- destruct m; auto; simpl. (* inductive step *)
  { 
    destruct m; simpl; auto.
    { 
      sl_induction_spec m. repeat rewrite double_negation_elim. sl_ineq_size_rewrite.
      auto using size_greater_not_2. 
    }
    all: sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
    pose proof (size_greater_not_or m1 m2) as H3; destruct H3;
    repeat auto_apply;
    pose proof demorgan_and;
    pose proof demorgan_or;
    pose proof negated_conditional_elim;
    try congruence.
  }
  all: sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
      pose proof (size_greater_or m1 m2) as H3; destruct H3;
      repeat auto_apply;
      congruence.
Defined.

(* Now, I finally prove the main point of this file *)

Definition drive_negations (m: SLPropSt): SLPropSt := negated_conditional( double_negation_rewrites (demorgan_rewrites m)).

Theorem drive_negations_sound (m: SLPropSt) : eval (drive_negations m) = eval m.
unfold drive_negations.
pose proof double_negation_sound.
pose proof demorgan_sound.
pose proof negated_conditional_sound.
congruence.
Defined.

Fixpoint drive_negations' (m: SLPropSt) : SLPropSt :=
match m with 
| Not (Atomic p) => Not (Atomic p)
| Not (Not p) => (drive_negations' p)
| Not (And p q) => Or (Not (drive_negations' p)) (Not (drive_negations' q))
| Not (Or p q) => And (Not (drive_negations' p)) (Not (drive_negations' q))
| Not (Then p q) => (And (drive_negations' p) (Not (drive_negations' q)))
| Or p q => Or (drive_negations' p) (drive_negations' q)
| And p q => And (drive_negations' p) (drive_negations' q)
| Then p q => Then (drive_negations' p) (drive_negations' q)
| Atomic p => Atomic p (* atomic *)
end.

Theorem drive_negations_equiv (m: SLPropSt): drive_negations' m = drive_negations m.
Proof.
induction m using @strong_induction.
- sl_induction_base_case.
- destruct m; auto; simpl.
  {
    admit.
  }
  all: unfold drive_negations; simpl; (* TODO: how can I fold the definition back in? *)
      unfold drive_negations in H; fold drive_negations; 
      sl_induction_spec m1; sl_induction_spec m2; repeat sl_ineq_size_rewrite;
      pose proof (size_greater_or m1 m2) as H3; destruct H3;
      repeat auto_apply;
      congruence.
Admitted.

(* I should probably change this to be of type Prop, to clearly distinguish the metalogic and the object logic.
   This is perfectly fine, though. 
*)
Fixpoint negations_only_atomic (m: SLPropSt) : SLProp := 
match m with 
| Not (Atomic p) => True
| Not (Not p) => False
| Not (And p q) => False
| Not (Or p q) => False
| Not (Then p q) => False
| Atomic p => True
| Or p q => AndC (negations_only_atomic p) (negations_only_atomic q)
| And p q => AndC (negations_only_atomic p) (negations_only_atomic q)
| Then p q => AndC (negations_only_atomic p) (negations_only_atomic q)
end.
