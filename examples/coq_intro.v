From iris.heap_lang Require Import notation proofmode.
From iris Require Import prelude.
Open Scope string_scope. 

Section coq_intro.

(* Should print "it works" : string *)
Check "it works".

Lemma very_basic: 1 + 1 = 2.
Proof.
  lia.
Qed.

Lemma more_advanced x y : x = 2 ∧ y = 3 →  x+y = 5 ∨ x+y = 8.
Proof.
  intros H. (* Assume the LHS of the implication to prove the RHS *)
  destruct H as [H1 H2]. (* Split the conjunction into two parts *)
  rewrite H1. (* H1 is an equality, we can _rewrite_ with it *)
  rewrite H2. (* similar *)
  left. (* we know the left side is true *)
  lia.
Qed.

Lemma quantifiers : ∀ x, ∃ y, y > x + x.
  intros x. (* Read: Let x be an arbitrary number. *)
  exists (2 * x +1). (* We choose y := 2 * x + 1 *)
  lia. (* The resulting equation is now simple enough for lia to handle it *)
Qed.

(* A tactic overview:

Here, `x` is a stand-in for a variable, and `H` a stand-in for a hypothesis.

intros x -- introduce a quantifier
intros H -- introduce a variable
exists x -- solve an existentail quantifier

apply lemma -- applies a lemma
apply H -- apply a hypothesis that has the shape ∀ x, .. or shape P → Q
           (i.e. this is the counterpart to intros)

split -- Solve a conjunction by proving both sides individually
destruct H as [H1 H2] -- Destruct a conjunction that is assumed

left -- Solve a disjunction (or) by proving the left side
right -- Analogous but the right side
destruct H as [H1|H2] -- destruct a disjunction that is assumed. This generates two new cases

assert (P) as H -- allows you to prove an arbitrary new goal, which can then be used as a hypothesis

rewrite H -- when H is an equality, this allows you to replace one side with the other
reflexivity -- proves goals of shape `x = y`, when x and y can be converted to the other by computation

lia -- proves goals about linear (in)equations in the integers / natural numbers.

*)

End coq_intro.
