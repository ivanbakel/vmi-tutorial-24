From iris.heap_lang Require Import notation proofmode.
From iris Require Import prelude.
Open Scope string_scope. 

Section coq_intro.

Context `{Σ : gFunctors}.
Local Notation "P ⊢ Q" := (@bi_entails (iProp Σ) P%I Q%I) .
Local Notation "⊢ P" := (@bi_emp_valid (iProp Σ) P%I) .
Implicit Types x y : Z.

(* This is a basic intro to using Coq and the Iris proofmode. *)

(* Should print "it works" : string *)
Check "it works".

(* The proofmode lets us mix separation logic statements (more on that later)
   with pure mathematical statements. Pure statements are written in the notation
   [⌜ ... ⌝] - for the sake of the tutorial we will only look at statements about
   the integers.

   A proof in the proofmode is divided into
     * pure mathematical hypotheses 
     * separation logic hypotheses
     * the goal (of one or more statements)

   We write our lemmas as [P ⊢ Q] - this means everything in [P] is a hypothesis,
   and [Q] is the goal.

   For example, the next lemma has no hypotheses, and one goal. If we know enough
   to solve a pure goal about integers, we can solve it with a tactic -
   [eauto with lia]. *)

Lemma very_basic: ⊢ ⌜(1 + 1 = 2)%Z⌝.
Proof.
  eauto with lia.
Qed.

(* To handle more complex goals, and to manipulate hypotheses, Coq uses *tactics*.
   These are instructions to the proof engine.

   The next proofs use 3 tactics
     * [iIntros], which introduces (gives names to) hypotheses
     * [iLeft], which changes the goal by picking a side of the disjunction
     * [eauto with lia], the integer-fact-solving tactic we saw before *)

Lemma with_hypothesis x : ⌜(x > 3)%Z⌝ ⊢ ⌜(x >= 4)%Z⌝.
Proof.
  iIntros "%H". (* Here, we introduce a *pure* hypothesis, so it gets a % *)
  eauto with lia.
Qed.


Lemma more_advanced x y : ⌜x = 2⌝ ∗ ⌜y = 3⌝ ⊢ ⌜(x + y = 5)%Z⌝ ∨ ⌜(x + y = 8)%Z⌝.
Proof.
  iIntros "[%H1 %H2]".
    (* here we have two hypotheses, so we split them with the [] pattern. They're
       still pure, so they both get a leading % *)
  iLeft. (* we know the left side is true *)
  eauto with lia. (* lia can do the algebra for us *)
Qed.

Lemma iFrame_example P Q : P ∗ Q ⊢ Q ∗ P.
Proof.
  iIntros "[HP HQ]".
  (* solves the `P` *)
  iFrame "HP".
  iFrame "HQ".
Qed.


(* A tactic overview:

Here, `x` is a stand-in for a variable, and `H` a stand-in for a hypothesis.

iIntros "%H" -- introduce a pure hypothesis 
iIntros "H" -- introduce a hypothesis 

iApply H -- applies a lemma
iApply "H" -- applies a separation logic hypothesis in the context

iSplit -- Solve a conjunction by proving both sides individually
iDestruct "H" as "[H1 H2]" -- Destruct a conjunction that is assumed

iLeft -- Solve a disjunction (or) by proving the left side
iRight -- Analogous but the right side
iDestruct "H" as "[H1|H2]" -- destruct a disjunction that is assumed. This generates two new cases

iExists x -- solve an existential quantifier
iDestruct "H" as "[%x H]" -- destructs an assumed existential quantifier. `x` is the witness' name, `H` the assumption about it.

iFrame "Hyp" -- if the contains "Hyp" as well as a bunch of different things, all in a separating conjunction (∗), then iFrame will "remove" parts.

eauto with lia -- proves goals about linear (in)equations in the integers / natural numbers.



Note that you can often combine `iDestruct` and `iIntros`.
For example, `iIntros [H1 H2]` does `iIntros` and then immediately destruct it.

*)

End coq_intro.
