From iris.heap_lang Require Import notation proofmode.
From iris Require Import prelude.

Section basic.

Context `{!heapGS Σ}.

Implicit Types v u : val.
Implicit Types l k : loc.

(* Iris is a tool for program reasoning using separation logic.

   Separation logic is a logic for reasoning about program heaps - finite
   maps from locations to value. It includes propositions like [l ↦ v], that
   the heap location [l] maps to the value [v] in the heap. The most important
   feature of separation logic is the separating conjunction [∗], which is a
   binary operator. [P ∗ Q] says that the propositions [P] and [Q] are true
   under a *partition* of the heap into two disjoint parts i.e. some part of
   the heap makes [P] true, another part makes [Q] true, and they don't overlap
   in their locations.

   This turns out to be useful for many reasons. For example, if we are talking
   about two heap locations, we automatically learn that they aren't the same. *)

Lemma disjoint l k v u:
  l ↦ v ∗ k ↦ u ⊢ ⌜l ≠ k⌝.
Proof.
  iIntros "[Hl Hk]".
  iApply (mapsto_ne with "Hl Hk").
Qed.

(* Program reasoning in Iris can be done in various ways. For this tutorial we
   use *weakest preconditions*. The weakest precondition (WP) of an expression is
   parameterised by a post-condition. For a given post-condition, the WP is the
   statement that guarantees that the expression executes correctly, and that
   afterwards, the post-condition is true.

   For example, the weakest precondition [WP ! #l {{ v, P v }}] is the proposition
   that will let us read from [l] ([!] is a load), such that the value read from
   [l] satisfies [P]. Clearly, for this to be true, [l] must hold a value that
   satisfies [P] already - all we do is read from it! Therefore, we expect to be
   able to prove this WP just from knowing that [l ↦ v ∗ P v]. *)

Lemma load_value l v :
  l ↦ v ⊢
  WP ! #l
  {{ v, l ↦ v }}.
Proof.
  iIntros "Hl".
  wp_load.
  iFrame "Hl".
  done.
Qed.

Lemma store_value l v u:
  l ↦ v ⊢
  WP #l <- u
  {{ _, l ↦ u }}.
Proof.
  iIntros "Hl".
  wp_store.
  iFrame "Hl".
  done.
Qed.

(* The variable mentioned in the post-condition of a WP is the value that the
   expression evaluates to. We can relate this value to other values in the
   program in any number of ways. *)

Lemma alloc_value v :
⊢ WP let: "x" := ref v in
     ! "x"
  {{ v', ⌜v' = v⌝ }}.
Proof.
  wp_alloc l as "Hl".
  wp_let.
  wp_load.
  iModIntro.
  done.
Qed.

Lemma load_add_store l (n : Z) :
  l ↦ #n ⊢ 
  WP #l <- !#l + #1
  {{ _,  l ↦ #(n + 1) }}.
Proof.
  iIntros "Hl".
  wp_load.
  wp_pures.
  wp_store.
  iFrame "Hl".
  done.
Qed.

(* For this one, you will need to do some *arithmetic*! However, the results
   you'll want to apply are trivial, and Coq can handle them with the `lia`
   tactic.

   The easiest approach is to tell Coq that you want to `replace` one term by
   another, and that the replacement is justified because they're mathematically
   the same. This can be done like so:

   >>> replace (...)%Z with (...)%Z by lia.

   where the things inside the brackets are the term you want to replace, and its
   replacement. The `%Z` marker tells Coq to interpret the terms as integers. This
   tactic generates a subgoal for the replacement, which `lia` immediately solves. *)
Lemma two_plus_two_is_four :
⊢ WP let: "x" := ref #0 in
     "x" <- !"x" + #2 ;;
     "x" <- !"x" + #2 ;;
    ! "x"
  {{ v, ⌜v = #4⌝ }}.
Proof.
  (* TODO: Fill in! *)
Admitted.

End basic.
