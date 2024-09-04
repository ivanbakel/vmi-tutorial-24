From iris.heap_lang Require Import notation proofmode.
From iris Require Import prelude.

Section basic.

Context `{!heapGS Σ}.

Implicit Type v : val.
Implicit Type l : loc.

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

Lemma store_value l v v':
  l ↦ v ⊢
  WP #l <- v'
  {{ _, l ↦ v' }}.
Proof.
  iIntros "Hl".
  wp_store.
  iFrame "Hl".
  done.
Qed.

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
