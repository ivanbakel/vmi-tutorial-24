From iris.heap_lang Require Import notation proofmode.
From iris Require Import prelude.

Section basic.

Context `{!heapGS Σ}.

Lemma load_value x v :
  {{{ x ↦ v }}}
    ! #x
  {{{ RET v; x ↦ v }}}.
Proof.
  iIntros (Φ) "Hx HΦ".
  wp_load.
  iApply "HΦ".
  iFrame "Hx".
  done.
Qed.

Lemma store_value x v v':
  {{{ x ↦ v }}}
    #x <- v'
  {{{ RET #(); x ↦ v' }}}.
Proof.
  iIntros (Φ) "Hx HΦ".
  wp_store.
  iApply "HΦ".
  iFrame "Hx".
  done.
Qed.

Lemma alloc_value v :
  {{{ True }}}
    let: "x" := ref #v in
    ! "x"
  {{{ RET #v; True }}}.
Proof.
  iIntros (Φ) "Htrue HΦ".
  wp_alloc l as "Hl".
  wp_let.
  wp_load.
  iApply "HΦ".
  done.
Qed.

Lemma load_add_store x (n : Z) :
  {{{ x ↦ #n }}}
    #x <- !#x + #1
  {{{ RET #(); x ↦ #(n + 1) }}}.
Proof.
  iIntros (Φ) "Hx HΦ".
  wp_load.
  wp_pures.
  wp_store.
  iApply "HΦ".
  iFrame "Hx".
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
  {{{ True }}}
    let: "x" := ref #0 in
    "x" <- !"x" + #2 ;;
    "x" <- !"x" + #2 ;;
    ! "x"
  {{{ RET #4; True }}}.
Proof.
  (* TODO: Fill in! *)
  Admitted.

End basic.
