From iris.prelude Require Import options.
From iris.algebra Require Import gmultiset.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Export fractional.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang.lib Require Export rw_lock.
From iris.prelude Require Import options.


Section invariants.

Context `{!heapGS Σ}.

Lemma inv_alloc N :
  {{{ True }}}
    ref #1
  {{{ x, RET #x; inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝) }}}.
Proof.
  iIntros (Φ) "Htrue HΦ".
  wp_alloc x as "Hx".
  iApply "HΦ".
  iApply (inv_alloc with "[Hx]").
  iNext.
  iExists 1.
  iFrame "Hx".
  iPureIntro.
  lia.
Qed.

Lemma read_inv x N :
  {{{ inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝) }}}
    ! #x
  {{{ n, RET #n; ⌜(n > 0)%Z⌝}}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  Fail wp_load.
  iInv "Hinv" as (n) ">[Hx %Hge0]" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists n.
    iFrame "Hx".
    iPureIntro.
    lia. }
  iApply "HΦ".
  done.
Qed.

Lemma fetch_and_add_inv x N :
  {{{ inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝) }}}
    FAA #x #1
  {{{ n, RET #n; ⌜(n > 0)%Z⌝ }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  iInv "Hinv" as (n) ">[Hx %Hge0]" "Hclose".
  wp_faa.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists (n + 1)%Z.
    iFrame "Hx".
    iPureIntro.
    lia. }
  iApply "HΦ".
  done.
Qed.

Lemma non_atomic_op_inv x N :
  {{{ inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝) }}}
    #x <- #2 * ! #x
  {{{ RET #() ; True }}}.
Proof.
  iIntros (Φ) "#Hinv HΦ".
  wp_bind (! _)%E.
  iInv "Hinv" as (n) ">[Hx %Hge0]" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists n.
    iFrame "Hx".
    iPureIntro.
    lia. }
  iModIntro.
  wp_pures.
  iInv "Hinv" as (?) ">[Hx _]" "Hclose".
  wp_store.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists (2 * n)%Z.
    iFrame "Hx".
    iPureIntro.
    lia. }
  iApply "HΦ".
  done.
Qed.

Lemma multiread x N :
  {{{ inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝) }}}
    let: "n1" := ! #x in
    let: "n2" := ! #x in
    "n1" + "n2"
  {{{ n, RET #n ; ⌜(n > 0)%Z⌝ }}}.
Proof. (* TODO: Fill in! *)
  Admitted.

End invariants.
