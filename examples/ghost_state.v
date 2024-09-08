From iris.heap_lang Require Import notation proofmode par.
From iris.algebra Require Import agree csum excl.
From iris.base_logic.lib Require Import invariants.
From iris Require Import prelude.

Section ghost_state.

Definition one_shotR := csumR (exclR unitR) (agreeR unitR).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot : one_shotR := Cinr (to_agree ()).

Lemma shoot : Pending ~~> Shot.
Proof.
  apply cmra_update_exclusive.
  done.
Qed.

Class one_shotG Σ := { one_shot_inG : inG Σ one_shotR }.
Global Existing Instance one_shot_inG.

Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Context `{!heapGS Σ, !one_shotG Σ}.

Lemma shoot_upd γ : own γ Pending ==∗ own γ Shot.
Proof.
  iApply own_update.
  apply shoot.
Qed.

End ghost_state.

Section parallelism.

Context `{!heapGS Σ, !one_shotG Σ}.

Definition flag_before_update : Z := 0.
Definition flag_during_update : Z := 1.
Definition flag_after_update : Z := 2.

Definition flag_invariant γ flag loc : iProp Σ :=
  ∃ f, flag ↦ #f ∗
    (loc ↦ #2 ∗ ⌜f = flag_before_update⌝ ∗ own γ Pending ∨
     ⌜f = flag_during_update⌝ ∨
     loc ↦ #4 ∗ ⌜f = flag_after_update⌝ ∗ own γ Shot).

Definition thread_body (flag loc : expr) : expr :=
  rec: "thread_body" "_" :=
    if: CAS flag #flag_before_update #flag_during_update
      then
        loc  <- ! loc + #2 ;;
        flag <- #flag_after_update
      else
        if: !flag = #flag_during_update
          then "thread_body" #()
          else #().

Lemma thread_helper γ flag loc N :
  inv N (flag_invariant γ flag loc)
  ⊢ WP (thread_body #flag #loc) {{ _, own γ Shot }}.
Admitted.

Definition main : expr :=
  let: "flag" := ref #flag_before_update in
  let: "x" := ref #2 in
  (thread_body "flag" "x" #() ||| 
    thread_body "flag" "x" #()) ;;
  ! "x".

Lemma threads :
  ⊢ WP main {{ v, ⌜v = #4⌝ }}.
Admitted.

End parallelism.
