From iris.heap_lang Require Import notation proofmode par.
From iris.algebra Require Import agree csum excl.
From iris.base_logic.lib Require Import invariants.
From iris Require Import prelude.
Require Import examples.basic.

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

Lemma shoot_init : ⊢ |==> ∃ γ, own γ Pending.
Proof.
  iApply own_alloc.
  done.
Qed.

Lemma shoot_upd γ : own γ Pending ==∗ own γ Shot.
Proof.
  iApply own_update.
  apply shoot.
Qed.

Instance shot_persistent γ : Persistent (own γ Shot).
Proof.
  eapply own_core_persistent.
  econstructor. done.
Qed.

Lemma shot_not_pending γ : own γ Shot -∗ own γ Pending -∗ False.
Proof.
  iIntros "H1 H2".
  iPoseProof (own_valid_2 with "H1 H2") as "%H".
  cbv in H.
  done.
Qed.

End ghost_state.

Section parallelism.

Context `{!heapGS Σ, !one_shotG Σ, !spawnG Σ}.

Definition flag_before_update : Z := 0.
Definition flag_during_update : Z := 1.
Definition flag_after_update : Z := 2.

Definition thread_body  : val :=
  rec: "thread_body" "flag" "loc" :=
    let: "pp" := CmpXchg "flag" #flag_before_update #flag_during_update in
    let: "old_value" := Fst "pp" in
    let: "did_exchange" := Snd "pp" in
    if: "did_exchange"
      then
        "loc"  <- ! "loc" + #2 ;;
        "flag" <- #flag_after_update
      else if: "old_value" = #flag_during_update
        then 
          "thread_body" "flag" "loc"
        else #().

Definition main : expr :=
  let: "flag" := ref #flag_before_update in
  let: "x" := ref #2 in
  (thread_body "flag" "x" |||
    thread_body "flag" "x") ;;
  ! "x".

(* Here come the proofs *)


Definition flag_invariant γ flag loc : iProp Σ :=
  ∃ f, flag ↦ #f ∗
    (loc ↦ #2 ∗ ⌜f = flag_before_update⌝ ∗ own γ Pending ∨
     ⌜f = flag_during_update⌝ ∗ own γ Pending ∨
     loc ↦ #4 ∗ ⌜f = flag_after_update⌝ ∗ own γ Shot).

Lemma thread_helper γ flag loc N :
  inv N (flag_invariant γ flag loc)
  ⊢ WP (thread_body #flag #loc) {{ _, own γ Shot }}.
Proof.
  iIntros "#Hinv".
  iLöb as "IH".
  wp_rec. wp_pures.
  (* Focus on the CmpXchg, since it must be atomic *)
  wp_bind (CmpXchg _ _ _).
  (* Open the invariant *)
  iInv "Hinv" as ">(%f&Hflag&Hcases)" "Hclose".
  (* The invariant has a bunch of cases, let's analyze them *)
  iDestruct "Hcases" as "[(Hloc&->&Hpending)|[(->&Hpending)|(Hloc&->&#Hshot)]]".
  - (* In this case, the CmpXchg will succeed *)
    wp_cmpxchg_suc.
    (* This is how we close the invariant. We need "Hpending" and "Hflag" to go back into it *)
    iMod ("Hclose" with "[$Hflag Hpending]") as "_".
    { iNext. iRight. iLeft. iFrame "Hpending". done. }
    iModIntro.
    (* TODO: Now we increment by 2. *)

    (* Now we did the incrementing, we need to open the invariant again to update the flag. *)
    iInv "Hinv" as ">(%f&Hflag&Hcases)" "Hclose".
    iDestruct "Hcases" as "[(Hc&_)|[(->&Hpending)|(Hc&_)]]".
    1: { iExFalso.
        (* TODO: This is contradictory. Use `only_one_pointsto` *) }
    2: { (* TODO like case 1*) }
    (* TODO: Update the flag. *)
    
    (* The key part. Update to `Shot` *)
    iMod (shoot_upd with "Hpending") as "#Hshot".
    (* And now, we can close the invariant again. Then, we are done. *)
    iMod ("Hclose" with "[$Hflag Hloc]") as "_".
    { iNext. 
      (* TODO: close the invariant. Hint: We are now in the third case. *) }
    iModIntro. done.
  - wp_cmpxchg_fail. 1: done.
    iMod ("Hclose" with "[$Hflag Hpending]") as "_".
    (* This closes the invariant. Perhaps take inspiration here for some other todos :) *)
    { iNext. iRight. iLeft. iFrame "Hpending". done. }
    iModIntro.
    do 8 wp_pure _.
    do 2 wp_pure _.
    wp_pure _.
    (* Magic: we loop again. But since it is OK to loop forever, we can prove this case. The details go beyond this tutorial. *)
    iApply "IH".
  - wp_cmpxchg_fail. 1: done.
    iMod ("Hclose" with "[$Hflag Hloc]") as "_".
    { iNext. (* TODO: close the invariant again. *) }
    iModIntro.
    (* TODO: We are actually done here, since we know we are already "Shot". So there is nothing really left to do.*)
Qed.

Lemma threads :
  ⊢ WP main {{ v, ⌜v = #4⌝ }}.
Proof.
  unfold main.
  (* TODO: allocate the initial data *)
  
  (* Let's allocate the one-shot ghost state, and the invariant *)
  iMod shoot_init as "(%γ&Hpending)".
  iMod (inv_alloc nroot _ (flag_invariant γ flag loc) with "[$Hflag Hloc Hpending]") as "#Hinv".
  { iNext. iLeft. iFrame "Hloc Hpending". done. }
  wp_bind (par _ _).
  iApply wp_par.
  (* Now we handle both threads *)
  { (* TODO: Use the `thread_helper` lemma from above. *) }
  { (* TODO: The other thread. Same proof as the first. *) }
  simpl.
  (* Sometimes, we care about what our threads produce (v1 and v2). Here we do not. *)
  iIntros (v1 v2) "(Hshot&_)".
  iNext. wp_pures.
  (* Open the invariant again. We should now be in the third state. *)
  iInv "Hinv" as ">(%f&Hflag&Hcases)" "Hclose".
  iDestruct "Hcases" as "[(Hloc&->&Hpending)|[(->&Hpending)|(Hloc&->&#Hshot2)]]".
  { iExFalso. (* TODO: This case is impossible. Use `shot_not_pending` *) }
  { iExFalso. (* TODO: as above *) }
  (* TODO: do the load *)
  
  (* Let's close the invariant again. *)
  iMod ("Hclose" with "[$Hflag Hshot Hloc]") as "_".
  { iNext. (* TODO: Which case are we in again? *) }
  (* And then, we are actually _done_ *)
  done.
Qed.

End parallelism.
