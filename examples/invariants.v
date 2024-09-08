From iris.base_logic Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris Require Import prelude.

Section invariants.

Context `{!heapGS Σ}.

(* Here we will begin to see the power of invariants. Invariants record facts
   that are maintained by the program which can be relied on in our proofs,
   including for concurrent programs.

   The notation [inv N P], where P is a proposition, means that (in the namespace
   N, which we don't care about here), we have an invariant holding the fact P.

   We can create new invariants by proving the fact that they hold is true. *)

Lemma inv_alloc N :
  ⊢ WP ref #1 {{ x, ∃ (l : loc), ⌜#l = x⌝ ∗ inv N (∃ (n : Z), l ↦ #n ∗ ⌜(n > 0)%Z⌝) }}.
Proof.
  wp_alloc x as "Hx".
  iExists x.
  iSplitL ""; first done.
  iApply (inv_alloc with "[Hx]").
  iNext.
  iExists 1.
  iFrame "Hx".
  eauto with lia.
Qed.

(* We also want to use facts held in invariants (because we know they're true!)
   But this can't be done directly. Instead, we need to *open* the invariant to
   use the fact.

   Opening an invariant creates an obligation that the fact needs to *stay* true.
   Once we reestablish a fact, we can close the invariant and continue with the
   proof. All this has to happen in the same program step, for correctness. *)

Lemma read_inv x N :
  inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝)
  ⊢ WP ! #x {{ v, ∃ (n : Z), ⌜#n = v⌝ ∗  ⌜(n > 0)%Z⌝}}.
Proof.
  iIntros "#Hinv".
  Fail wp_load.
  iInv "Hinv" as (n) ">[Hx %Hge0]" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists n.
    iFrame "Hx".
    eauto with lia. }
  iExists n.
  done.
Qed.

(* The proof with which we close an invariant doesn't have to be identical to
   the one that opens an invariant. If, in the program step where we open the
   invariant, we change the program state, we might have to reestablish the
   invariant fact with a *new* proof.

   Here, for example, we open the invariant and get a proof that the location
   [x] points to an integer [n]. However, we have to close the invariant with a
   different [n] - because we incremented it! *)

Lemma fetch_and_add_inv x N :
  inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝)
  ⊢ WP FAA #x #1 {{ v, ∃ (n : Z), ⌜#n = v⌝ ∗ ⌜(n > 0)%Z⌝ }}.
Proof.
  iIntros "#Hinv".
  iInv "Hinv" as (n) ">[Hx %Hge0]" "Hclose".
  wp_faa.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists (n + 1)%Z.
    iFrame "Hx".
    eauto with lia. }
  iExists n.
  done.
Qed.

(* Remember that we can only correctly open invariants around single program
   steps. To use an invariant fact over multiple program steps, we need to use
   tricks. One trick might be to open the invariant repeatedly, once per program
   step. This is what we do here.

   NB: this approach is very weak, and for a good reason. We can't prove that we
   double the value of [x] - and indeed, thanks to concurrency, we might not!
   Other threads might modify [x] between us reading and writing it. *)
Lemma non_atomic_op_inv x N :
  inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝)
  ⊢ WP #x <- #2 * ! #x {{ _, True }}.
Proof.
  iIntros "#Hinv".
  wp_bind (! _)%E.
  iInv "Hinv" as (n) ">[Hx %Hge0]" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists n.
    iFrame "Hx".
    eauto with lia. }
  iModIntro.
  wp_pures.
  iInv "Hinv" as (?) ">[Hx _]" "Hclose".
  wp_store.
  iMod ("Hclose" with "[Hx]").
  { iNext.
    iExists (2 * n)%Z.
    iFrame "Hx".
    eauto with lia. }
  done.
Qed.

(* Similarly here, we can't prove that we read the same value twice from [x],
   because it may have changed due to concurrency. In reality, we use different
   techniques to specify programs such as this one if we want a stronger result. *)

Lemma multiread x N :
  inv N (∃ (n : Z), x ↦ #n ∗ ⌜(n > 0)%Z⌝)
  ⊢ WP
    let: "n1" := ! #x in
    let: "n2" := ! #x in
    "n1" + "n2"
    {{ v, ∃ (n : Z), ⌜#n = v⌝ ∗ ⌜(n > 0)%Z⌝ }}.
Proof.
  (* Always introduce the invariant - it's "persistent", so it gets a "#" *)
  iIntros "#Hinv".
  (* TODO: Fill in! *)
  Admitted.

End invariants.
