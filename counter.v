From iris.algebra Require Export auth excl frac numbers.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.


Definition counter : val :=
    λ: <>, ref #0.

Definition increment : val :=
    rec: "incr" "c" :=
    let: "n" := !"c" in 
    let: "m" := !"c" + #1 in 
    if: CAS "c" "n" "m" then "n" else "incr" "c".

Definition read : val :=
    λ: "c", !"c".

Module spec1.
Section spec1.
Context `{heapGS Σ}.

Definition is_counter(v : val) (n : nat) : iProp Σ :=
    ∃ l : loc, ⌜v = #l⌝ ∗ l ↦ #n.

Let N := nroot .@ "counter".

Definition is_counter1(v : val) (n : nat) : iProp Σ :=
    ∃ l : loc, ⌜v = #l⌝ ∗ inv N (l ↦ #n).
    
Definition is_counter2(v : val) (n : nat) : iProp Σ := 
    ∃ l : loc, ⌜v = #l⌝ ∗ inv N (∃ m: nat, l ↦ #m ∗ ⌜n ≤ m⌝).

Context `{!inG Σ (authR max_natUR)}.

Definition is_counter3(v : val) ( γ : gname ) (n : nat) : iProp Σ :=
    ∃ l : loc, ⌜v = #l⌝ ∗ own γ (◯ MaxNat n) ∗ 
    inv N (∃ m : nat, l ↦ #m ∗ own γ (● MaxNat m)).

Global Instance is_counter_persistent v γ n :
  Persistent (is_counter3 v γ n) := _.


Lemma alloc_initial_state : 
    ⊢ |==> ∃ γ, own γ (● MaxNat 0) ∗ own γ (◯ MaxNat 0).
Proof.
    setoid_rewrite <- own_op.
    apply own_alloc.
    apply auth_both_valid_discrete.
    split.
    - apply max_nat_included. simpl.
    reflexivity.
    - cbv.
    done.
Qed.

Lemma state_valid γ n m :
    own γ (● MaxNat n) -∗
    own γ (◯ MaxNat m) -∗
    ⌜m ≤ n⌝.
Proof.
    iIntros "Hm Hn".
    iPoseProof (own_valid_2 with "Hm Hn") as "%H".
    iPureIntro.
    apply auth_both_valid_discrete in H.
    destruct H as [H1 H2].
    apply max_nat_included in H1. simpl in H1.
    apply H1.
Qed.


