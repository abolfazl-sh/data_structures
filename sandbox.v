From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.
From iris.base_logic.lib Require Export invariants.


Section spec1.
Context `{heapGS Σ}.

Let N := nroot .@ "counter".

Definition variable : val :=
    λ: <>, ref #0.

Definition is_variable (v : val) (n: nat) : iProp Σ :=
   ∃ l : loc, ⌜v = #l⌝ ∗  inv N (∃ m : nat, l ↦ #m ∗ ⌜n ≤ m⌝). 

Definition plus1 : val :=
λ: "x",  
"x" + #1.

Lemma wp_plus1 (v : val) (n: nat) : 
   {{{is_variable v n}}}
      plus1 (! v) 
   {{{(k : nat), RET #k; ⌜n ≤ k%Z⌝}}}.
Proof.
  iIntros (Φ) "Hv HΦ".
  iDestruct "Hv" as (l) "#Hinv".
  iDestruct "Hinv" as "[%Hvl #Hinv]".
  rewrite Hvl.
  rewrite /plus1.
  wp_bind (! #l)%E.
  iInv N as (m) "[>Hl >%Hnm]" "Hclose".
  wp_load.
  iMod ("Hclose" with "[Hl]") as "AAA".
  { iNext. iExists m. iFrame. iPureIntro. lia. }
  iModIntro.
  wp_pures.
  iSpecialize ("HΦ" $! (m + 1)%nat).
  rewrite Nat2Z.inj_add.
  iApply "HΦ".
  iPureIntro. lia.
Qed.



   