From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Export invariants.

Section LobExercises.
Context `{!heapGS Σ}.

Let N := nroot .@ "flag".


Definition diverge : val := rec: "f" <> := "f" #().

Lemma diverge_spec : ⊢ WP diverge #() {{ _, False }}.
Proof.
    iLöb as "IH".
    rewrite /diverge.
    wp_rec.
    iApply "IH".
Qed.

Definition wait : val :=
  rec: "wait" "l" :=
    if: !"l" then #() else "wait" "l".

Lemma wait_spec (l : loc) :
  inv N (∃ b : bool, l ↦ #b) -∗ WP wait #l {{ _, True }}.
Proof.
    iIntros "#inv".
    iLöb as "IH".
    rewrite /wait.
    wp_rec.
    wp_bind (! #l)%E.
    iInv "inv" as (b) "Hl" "Hclose".
    wp_load.
    iMod ("Hclose" with "[Hl]") as "_".
    - iExists b. iNext. iFrame.
    - iModIntro.
    destruct b.
    + wp_if_true. done.
    + wp_if_false. iApply "IH".
Qed. 