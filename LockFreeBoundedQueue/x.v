From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Export invariants.

Section UnboundedQueue.
Context `{!heapGS Σ}.

Let N := nroot .@ "list".

Definition test (x : loc) : iProp Σ :=
    inv N (x ↦ #2).

Definition incr (x : nat) : val :=
    λ: "l", "l" <- #3.

Theorem a (v : val) : 
    {{{True}}}

    {{{}}}.