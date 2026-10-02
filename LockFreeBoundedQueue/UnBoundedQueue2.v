From iris.heap_lang Require Import lang proofmode notation.

Section UnboundedQueue.
Context `{!heapGS Σ}.

Definition node : val :=
  λ: "value",
    let: "cell" := AllocN #2 "value" in
    "cell" +ₗ #1 <- NONE;;
    "cell".

Definition queue : val :=
  λ: <>,
    let: "n" := node #0 in
    let: "head" := ref "n" in
    let: "tail" := ref "n" in
    ("head", "tail").

Fixpoint isList (from to : loc) (ys : list val) : iProp Σ :=
  match ys with
  | [] => ⌜from = to⌝
  | y :: ys => ∃ n : loc, from ↦ y ∗ (from +ₗ 1) ↦ SOMEV #n ∗ isList n to ys
  end.

Definition isQueue (head tail : loc) (xs : list val) : iProp Σ :=
  ∃ (hd td : loc) (d v : val) (ys : list val),
    head ↦ #hd ∗ tail ↦ #td ∗
    isList hd td ys ∗
    td ↦ v ∗ (td +ₗ 1) ↦ NONEV ∗
    ⌜d :: xs = ys ++ [v]⌝.

Definition enq : val :=
  λ: "value" "queue",
    let: "n" := node "value" in
    let: "tail" := Snd "queue" in
    (rec: "insert" <> :=
       let: "last" := !"tail" in
       let: "next" := !("last" +ₗ #1) in
       if: "last" = !"tail" then
         match: "next" with
           NONE =>
             if: CAS ("last" +ₗ #1) "next" (SOME "n") then
               CAS "tail" "last" "n";; #()
             else "insert" #()
         | SOME "l" =>
             CAS "tail" "last" "l";;
             "insert" #()
         end
       else "insert" #()) #().

Definition deq : val :=
  rec: "deq" "queue" :=
    let: "head" := Fst "queue" in
    let: "tail" := Snd "queue" in
    let: "first" := !"head" in
    let: "last" := !"tail" in
    let: "next" := !("first" +ₗ #1) in
    if: "first" = !"head" then
      if: "first" = "last" then
        match: "next" with
          NONE => NONE
        | SOME "n" =>
            CAS "tail" "last" "n";;
            "deq" "queue"
        end
      else
        match: "next" with
          NONE => "deq" "queue"
        | SOME "n" =>
            let: "v" := !"n" in
            if: CAS "head" "first" "n" then SOME "v" else "deq" "queue"
        end
    else "deq" "queue".

Lemma node_spec (v : val) :
  {{{ True }}}
    node v
  {{{ (n : loc), RET #n; n ↦ v ∗ (n +ₗ 1) ↦ NONEV }}}.
Proof.
    iIntros  "%φ %H Hn".
    wp_rec.
    wp_alloc l as "Hl".
    - reflexivity.
    - wp_let.
    wp_pures.
    simpl.
    iDestruct (array_cons with "Hl") as "[Hl0 Hl1]".
    iEval (rewrite array_singleton) in "Hl1".
    wp_store.
    iApply "Hn".
    iModIntro.
    iFrame.
Qed.
Set Printing Depth 1000.

Lemma isList_spec (hd td n: loc) ys v' :
  isList hd td ys -∗ td ↦ v'  -∗ (td +ₗ 1) ↦ SOMEV #n -∗ 
  isList hd n (ys ++ [v']).
Proof.
  induction ys in hd |- *.    
  -iIntros "HL HT HTP". simpl.
  iExists n. iDestruct "HL" as %Heq. rewrite Heq. iFrame. iPureIntro. reflexivity.
  -iIntros "HL HT HTP". simpl.
  iDestruct "HL" as (n0) "[HD HDN]". iFrame.
  iDestruct "HDN" as "[HDN HDL]". iExists n0. iFrame. iApply (IHys n0 with "HDL HT HTP").
 Qed. 

Lemma queue_spec (v : val) (head tail : loc) (xs : list val):
{{{ isQueue head tail xs }}}
 enq v (#head, #tail)
 {{{RET #(); isQueue head tail (xs ++ [v])}}}.
 Proof.
  iIntros "%φ HQ HQV" .
  unfold enq.
  wp_pures.
  wp_apply node_spec.
  - iFrame.
  -iIntros "%n Hn".
  wp_let.
  wp_proj.
  wp_let.
  wp_pures.
  iDestruct "HQ" as (hd td d v' ys) "(Hhead & Htail & Hlist & Htd & Htd1 & %Hxs)".
  wp_load.
  wp_let.
  wp_load.
  wp_let.
  wp_load.
  wp_op.
  rewrite bool_decide_eq_true_2. wp_if.
  wp_pures.
  wp_cmpxchg_suc.
  wp_pures.
  wp_cmpxchg_suc.
  wp_pures.
  iApply "HQV".
  iModIntro.
  unfold isQueue.
  iExists hd, n, d, v, (ys ++ [v']).
  iDestruct "Hn" as "[Hl0 Hl1]".
  iFrame.
  iSplit.
   + iApply (isList_spec hd td n ys v' with "Hlist Htd Htd1").
   + iPureIntro. rewrite <- Hxs. reflexivity.
   + reflexivity.
 Qed.



  
End UnboundedQueue.