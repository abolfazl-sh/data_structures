From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import own.

Section UnboundedQueue.
Context `{!heapGS Σ, !inG Σ (excl_authR (leibnizO (list val)))}.

Let M := nroot .@ "queue".

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
  | y :: ys => ∃ n : loc, from ↦□ y ∗ (from +ₗ 1) ↦□ SOMEV #n ∗ isList n to ys
  end.

Definition queueInv (head tail : loc) (γ: gname) : iProp Σ :=
  ∃ (hd td l : loc) (d lv : val) (ys zs xs : list val),
    head ↦ #hd ∗ tail ↦ #td ∗
    isList hd td ys ∗          
    isList td l zs ∗            
    l ↦□ lv ∗
    (l +ₗ 1) ↦ NONEV ∗ 
    ⌜d :: xs = ys ++ zs ++ [lv]⌝ ∗
    own γ (●E (xs : leibnizO (list val))).
Definition isQueue (head tail : loc) (γ : gname) (xs : list val) : iProp Σ :=
  inv M (queueInv head tail γ) ∗ own γ (◯E (xs : leibnizO (list val))).

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
  isList hd td ys -∗ td ↦□ v'  -∗ (td +ₗ 1) ↦□ SOMEV #n -∗ 
  isList hd n (ys ++ [v']).
Proof.
  induction ys in hd |- *.    
  -iIntros "HL HT HTP". simpl.
  iExists n. iDestruct "HL" as %Heq. rewrite Heq. iFrame. iPureIntro. reflexivity.
  -iIntros "HL HT HTP". simpl.
  iDestruct "HL" as (n0) "[HD HDN]". iFrame.
  iDestruct "HDN" as "[HDN HDL]". iExists n0. iFrame. iApply (IHys n0 with "HDL HT HTP").
 Qed. 

Lemma queue_spec (v : val) (head tail : loc) (γ : gname) (xs : list val):
{{{ isQueue head tail γ xs }}}
 enq v (#head, #tail)
 {{{RET #(); isQueue head tail γ (xs ++ [v])}}}.
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
  iDestruct "HQ" as "[#Hinv Hfrag]".
  wp_bind (! #tail)%E.
  unfold queueInv.

  iInv "Hinv" as (hd td l d lv ys zs xs0) "(Hhead & Htail & Hys & Hzs & Hl & Hl2  & >Hdxs & Hγ)" "Hiclose".
  wp_load.
  
  iMod ("Hiclose" with "[Hhead Htail Hys Hdxs Hzs Hl Hl2  Hγ]" ) as "_".
  {
    iNext. iExists hd, td, l, d, lv, ys, zs, xs0. iFrame. 
  }
  iModIntro.
  wp_let.
  wp_pures.
  wp_bind(! #(td +ₗ 1))%E.
  iInv "Hinv" as (hd' td' l' d' lv' ys' zs' xs0') "(Hhead & Htail & Hys & Hzs & Hl & Hl2 & >Hdxs & Hγ)" "Hiclose".

  iMod ("Hiclose" with "[Hhead Htail Hys Hdxs Hzs Hl Hl2 Hγ]" ) as "_".
  {
    iNext. iExists hd', td', l', d', lv', ys', zs', xs0'. iFrame. 
  }
 Admitted.



  
End UnboundedQueue.