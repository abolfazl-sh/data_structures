From iris.heap_lang Require Import lang proofmode notation.
From iris.base_logic.lib Require Export invariants.
From iris.algebra Require Import excl_auth.
From iris.base_logic.lib Require Import own.
From iris.bi.lib Require Import fixpoint_mono.

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


Global Instance isList_timeless from to ys : Timeless (isList from to ys).
Proof.
  revert from.
  induction ys as [|y ys IH]; intros from; simpl; apply _.
Qed.

Global Instance isList_persistent from to ys : Persistent (isList from to ys).
Proof.
  revert from.
  induction ys as [|y ys IH]; intros from; simpl; apply _.
Qed.

Definition queueInv (root head tail: loc) (γ: gname) : iProp Σ :=
  ∃ (hd td l: loc) (d lv : val) (gone ys zs xs : list val),
    head ↦ #hd ∗ tail ↦ #td ∗
    isList hd td ys ∗          
    isList td l zs ∗      
    isList root hd gone ∗      
    l ↦□ lv ∗
    (l +ₗ 1) ↦ NONEV ∗ 
    ⌜d :: xs = ys ++ zs ++ [lv]⌝ ∗
    own γ (●E (xs : leibnizO (list val))).

Definition isQueue (root head tail : loc) (γ : gname) (xs : list val) : iProp Σ :=
  inv M (queueInv root head tail γ) ∗ own γ (◯E (xs : leibnizO (list val))).

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

Lemma nextNode  (td l: loc):
    ∃ v v', (⌜td = l⌝ ∧ (td +ₗ 1) ↦□ NONEV) ∨ td ↦□ SOMEV(v') -∗ td ↦ SOMEV(v) .
Admitted.

Definition reach_pre (Φ : prodO locO locO → iProp Σ) :
    prodO locO locO → iProp Σ :=
  λ '(x, z), (⌜x = z⌝ ∨ ∃ y : loc, (x +ₗ 1) ↦□ SOMEV #y ∗ Φ (y, z))%I.

Definition Reach (x z : loc) : iProp Σ :=
  bi_least_fixpoint reach_pre (x, z).

Lemma isList_Reach(hd td : loc) ys :
  isList hd td ys -∗ Reach hd td.
Admitted.

Lemma reach_last(root td l: loc) ys :
    isList root l ys -∗ Reach root td -∗ (l +ₗ 1) ↦ NONEV -∗
    (l +ₗ 1) ↦ NONEV ∗ ((⌜td = l⌝) ∨ (∃ n, (td +ₗ 1) ↦□ SOMEV #n)).
Admitted.

Lemma isList_app (a b c : loc) ys zs :
    isList a b ys -∗ isList b c zs -∗ isList a c (ys ++ zs).
Admitted.

 Lemma queue_spec (v : val) (root head tail : loc) (γ : gname) (xs : list val):
{{{ isQueue root head tail γ xs }}}
 enq v (#head, #tail)
 {{{RET #(); isQueue root head tail γ (xs ++ [v])}}}.
 Proof.   
    iIntros "%φ [#Hinv Hown] Hn".
    iLöb as "H".
    rewrite /enq.
    rewrite /isQueue.
    wp_pures.
    wp_bind(node v).
    rewrite /node.
    wp_pures.
    wp_alloc l as "Hl". {reflexivity. }
    wp_let.
    wp_pures.
    iDestruct (array_cons with "Hl") as "[Hl0 Hl1]".
    iDestruct (array_singleton with "Hl1") as "Hl1".
    wp_store.
    wp_let.
    wp_pures.
    wp_bind(! #tail)%E.

    (*loading last*)
    iInv "Hinv" as (hd1 td1 l1 d1 lv1 gone1 ys1 zs1 xs1) 
    "(>Hhead1 & >Htail1 & >HLt1 & >HLl1 & >Hgone1 & >Hlast1 & >HNl1 & >Hdx1 & >Hown1)" "Hclose1".
    wp_load.
    iDestruct (isList_app with "Hgone1 HLt1") as "#Hpre".

    iMod ("Hclose1" with "[Hhead1 Htail1 HLt1 HLl1 Hgone1 Hlast1 HNl1 Hdx1 Hown1]") as "_".
    {
     iNext. rewrite /queueInv.
     iExists hd1, td1, l1,  d1, lv1, gone1, ys1, zs1, xs1.
     iFrame. 
    }
    iModIntro.

    (*loading the next of last*)
    wp_let.
    wp_pures.
    wp_bind(! #(td1 +ₗ 1))%E.
        iInv "Hinv" as (hd2 td2 l2 d2 lv2 gone2 ys2 zs2 xs2) 
    "(>Hhead2 & >Htail2 & >HLt2 & >HLl2 & >Hgone2 & >Hlast2 & >HNl2 & >Hdx2 & >Hown2)" "Hclose2".
    iDestruct(isList_app with "Hgone2 HLt2") as "HRT".
    iDestruct(isList_app with "HRT HLl2") as "Hchain".
    iDestruct(isList_Reach with "Hpre") as "#HR".
    iDestruct(reach_last with "Hchain HR HNl2") as "[Hl2 Hcases]".
    iDestruct "Hcases" as "[Heq | Hnext]".
    