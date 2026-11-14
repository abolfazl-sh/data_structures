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

Lemma reach_first(root hd: loc) xs ys:
  isList root hd (xs ++ ys) -∗ ∃ hd':loc, (⌜hd = hd'⌝ ∗ ⌜ys = []⌝ ∗ isList root hd xs) ∨
    (isList root hd' xs ∗ isList hd' hd ys).

Lemma isList_app (a b c : loc) ys zs :
    isList a b ys -∗ isList b c zs -∗ isList a c (ys ++ zs).
Admitted.

Lemma isList_snoc (a b c : loc) (x : val) (xs : list val) :
  isList a b xs -∗ b ↦□ x -∗ (b +ₗ 1) ↦□ InjRV #c -∗ isList a c (xs ++ [x]).
Admitted.


 Lemma queue_spec (v : val) (root head tail : loc) (γ : gname) (xs : list val):
{{{ isQueue root head tail γ xs }}}
 enq v (#head, #tail)
 {{{RET #(); isQueue root head tail γ (xs ++ [v])}}}.
 Proof.   
    iIntros "%φ HQ HQV".
    unfold enq.
    wp_pures.
    wp_apply node_spec.
    {done. }
    iIntros "%n Hn".
    wp_pures.
    iDestruct "Hn" as "[Hn1 Hn2]".        
    iDestruct "HQ" as "[#Hinv Hfrag]".
    iLöb as "IH" forall "Hfrag HQV Hn1 Hn2". 
    
    (*loading last*)
    wp_bind(! #tail)%E.
    iInv "Hinv" as (hd1 td1 l1 d1 lv1 gone1 ys1 zs1 xs1) 
    "(>Hhead1 & >Htail1 & >#HLt1 & >#HLl1 & >#Hgone1 & >#Hlast1 & >HNl1 & >%Hdx1 & >Hown1)" "Hclose1".
    wp_load.
    iDestruct (isList_app with "Hgone1 HLt1") as "#Hpre".

    iMod ("Hclose1" with "[Hhead1 Htail1 HNl1 Hown1]") as "_".
    {
     iNext. rewrite /queueInv.
     iExists hd1, td1, l1,  d1, lv1, gone1, ys1, zs1, xs1.
     
     iFrame. 
     iFrame "#".
     iPureIntro. exact.
    }
    iModIntro.

    (*loading the next of the last*)
    wp_let.
    wp_pures.
    wp_bind(! #(td1 +ₗ 1))%E.
        iInv "Hinv" as (hd2 td2 l2 d2 lv2 gone2 ys2 zs2 xs2) 
    "(>Hhead2 & >Htail2 & >#HLt2 & >#HLl2 & >#Hgone2 & >#Hlast2 & >HNl2 & >%Hdx2 & >Hown2)" "Hclose2".
    iDestruct(isList_app with "Hgone2 HLt2") as "HRT".
    iDestruct(isList_app with "HRT HLl2") as "Hchain".
    iDestruct(isList_Reach with "Hpre") as "#HR".
    iDestruct(reach_last with "Hchain HR HNl2") as "[Hl2 Hcases]".
    iDestruct "Hcases" as "[%Heq | Hnext]".
    + rewrite Heq.
      wp_load.
      iMod ("Hclose2" with "[Hhead2 Htail2 Hl2 Hown2]") as "_".
        {
        iNext. rewrite /queueInv.
        iExists hd2, td2, l2,  d2, lv2, gone2, ys2, zs2, xs2.
        rewrite <- Heq.
        iFrame. iFrame "#".
        iPureIntro. exact. 
        }
      iModIntro.
      wp_let.

    (*last is equal to tail condition(first condition)*)
    wp_bind(! #tail)%E.
    iInv "Hinv" as (hd3 td3 l3 d3 lv3 gone3 ys3 zs3 xs3)
        "(>Hhead3 & >Htail3 & >#HLt3 & >#HLl3 & >#Hgone3 & >#Hlast3 & >HNl3 & >%Hdx3 & >Hown3)" "Hclose3".
    
    wp_load.
    iMod ("Hclose3" with "[Hhead3 Htail3 HNl3 Hown3]") as "_".
      {
      iNext. rewrite /queueInv.
      iExists hd3, td3, l3,  d3, lv3, gone3, ys3, zs3, xs3.
      rewrite <- Heq.
      iFrame. iFrame "#".
      iPureIntro. exact. 
      }
    iModIntro.
    wp_op.
    case_bool_decide as HT13eq.
      (*if "last" = !"tail"*)
      - rewrite HT13eq.
        wp_pures.
        (*first CAS (the case will be sucessful)*)
        wp_bind(CmpXchg #(td3 +ₗ 1) (InjLV #()) (InjRV #n))%E.
        iInv "Hinv" as (hd4 td4 l4 d4 lv4 gone4 ys4 zs4 xs4)
        "(>Hhead4 & >Htail4 & >#HLt4 & >#HLl4 & >#Hgone4 & >#Hlast4 & >HNl4 & >%Hdx4 & >Hown4)" "Hclose4".
        iDestruct (isList_app with "Hgone4 HLt4") as "Hrt4".
        iDestruct (isList_app with "Hrt4 HLl4") as "Hchain4".
        iDestruct(reach_last with "Hchain4 HR HNl4") as "[HNl4 Hcases]".
        iDestruct "Hcases" as "[%Heq4 | Hnext4]".
        (*first cmpechg is successful*)
        ++ injection HT13eq as HT13eq.  rewrite <- HT13eq. rewrite Heq4.
        wp_cmpxchg_suc.

        (*update invariant*)
        iDestruct (own_valid_2 with "Hown4 Hfrag") as %Hag.
        apply excl_auth_agree_L in Hag. subst xs4.
        iCombine "Hown4 Hfrag" as "Hγ".
        iMod (own_update γ _
                ((●E (xs ++ [v] : leibnizO (list val))) ⋅ (◯E (xs ++ [v] : leibnizO (list val))))
                with "Hγ") as "Hγ".
        { apply excl_auth_update. }
        rewrite own_op.
        iDestruct "Hγ" as "[Hown4 Hfrag]".

        iMod (pointsto_persist with "Hn1") as "#Hn1".
        iMod (pointsto_persist with "HNl4") as "#HNl4".  

        iMod ("Hclose4" with "[Hhead4 Htail4 Hn2 Hown4]") as "_".
        { iNext. rewrite /queueInv.
          iExists hd4, td4, n, d4, v, gone4, ys4, (zs4 ++ [lv4]), (xs ++ [v]).
          iFrame.
          iFrame "#".        
        iSplit.
        - iApply (isList_snoc with "HLl4 Hlast4 HNl4").
        - iPureIntro.
          replace (d4 :: xs ++ [v]) with ((d4 :: xs) ++ [v]) by reflexivity.
          rewrite Hdx4.
          by rewrite -!app_assoc. }
    iModIntro.
    wp_pures.

    (*second CAS (the sucess case)*)
    wp_bind(CmpXchg #tail #l4 #n).
    iInv "Hinv" as (hd5 td5 l5 d5 lv5 gone5 ys5 zs5 xs5)
    "(>Hhead5 & >Htail5 & >#HLt5 & >#HLl5 & >#Hgone5 & >#Hlast5 & >HNl5 & >%Hdx5 & >Hown5)" "Hclose5".
    wp_cmpxchg as Hne | Heq'.
      -- injection Hne as Hne. subst td5.
       destruct zs5 as [|z zs'].
    +++ iDestruct "HLl5" as %Heq5. subst l5.
      iDestruct (pointsto_agree with "HNl5 HNl4") as %Hag.
      simplify_eq.
    +++ simpl. iDestruct "HLl5" as (m) "(Hz & Hzn & Hrest)".
      iDestruct (pointsto_agree with "Hzn HNl4") as %Hag.
      simplify_eq.                      (* m = n *)
      iMod ("Hclose5" with "[Hhead5 Htail5 HNl5 Hown5]") as "_".
      { iNext. rewrite /queueInv.
        iExists hd5, n, l5, d5, lv5, gone5, (ys5 ++ [z]), zs', xs5.
        iFrame. iFrame "#".
        iSplit.
        - iApply (isList_spec with "HLt5 Hz Hzn").
        - iPureIntro. rewrite Hdx5. by rewrite -!app_assoc. }
      
    iModIntro.
    wp_pures.
    iApply "HQV".
    unfold isQueue. iFrame. iFrame "#". done.


    -- (*second CAS is failed*)
      iMod ("Hclose5" with "[Hhead5 Htail5 HNl5 Hown5]") as "_".
      { iNext. rewrite /queueInv.
        iExists hd5, td5, l5, d5, lv5, gone5, ys5, zs5, xs5.
        iFrame. iFrame "#".
        iPureIntro. exact.
      }
      iModIntro.
      wp_pures.
      iApply "HQV".
      unfold isQueue.
      iFrame. exact.

      (*first cmpxchg is not sucessful*)
      ++injection HT13eq as HT13eq. 
        rewrite <- HT13eq. 
        iDestruct "Hnext4" as (n0) "#Hn0".
        wp_cmpxchg_fail.
        iMod ("Hclose4" with "[Hhead4 Htail4 HNl4 Hown4]") as "_".
        { iNext. rewrite /queueInv.
          iExists hd4, td4, l4, d4, lv4, gone4, ys4, zs4, xs4.
          iFrame. iFrame "#".
          iPureIntro. exact.
        }
        iModIntro.
        wp_pures.
        iApply ("IH" with "Hfrag HQV Hn1 Hn2").
    - wp_pures.
      iApply ("IH" with "Hfrag HQV Hn1 Hn2").
      (*the next of last is not null, it means that another cell is added to linked list before finilization of current one*)
    + iDestruct "Hnext" as (n0) "#Hn0".
      wp_load.
      iMod ("Hclose2" with "[Hhead2 Htail2 Hl2 Hown2]") as "_".
        { iNext. rewrite /queueInv.
          iExists hd2, td2, l2, d2, lv2, gone2, ys2, zs2, xs2.
          iFrame. iFrame "#".
          iPureIntro. exact.
        }
        iModIntro.

     wp_let.
     wp_bind(! #tail)%E.
     iInv "Hinv" as (hd3 td3 l3 d3 lv3 gone3 ys3 zs3 xs3)
    "(>Hhead3 & >Htail3 & >#HLt3 & >#HLl3 & >#Hgone3 & >#Hlast3 & >HNl3 & >%Hdx3 & >Hown3)" "Hclose3".
    wp_load.
    iMod ("Hclose3" with "[Hhead3 Htail3 HNl3 Hown3]") as "_".
        { iNext. rewrite /queueInv.
          iExists hd3, td3, l3, d3, lv3, gone3, ys3, zs3, xs3.
          iFrame. iFrame "#".
          iPureIntro. exact.
        }
    iModIntro.
    wp_pures.
    case_bool_decide as Heq13.
    wp_pures.
      ++ wp_bind(CmpXchg #tail #td1 #n0).
        iInv "Hinv" as (hd4 td4 l4 d4 lv4 gone4 ys4 zs4 xs4)
        "(>Hhead4 & >Htail4 & >#HLt4 & >#HLl4 & >#Hgone4 & >#Hlast4 & >HNl4 & >%Hdx4 & >Hown4)" "Hclose4".
        wp_cmpxchg as Htd41eq | Htd41neq.
          --injection Htd41eq as Htd41eq. subst td4.   (* now td4 is td1 *)
            destruct zs4 as [|z zs'].
            - (* zs4 = []: l4 = td1, so (td1+1) ↦ NONE, contradicting Hn0 *)
              iDestruct "HLl4" as %->.
              iDestruct (pointsto_agree with "HNl4 Hn0") as %Hag.
              simplify_eq.
            - (* zs4 = z :: zs' *)
              simpl. iDestruct "HLl4" as (m) "(Hz & Hzn & Hrest)".
              iDestruct (pointsto_agree with "Hzn Hn0") as %Hag.
              simplify_eq.                                (* m = n0 *)
              iMod ("Hclose4" with "[Hhead4 Htail4 HNl4 Hown4]") as "_".
              { iNext. rewrite /queueInv.
                iExists hd4, m, l4, d4, lv4, gone4, (ys4 ++ [z]), zs', xs4.
                iFrame. iFrame "#". iSplit.
                - iApply (isList_spec with "HLt4 Hz Hzn").
                - iPureIntro. rewrite Hdx4. by rewrite -!app_assoc. }
              iModIntro. wp_pures.
              iApply ("IH" with "Hfrag HQV Hn1 Hn2").
          --iMod ("Hclose4" with "[Hhead4 Htail4 HNl4 Hown4]") as "_".
              { iNext. rewrite /queueInv.
                iExists hd4, td4, l4, d4, lv4, gone4, ys4, zs4, xs4.
                iFrame. iFrame "#".
                iPureIntro. exact. }
            iModIntro.
            wp_pures.
            iApply ("IH" with "Hfrag HQV Hn1 Hn2").
      ++ wp_pures.
        iApply ("IH" with "Hfrag HQV Hn1 Hn2").
 Qed.

Lemma deq_spec (v : val) (root head tail : loc) (γ : gname) (xs : list val):
{{{∃ v, isQueue root head tail γ (xs ++ [v]) }}}
 deq (#head, #tail)
{{{RET #(); isQueue root head tail γ xs}}}.
Proof.
  iIntros "%φ HQ HQV".
  unfold deq.
  iDestruct "HQ" as "[%v0 HQ]".
  iDestruct "HQ" as "[#Hinv Hγ]".
  wp_pures.
  iLöb as "IH" forall "Hγ HQV".
  wp_bind(! #head)%E.
  iInv "Hinv" as (hd1 td1 l1 d1 lv1 gone1 ys1 zs1 xs1) 
  "(>Hhead1 & >Htail1 & >#HLt1 & >#HLl1 & >#Hgone1 & >#Hlast1 & >HNl1 & >%Hdx1 & >Hown1)" "Hclose1".
  wp_load.
  iMod("Hclose1" with "[Hhead1 Htail1 HNl1 Hown1]") as "_" .
  {
    iNext. rewrite /queueInv.
    iExists hd1, td1, l1, d1, lv1, gone1, ys1, zs1, xs1.
    iFrame. iFrame "#".
    iPureIntro. exact.
  }
  iModIntro.
  wp_let.
  wp_bind(! #tail)%E.
  iInv "Hinv" as (hd2 td2 l2 d2 lv2 gone2 ys2 zs2 xs2)
  "(>Hhead2 & >Htail2 & >#HLt2 & >#HLl2 & >#Hgone2 & >#Hlast2 & >HNl2 & >%Hdx2 & >Hown2)" "Hclose2".
  iDestruct(isList_app with "Hgone2 HLt2") as "#Hpre".
  wp_load.
  iMod("Hclose2" with "[Hhead2 Htail2 HNl2 Hown2]") as "_".
  {
    iNext; rewrite/queueInv.
    iExists hd2, td2, l2, d2, lv2, gone2, ys2, zs2, xs2.
    iFrame. iFrame "#".
    iPureIntro. exact.
  }
  iModIntro.
  wp_let.
  wp_pures.
  wp_bind(! #(hd1 +ₗ 1))%E.

