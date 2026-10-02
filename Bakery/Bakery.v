From iris.algebra Require Export auth excl frac numbers agree gmap.
From iris.base_logic.lib Require Export invariants.
From iris.heap_lang Require Import lang proofmode notation par.
From iris.algebra.lib Require Import excl_auth.
From iris.heap_lang.lib Require Import spawn. 

Definition Bakery : val := 
    λ: "n",
    let: "flag" := AllocN "n" #false in 
    let: "number" := AllocN "n" #0 in 
    ("flag", "number").

Definition set_flag : val :=
    λ: "b" "i" "v", (Fst "b" +ₗ "i" ) <- "v".

Definition set_number : val :=
    λ: "b" "i" "v", (Snd "b" +ₗ "i") <- "v".

Definition array_max : val :=
    λ: "arr" "n" ,
        let: "loop" :=
            rec: "go" "i" "max" :=
                if: "i" = "n" then "max"
                else 
                let: "v" := !(Snd "arr" +ₗ "i") in 
                "go" ("i" + #1) (if: "v" < "max" then "max" else "v")
            in
        "loop" #0 #0.

Definition lock : val  :=
    λ: "arr" "n" "id",
    set_flag "arr" "id" #true;;
    let: "max" := array_max "arr" "n" in
    set_number "arr" "id" ("max" + #1);;
    set_flag "arr" "id" #false;;

    let: "loop" :=
        rec: "go" "i" :=
            if: "i" = "n" then #()
            else if: "i" = "id" then "go" ("id" + #1) 
            else if: !(Fst "arr" +ₗ "i") ||
            (!(Snd "arr" +ₗ "i") < !(Snd "arr" +ₗ "id")) || 
            (!(Snd "arr" +ₗ "i") = !(Snd "arr" +ₗ "id") && ("i" < "id"))
        then "go" "i"
        else "go" ("i" + #1)
    in 
    "loop" #0.

Definition unlock : val :=
    λ: "arr" "id",
    set_number "arr" "id" #0.

Inductive phase :=
    | idle
    | doorway
    | queued (v : nat).

Instance Phase_eq_dec : EqDecision phase.
Proof. solve_decision. Defined.

Instance Phase_countable : Countable phase.
Proof.
  refine (inj_countable'
    (fun p => match p with 
        | idle => inl () 
        | doorway => inr (inl ())
        | queued v => inr (inr v) end)
    (fun x => match x with
        | inl () => idle 
        | inr (inl ()) => doorway
        | inr (inr v) => queued v end) _);
  by intros [].
Defined.



Definition bakeryΣ : gFunctors :=
#[  GFunctor (excl_authR (leibnizO phase));
    GFunctor (exclR unitO);
    GFunctor (authR (gmapUR nat (agreeR (leibnizO (nat * nat)))));
    spawnΣ
].

Class bakeryG Σ := BakeryG {
    bakery_phaseG :: inG Σ (excl_authR (leibnizO phase)); 
    bakery_tokG :: inG Σ (exclR unitO);
    bakery_snapG :: inG Σ (authR (gmapUR nat (agreeR (leibnizO (nat * nat)))));
}.

#[export] Instance subG_bakeryΣ {Σ} : subG bakeryΣ Σ → bakeryG Σ.
Proof. solve_inG. Qed.

Section proof.
Context `{!heapGS Σ, !bakeryG Σ, !spawnG Σ}.
Context (N : namespace).

Definition phys_match (p : phase) (b : bool) (v : nat) : Prop :=
  match p with
  | idle      => b = false ∧ v = 0
  | doorway   => b = true  ∧ v = 0
  | queued v' => b = false ∧ v = v'
  end.

Definition thread_inv (γ : gname) (flag_l number_l : loc) : iProp Σ :=
  ∃ (p : phase) (b : bool) (v : nat),
    flag_l   ↦ #b ∗
    number_l ↦ #v ∗
    own γ (●E (p : leibnizO phase)) ∗
    ⌜phys_match p b v⌝.

Definition Inv_i (γ : gname) (flag_l number_l : loc) : iProp Σ :=
  inv N (thread_inv γ flag_l number_l).

Definition phase_frag (γ : gname) (p : phase) : iProp Σ :=
  own γ (◯E (p : leibnizO phase)).

Definition ord (occ comp : nat * nat) : Prop :=
  let '(v_occ, id_occ) := occ in
  let '(v_c,   id_c)   := comp in
  (v_occ < v_c) ∨ (v_occ = v_c ∧ id_occ < id_c).



Definition to_agree_map (m : gmap nat (nat * nat)) : gmapUR nat (agreeR (leibnizO (nat * nat))) :=
  (fun p => to_agree (p : leibnizO (nat * nat))) <$> m.

Definition occ_inv (γ_tok γ_map : gname) (R : iProp Σ) : iProp Σ :=
  (own γ_tok (Excl () : exclR unitO)
   ∗ own γ_map (● (∅ : gmapUR nat (agreeR (leibnizO (nat * nat)))))
   ∗ R)
 ∨
  (∃ (id v : nat) (m : gmap nat (nat * nat)),
      own γ_map (● to_agree_map m) ∗
      ⌜m !! id = Some (v, id)⌝ ∗
      ⌜∀ j vj idj, j ≠ id → m !! j = Some (vj, idj) → ord (v, id) (vj, idj)⌝).

Definition Inv_occ (γ_tok γ_map : gname) (R : iProp Σ) : iProp Σ :=
  inv N (occ_inv γ_tok γ_map R).


Definition in_cs (γ_tok : gname) : iProp Σ :=
  own γ_tok (Excl () : exclR unitO).

Lemma mutual_exclusion (γ_tok : gname) :
  in_cs γ_tok -∗ in_cs γ_tok -∗ False.
Proof.
  iIntros "Htok1 Htok2".
  iDestruct (own_valid_2 with "Htok1 Htok2") as %[].
Qed.

Theorem wp_lock (arr : val) (flag_l number_l : loc) (n id : nat)
    (γ γ_tok γ_map : gname) (E : coPset) :
  ↑N ⊆ E →
  arr = (#flag_l, #number_l)%V →
  (id < n)%nat →
  {{{ Inv_i γ flag_l number_l ∗
      Inv_occ γ_tok γ_map True%I ∗
      phase_frag γ idle }}}
    lock arr #n #id @ E
  {{{ RET #(); in_cs γ_tok }}}.
Proof.
Admitted.

Theorem lock_excludes_concurrent (arr : val) (flag_l number_l : loc)
    (n id1 id2 : nat) (γ1 γ2 γ_tok γ_map : gname) :
  arr = (#flag_l, #number_l)%V →
  id1 ≠ id2 → id1 < n → id2 < n →
  {{{ Inv_i γ1 flag_l number_l ∗ Inv_i γ2 flag_l number_l ∗
      Inv_occ γ_tok γ_map True%I ∗
      phase_frag γ1 idle ∗ phase_frag γ2 idle }}}
    lock arr #n #id1 ||| lock arr #n #id2
  {{{ RET (#(), #()); False }}}.

Proof.
  iIntros (Harr Hne Hid1 Hid2 Φ) "(#Hi1 & #Hi2 & #Hocc & Hf1 & Hf2) HΦ".
  wp_pures.
  wp_apply (wp_par (fun v => in_cs γ_tok) (fun v => in_cs γ_tok)
              with "[Hf1] [Hf2]").
  - wp_apply (wp_lock with "[$Hi1 $Hocc $Hf1]"); auto.
  - wp_apply (wp_lock with "[$Hi2 $Hocc $Hf2]"); auto.
  - iIntros (v1 v2) "[Htok1 Htok2]".
    iDestruct (mutual_exclusion with "Htok1 Htok2") as %[].
Qed.  

End proof.
