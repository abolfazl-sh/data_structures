From iris.heap_lang Require Import lang proofmode notation.

From iris.base_logic.lib Require Export invariants.

From iris.algebra Require Import excl_auth.

From iris.base_logic.lib Require Import own.

From iris.bi.lib Require Import fixpoint_mono.

Section UnboundedQueue.

Context `{!heapGS Σ, !inG Σ (excl_authR (leibnizO (list val)))}.

Let M := nroot .@ "queue".

(*
English explanation — node
--------------------------
This function allocates one Michael–Scott queue node as two consecutive heap cells.
- Cell 0 stores the user value.
- Cell 1 stores the link to the next node.
The link is initialized to NONE, so a freshly allocated node is initially the last
node of a linked list.

Operational result: node v returns a location n such that n contains v and n+1
contains NONE.
*)
Definition node : val :=

  λ: "value",

    let: "cell" := AllocN #2 "value" in

    "cell" +ₗ #1 <- NONE;;

    "cell".

(*
English explanation — queue
---------------------------
This creates an empty Michael–Scott queue.
A dummy/sentinel node n is allocated first. Both head and tail initially point to
that same node. Therefore the queue contains no user element yet, but it has the
sentinel node required by the algorithm.

Returned value: a pair (head, tail), where head and tail are references containing
locations of queue nodes.
*)
Definition queue : val :=

  λ: <>,

    let: "n" := node #0 in

    let: "head" := ref "n" in

    let: "tail" := ref "n" in

    ("head", "tail").

(*
English explanation — isList
----------------------------
isList from to ys is the logical description of a linked-list segment.
- If ys = [], then the segment contains no nodes, so from = to.
- If ys = y :: ys', then `from` stores y, the next-field at from+1 points to some
  node n, and the rest of the segment from n to `to` represents ys'.

The points-to assertions are persistent/read-only (↦□). This lets the proof keep
knowledge about already-linked nodes even after closing the queue invariant.
*)
Fixpoint isList (from to : loc) (ys : list val) : iProp Σ :=

  match ys with

  | [] => ⌜from = to⌝

  | y :: ys => ∃ n : loc, from ↦□ y ∗ (from +ₗ 1) ↦□ SOMEV #n ∗ isList n to ys

  end.

(*
English explanation — isList_timeless
--------------------------------------
This instance proves that isList is Timeless. In Iris this means the assertion can
be used across the later modality in the standard way needed when opening/closing
invariants. The proof is structural induction on the represented list.
*)
Global Instance isList_timeless from to ys : Timeless (isList from to ys).

Proof.

  revert from.

  induction ys as [|y ys IH]; intros from; simpl; apply _.

Qed.

(*
English explanation — isList_persistent
----------------------------------------
This instance proves that isList is Persistent. Intuitively, the list description
contains only persistent points-to facts and pure equalities, so it may safely be
copied/reused by the proof.
*)
Global Instance isList_persistent from to ys : Persistent (isList from to ys).

Proof.

  revert from.

  induction ys as [|y ys IH]; intros from; simpl; apply _.

Qed.

(*
English explanation — queueInv
------------------------------
This is the central invariant describing the concrete heap representation of the
Michael–Scott queue and its abstract logical contents.

Important pieces:
- `head ↦ #hd` and `tail ↦ #td` are the current concrete head/tail pointers.
- `isList hd td ys` describes the segment from head to tail.
- `isList td l zs` describes nodes after the current tail pointer. This is needed
  because in Michael–Scott queue another thread may already have linked a node but
  not yet advanced the tail pointer.
- `isList root hd gone` remembers the prefix already passed by head.
- `l ↦□ lv` and `(l +ₗ 1) ↦ NONEV` say l is the physical last node: it stores lv
  and its next field is currently null.
- `d :: xs = ys ++ zs ++ [lv]` connects the concrete linked structure with the
  abstract queue contents. `d` is the dummy/front value not returned to clients.
- `own γ (●E xs)` is the authoritative ghost state for the abstract queue contents.

The invariant therefore allows head and tail to lag in ways permitted by the
lock-free algorithm while still tying every concrete state to one abstract list.
*)
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

(*
English explanation — isQueue
-----------------------------
This is the client-facing queue predicate.
It combines:
1. the shared invariant `queueInv`, and
2. a fragment of the ghost state saying that the client-visible abstract contents
   are `xs`.

Agreement between the fragment and the authoritative ghost state inside the
invariant is what lets enqueue/dequeue proofs connect concrete CAS operations to
changes of the abstract list.
*)
Definition isQueue (root head tail : loc) (γ : gname) (xs : list val) : iProp Σ :=

  inv M (queueInv root head tail γ) ∗ own γ (◯E (xs : leibnizO (list val))).

(*
English explanation — enq
-------------------------
This is the Michael–Scott enqueue operation.
Program-line structure:
1. Allocate a new node n containing the value, with next = NONE.
2. Read the shared tail pointer into `last`.
3. Read `last.next` into `next`.
4. Re-read tail and continue only if the previously read `last` is still current.
5. If `next = NONE`, try to CAS last.next from NONE to SOME n. This is the
   linearization point of a successful enqueue: the new node becomes reachable.
6. After linking n, try to move tail from last to n. This CAS is only helping/
   cleanup; enqueue is already logically complete even if this second CAS fails.
7. If `next = SOME l`, another thread has already linked a node but tail is lagging.
   Help move tail to l and retry.
8. If tail changed during validation, retry.
*)
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

(*
English explanation — deq
-------------------------
This is the Michael–Scott dequeue operation.
Program-line structure:
1. Read head into `first`, tail into `last`, and first.next into `next`.
2. Re-read head and continue only if `first` is still current.
3. If first = last, head and tail point to the same node:
   - next = NONE means the queue is empty;
   - next = SOME n means tail is lagging, so help advance tail and retry.
4. If first <> last, there should be a successor node. Read its value v.
5. CAS head from first to n. A successful CAS removes the old dummy/front node and
   is the dequeue linearization point; the successor becomes the new dummy/head.
6. If the CAS fails, another thread changed head, so retry.
*)
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

(*
English explanation — node_spec
-------------------------------
Specification of `node`.
Precondition: no heap resource is required (`True`).
Postcondition: it returns a fresh location n with ownership of two cells:
  n      ↦ v
  n + 1  ↦ NONE
The proof allocates two cells, splits the array ownership, stores NONE in the next
field, and returns both points-to resources.
*)
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

(*
English explanation — isList_spec
---------------------------------
This lemma extends an existing list segment by one already-linked node.
Prerequisites:
- isList hd td ys
- td stores v'
- td.next points to n
Result:
- isList hd n (ys ++ [v'])
The induction walks to the end of the old segment and appends the final node.
*)
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

(*
English explanation — reach_pre
-------------------------------
This is the one-step functional used to define reachability as a least fixed point.
A pair (x,z) is reachable if either x = z, or x.next points to some y and y can
reach z according to Φ.
*)
Definition reach_pre (Φ : prodO locO locO → iProp Σ) :

    prodO locO locO → iProp Σ :=

  λ '(x, z), (⌜x = z⌝ ∨ ∃ y : loc, (x +ₗ 1) ↦□ SOMEV #y ∗ Φ (y, z))%I.

(*
English explanation — Reach
---------------------------
Reach x z is the transitive/reflexive linked-list reachability relation generated
by reach_pre. It says that by repeatedly following next pointers from x, one can
arrive at z.
*)
Definition Reach (x z : loc) : iProp Σ :=

  bi_least_fixpoint reach_pre (x, z).

(*
English explanation — isList_Reach
----------------------------------
This lemma converts the stronger structural list predicate `isList hd td ys` into
the weaker fact `Reach hd td`. The element values are forgotten; only existence of
a next-pointer path is retained.
*)
Lemma isList_Reach(hd td : loc) ys :

  isList hd td ys -∗ Reach hd td.

Admitted.

(*
English explanation — reach_last
--------------------------------
Given a concrete list ending at l, reachability from root to td, and the fact that
l.next = NONE, this lemma classifies td:
- either td is exactly the physical last node l, or
- td has a non-null next pointer.
This is useful when deciding whether a previously read tail is at the true end or
is lagging behind an already-linked node.
*)
Lemma reach_last(root td l: loc) ys :

    isList root l ys -∗ Reach root td -∗ (l +ₗ 1) ↦ NONEV -∗

    (l +ₗ 1) ↦ NONEV ∗ ((⌜td = l⌝) ∨ (∃ n, (td +ₗ 1) ↦□ SOMEV #n)).

Admitted.

(*
English explanation — reach_first
---------------------------------
This lemma decomposes a list described as xs ++ ys around the point after prefix
xs. It produces an intermediate location hd'. Either the suffix ys is empty and
hd' coincides with hd, or the original segment splits into root--hd' representing
xs and hd'--hd representing ys.
*)
Lemma reach_first(root hd: loc) xs ys:

  isList root hd (xs ++ ys) -∗ 

    ∃ hd':loc, (⌜hd = hd'⌝ ∗ ⌜ys = []⌝ ∗ isList root hd xs) ∨
    (isList root hd' xs ∗ isList hd' hd ys).

(*
English explanation — isList_app
--------------------------------
This is concatenation for logical list segments. If a--b represents ys and b--c
represents zs, then a--c represents ys ++ zs.
*)
Lemma isList_app (a b c : loc) ys zs :

    isList a b ys -∗ isList b c zs -∗ isList a c (ys ++ zs).

Admitted.

(*
English explanation — isList_snoc
---------------------------------
This is another append-one-element lemma. If a--b represents xs, b stores x, and
b.next points to c, then a--c represents xs ++ [x]. It is used after enqueue has
successfully changed the old last node's next field to point at the new node.
*)
Lemma isList_snoc (a b c : loc) (x : val) (xs : list val) :

  isList a b xs -∗ b ↦□ x -∗ (b +ₗ 1) ↦□ InjRV #c -∗ isList a c (xs ++ [x]).

Admitted.

(*
Proof guide — queue_spec / enqueue
==================================
Specification goal:
  Starting from isQueue ... xs, `enq v` returns unit and establishes
  isQueue ... (xs ++ [v]).

The comments below are grouped by actual program actions. For each action:
- PRE: facts/resources that must be available before proving that line.
- ACTION: the concrete HeapLang operation being verified.
- POST: what the proof knows/needs after that line.
*)
Lemma queue_spec (v : val) (root head tail : loc) (γ : gname) (xs : list val):

{{{ isQueue root head tail γ xs }}}

 enq v (#head, #tail)

 {{{RET #(); isQueue root head tail γ (xs ++ [v])}}}.

Proof.

    iIntros "%φ HQ HQV".

    unfold enq.

    wp_pures.

(*
PROGRAM LINE: let: "n" := node "value" in
PRE:
- The enqueue proof has the queue predicate HQ.
- `node_spec` requires only True.
ACTION:
- Allocate the new node n.
POST:
- Hn gives n ↦ v and (n+1) ↦ NONE.
- These resources are kept private until the successful linking CAS.
*)
    wp_apply node_spec.

    {done. }

    iIntros "%n Hn".

    wp_pures.

    iDestruct "Hn" as "[Hn1 Hn2]".

    iDestruct "HQ" as "[#Hinv Hfrag]".

(*
PROGRAM STRUCTURE: recursive `insert` loop
PRE:
- Persistent queue invariant Hinv.
- Ghost fragment Hfrag describing abstract xs.
- New node resources Hn1/Hn2.
ACTION:
- Establish a Löb induction hypothesis for retries of `insert`.
POST:
- Any interference branch can restart while preserving exactly the resources
  needed for another iteration.
*)
    iLöb as "IH" forall "Hfrag HQV Hn1 Hn2".

(*
PROGRAM LINE: let: "last" := !"tail" in
PRE:
- Must open Hinv to obtain ownership of tail ↦ #td1 before loading it.
- The invariant also exposes the current concrete list decomposition.
ACTION:
- Read tail, so program variable `last` becomes td1.
POST:
- Record Hpre = isList root td1 (gone1 ++ ys1). This persistent prefix is later
  used to prove that the old tail value td1 remains reachable even if the queue
  changes before the next atomic step.
- Close the invariant unchanged.
*)
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

(*
PROGRAM LINE: let: "next" := !("last" +ₗ #1) in
PRE:
- `last` is the previously read td1.
- Need to justify what may currently be stored in td1.next despite interference.
- Hpre proves root reaches td1; the newly opened invariant gives the current full
  chain root--l2 and l2.next = NONE.
ACTION:
- `reach_last` classifies td1 as either the current physical last node l2 or a node
  with a persistent SOME successor.
POST:
- Case A: td1 = l2, so the load returns NONE.
- Case B: td1.next = SOME n0, so the load returns SOME n0.
These are exactly the two algorithmic branches for `next`.
*)
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

(*
PROGRAM LINE: if: "last" = !"tail" then ... else retry
PRE:
- `last` is still the snapshot td1.
ACTION:
- Re-read the shared tail and compare it with the snapshot.
POST:
- Equal branch: the snapshot passed the Michael–Scott validation check, so the
  proof may reason about the following CAS using that equality.
- Unequal branch: another thread moved tail; no queue update is performed by this
  iteration, so invoke IH and retry with the same ghost fragment/new node.
*)
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

(*
PROGRAM LINE: CAS ("last" +ₗ #1) "next" (SOME "n")
This is the important enqueue CAS.
PRE:
- We are in the validated branch `last = current tail`.
- In the success subcase, `reach_last` proves this `last` is also the physical last
  l4 and therefore l4.next currently contains NONE.
- Hn1/Hn2 describe the new node n, whose next is still NONE.
ACTION:
- CAS old-last.next from NONE to SOME n.
POST ON SUCCESS:
- n is now reachable from the queue. This is the enqueue linearization point.
- The abstract ghost list must change from xs to xs ++ [v].
- The old last.next fact is made persistent, and the invariant is rebuilt with n
  as the new physical last node and v as its stored last value.
POST ON FAILURE:
- A persistent SOME successor proves another thread linked first. The invariant is
  closed unchanged and the loop retries; our node n is still private and reusable.
*)
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

(*
ABSTRACT UPDATE AFTER THE SUCCESSFUL LINKING CAS
PRE:
- Hown4 is authoritative ghost state from the invariant.
- Hfrag is this operation's fragment.
- Validity forces both to agree on the old abstract list xs.
ACTION:
- Perform an excl_auth ghost update to xs ++ [v].
- Convert the now-stable node/value and old-next facts to persistent assertions.
POST:
- Both authoritative and fragment ghost states describe xs ++ [v].
- The concrete linked structure and equation d4 :: (xs ++ [v]) = ... are rebuilt
  consistently with the newly linked node.
*)
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

(*
PROGRAM LINE: CAS "tail" "last" "n";; #()
PRE:
- The new node has already been linked, so abstract enqueue is complete.
- Tail may still point to the old node, or another thread may already have moved it.
ACTION:
- Try to advance tail to n.
POST IF CAS SUCCEEDS:
- Repartition the invariant so the concrete tail pointer advances by one node.
- Abstract ghost contents stay xs ++ [v]; this CAS is NOT the linearization point.
POST IF CAS FAILS:
- Some interference already changed tail. Close the invariant unchanged and return
  success anyway, because the first CAS already inserted v.
*)
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

(*
PROGRAM BRANCH: match next with SOME "l"
PRE:
- The earlier load established td1.next = SOME n0.
INTERPRETATION:
- Another enqueue already linked a node after our observed tail, but tail may still
  be pointing to td1. This is the standard lagging-tail case.
ACTION:
- Revalidate tail. If it is still td1, CAS tail from td1 to n0 to help the other
  enqueue; otherwise do nothing.
POST:
- No abstract queue contents are changed by this helping CAS.
- Regardless of CAS success/failure, retry our own insertion with IH and the same
  private new node n.
*)
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

(*
Proof guide — deq_spec / dequeue
================================
The supplied specification assumes there exists a value v such that the current
abstract queue is xs ++ [v], and aims to finish with abstract xs.

NOTE: the uploaded proof is incomplete and stops while beginning the proof of the
program line `let: "next" := !("first" +ₗ #1) in`. The comments below explain only
the proof steps actually present; no missing proof code is added.

As with enqueue:
- PRE = what must be known before an actual program line.
- ACTION = what the program does.
- POST = what should be available after proving that line.
*)
Lemma deq_spec (v : val) (root head tail : loc) (γ : gname) (xs : list val):

{{{ isQueue root head tail γ ([v] ++ xs) }}}

 deq (#head, #tail)

{{{RET v; isQueue root head tail γ xs}}}.

Proof.

  iIntros "%φ HQ HQV".

  unfold deq.

  iDestruct "HQ" as "[%v0 HQ]".

  iDestruct "HQ" as "[#Hinv Hγ]".

  wp_pures.

(*
PROGRAM STRUCTURE: recursive `deq` retry loop
PRE:
- Hinv is persistent and can be reopened on every iteration.
- Hγ is the ghost fragment for the current abstract queue.
ACTION:
- Set up Löb induction so branches caused by interference can recursively retry.
POST:
- IH can restart dequeue while carrying the ghost fragment and final continuation.
*)
  iLöb as "IH" forall "Hγ HQV".

(*
PROGRAM LINE: let: "first" := !"head" in
PRE:
- Need head ↦ #hd1 from the invariant.
ACTION:
- Open the invariant and load head.
POST:
- Program variable `first` is hd1.
- The invariant is restored unchanged because a load does not modify the queue.
*)
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

(*
PROGRAM LINE: let: "last" := !"tail" in
PRE:
- Need tail ↦ #td2 from the invariant.
- The invariant also supplies the concrete prefix from root through head to tail.
ACTION:
- Load tail, so program variable `last` becomes td2.
POST:
- Build persistent Hpre = isList root td2 (gone2 ++ ys2). This records that the
  observed tail is reachable from the root and can later help reason under
  interference.
- Close the invariant unchanged.
*)
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

(*
PROGRAM LINE: let: "next" := !("first" +ₗ #1) in
PRE:
- `first` is the earlier snapshot hd1.
- Because other threads may have changed head since that read, the proof must open
  the invariant again and establish that hd1 is still a valid reachable node whose
  next field can be read consistently.
ACTION:
- Read the next pointer of the observed first node.
EXPECTED POST (from the program, although the supplied proof stops here):
- `next` is either NONE or SOME n.
- The later proof must then re-read head (`if first = !head`) to validate the
  snapshot before using first/next to decide empty, help tail, or CAS head.

The uploaded source ends immediately after the wp_bind below, so there is no proof
text available to annotate for the remaining deq program lines.
*)
  wp_bind(! #(hd1 +ₗ 1))%E.
