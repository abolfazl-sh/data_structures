From iris.heap_lang Require Import lang proofmode notation.


Section UnboundadedQueue.
Context `{!heapGS Σ}.

Fixpoint isList (lhd : val) (ltail : val) (xs : list val) : iProp Σ :=
  match xs with
  | [] => ⌜lhd = NONEV⌝ ∗ ⌜ltail = NONEV⌝
  | x :: xs => ∃ (hdv hdl : loc) l' l'', ⌜lhd = SOMEV (#hdv)⌝ ∗ ⌜ltail = SOMEV (#hdl)⌝ ∗ hdv ↦ x ∗ hdl ↦ (l', l'') ∗ isList l' l'' xs 
  end.

  Definition Node : val :=
    λ: "v" "next",
    (SOME (ref "v"), SOME(ref "next")).

  Definition GetNodeValue : val :=
  λ: "n", 
  match: Fst "n" with 
  NONE => NONE
  | SOME("n'") => "n'"
  end.

  Definition GetNodeNext : val :=
  λ: "n",
  match: Snd "n" with 
  NONE => NONE
  | SOME("n'") => "n'"
  end.

Definition UnBoundadeQueue : val :=
    λ: <>,
    let: "node" := Node NONE NONEV in
    let: "head" := ref "node" in 
    let: "tail" := ref "node" in 
    ("head", "tail").

Definition enq : val :=
    λ: "node" "Queue",
        let: "loop" :=
            rec: "insert" "node" "Queue" :=
            let: "last" :=   ! (Snd "Queue") in  (*last =  (Some (ref "v") , Some(ref "next"))*)
            let: "next" :=  GetNodeNext ("last") in (*next = ref "next" (next = Some(ref "v'"), Some(ref "next'")) *) 
            if: ("last" =  ! (Snd "Queue")) then (*(Some (ref "v"), Some(ref "next")) = (Some (ref "v"), Some(ref "next"))*)
                if: ((GetNodeValue (Fst(!"next"))) = NONE) then (*"v'" == NONE*)
                    if: CAS (GetNodeNext (Snd("last"))) "next" "node" then (*CAS (ref "next")  *)
                        CAS (Snd "Queue") "last" "node"
                    else "insert" "node" "Queue"
                else CAS (Snd "Queue") "last" "next";;
                    "insert" "node" "Queue"
            else "insert" "node"  "Queue" in 
    "loop" "node" "Queue".

Lemma enqspc (hd : val) (tail : val) (xs : list Z) (node : val):
    {{{isList hd tail ((λ x : Z, #x) <$> xs) }}}
        enq node xs
    {{{ RET _; isList hd tail ((λ x : Z, #x) <$> xs)}}}.
Proof.
    revert l.
    iLöb as "IH".
    induction xs.
    - iIntros "%l %φ %H HL".
    wp_rec.


