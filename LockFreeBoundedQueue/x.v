Lemma a (P Q : Prop) : P /\ Q-> Q .
Proof.
    intros [H1 H2] .
    apply H2.
Qed.