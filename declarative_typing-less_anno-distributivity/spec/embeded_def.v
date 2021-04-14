(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec A B := forall C, ordinary C -> sub C (t_and A B) -> False.
Notation "A *s B" := (DisjSpec A B) (at level 80).
