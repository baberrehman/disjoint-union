(*
Library Cpdt.GeneralRec
*)

Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

Set Implicit Arguments.

Infix "::" := cons (at level 60, right associativity).

Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
    | nil => x :: nil
    | h :: ls' =>
      if le x h
        then x :: ls
        else h :: insert x ls'
    end.

Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
    | nil => ls2
    | h :: ls1' => insert h (merge ls1' ls2)
    end.

Fixpoint split (ls : list A) : list A * list A :=
    match ls with
    | nil => (nil,nil)
    | h :: nil => (h :: nil, nil)
    | h1 :: h2 :: ls' =>
      let (ls1, ls2) := split ls' in
        (h1 :: ls1 , h2 :: ls2)
    end.

(*Fixpoint mergeSort (ls : list A) : list A :=
    if (leb (length ls)) 1
      then ls
      else let lss := split ls in
      merge (mergeSort (fst lss)) (mergeSort (snd lss)).*)

Print well_founded.

Print Acc.