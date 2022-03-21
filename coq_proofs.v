(* Write your proof terms in place of underscores below ("_") *)

Variables A B C : Prop.

(* Exercise 1: Prove implication is transitive. What does this logical lemma correspond to in functional programming? *)
Check
  (fun ab bc =>
    fun a => bc (ab a)
  )
: (A -> B) -> (B -> C) -> (A -> C).

(* Exercise 2: Prove conjunction is associative *)
Check
  (fun abC =>
    conj (proj1 (proj1 abC)) (conj (proj2 (proj1 abC)) (proj2 abC))
  )
: (A /\ B) /\ C -> A /\ (B /\ C).

(* Exercise 3: Prove disjunction distributes over conjunction: *)
Check
  (fun AvBC =>
    match AvBC with
    | or_introl a  => conj (or_introl a) (or_introl a)
    | or_intror bc => conj (or_intror (proj1 bc)) (or_intror (proj2 bc))
    end
  )
: A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).

(* Exercise 4: Prove weak form of Peirce's law holds in intuitionistic logic *)
Check
  (fun abAab =>
    abAab (fun abA => abA (fun a => abAab (fun abA2 => a)))
  )
: ((((A -> B) -> A) -> A) -> B) -> B.

(* Exercise 5: We can always add double negation (but cannot drop it in general) *)
Check
  (fun a => fun na => na a)
: A -> ~ ~ A.

(* Exercise 6: Although we can in some special cases like the following: *)
Check
  (fun nnna => fun a => nnna (fun na => na a))
: ~ ~ ~ A -> ~ A.

(* Exercise 7: Prove we cannot add the negation of the law of excluded middle and have a sound logic.
   Keep in mind that "~ A" means "A -> False" *)
Check
  (fun nANA => nANA (or_intror (fun a => nANA (or_introl a))))
: ~ ~ (A \/ ~ A).
