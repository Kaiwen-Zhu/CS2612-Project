Require Export Coq.Strings.String.
Require Export Coq.Bool.Bool.
Require Export Compare_dec.
Require Export Coq.Lists.List.
Require Export DPLL.ExplicitName.
Export ListNotations.


(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Definition of DPLL                                               *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

(* ***************************************************************** *)
(*                                                                   *)
(*  Definition of CNF propositions                                   *)
(*                                                                   *)
(* ***************************************************************** *)

(** PV is imported from ExplicitName. You do not need to read those
    details. It is about string and string comparisons. *)
Module PV := StringName.

(** ident:Type of variables. Here, _[PV.t]_ is just string. *)
Definition ident := PV.t.

(** clause: list of literals.
      - true: positive literal
      - false: negative literal *)
Definition clause := list (bool * ident).

Definition CNF := list clause.

(* ***************************************************************** *)
(*                                                                   *)
(*  Definition of Assignments                                        *)
(*                                                                   *)
(* ***************************************************************** *)

(** partial_asgn: list of variables and their values *)
Definition partial_asgn := list (ident * bool).

(** asgn: value of all variables, total function *)
Definition asgn:= ident-> bool.

(** PV.look_up: find the value of x in partial_asgn J *)
Print PV.look_up.

(* ***************************************************************** *)
(*                                                                   *)
(*  Unit Propagation                                                 *)
(*                                                                   *)
(* ***************************************************************** *)

(** We define _[unit_pro]_ to improve a partial assignment. The return
    value is _[None]_ is a conflict can be derived. *)

Inductive UP_result :=
| Conflict
| UP (x: ident) (b: bool)
| Nothing.

(** Construct UP_result from a clause c.
If all literals in c contradicts with J, return Conflict.
If there is only one literal (op, x) that is not assgined in J, return UP x op.
O.w., return Nothing. *)
Fixpoint find_unit_pro_in_clause (c: clause) (J: partial_asgn) (cont: UP_result): UP_result :=
  match c with
  | nil => cont
  | (op, x) :: c' =>
      match PV.look_up x J with
      | None => match cont with
                | Conflict => find_unit_pro_in_clause c' J (UP x op)
                | UP _ _ => Nothing
                | _ => Nothing
                end
      | Some b => if eqb op b then Nothing else find_unit_pro_in_clause c' J cont
      end
  end.

Definition unit_pro' (P: CNF) (J: partial_asgn): list UP_result :=
  map (fun c => find_unit_pro_in_clause c J Conflict) P.

 (* Type of fold_left: (A -> B -> A) -> list B -> A -> A. 
Below, A is option partial_asgn and B is UP_res. *)
Check fold_left.
Print fold_left.
(** Construct partial asgn from a list of UP_result. *)
Definition fold_UP_result (rs: list UP_result): option partial_asgn :=
  fold_left (fun (o: option partial_asgn) (r: UP_result) =>
               match r, o with
               | _, None => None
               | Nothing, _ => o
               | Conflict, _ => None
               | UP x b, Some J => Some ((x, b) :: J)
               end) rs (Some nil).

(** Improve partial_asgn by unit propagation. *)
Definition unit_pro (P: CNF) (J: partial_asgn): option partial_asgn :=
  fold_UP_result (unit_pro' P J).
  
(* ***************************************************************** *)
(*                                                                   *)
(*  Filter                                                           *)
(*                                                                   *)
(* ***************************************************************** *)

(** Literal of value false will be eliminated by _[clause_filter]_ from
    a clause. Literals of value true and literals of an unknown value
    will be left. *)
Definition clause_filter (J: partial_asgn) (c: clause): clause :=
  filter (fun opx: bool * ident =>
            match opx with
            | (op, x) => match PV.look_up x J with
                         | None => true
                         | Some b => eqb b op
                         end
            end) c.

(** This function _[clause_not_ex_true]_ tests whether no literal in the
    clause is known to be true. *)
Definition clause_not_ex_true (J: partial_asgn) (c: clause): bool :=
  negb 
  (existsb
      (fun opx: bool * ident =>
            match opx with
            | (op, x) => match PV.look_up x J with
                         | None => false
                         | Some b => eqb b op
                         end
            end) c).

(** After all, literals that are known to be false are eliminated;
    clauses with at least one literal known to be true are alsi
    eliminated. *)
Definition CNF_filter (P: CNF) (J: partial_asgn): CNF :=
  map (clause_filter J) (filter (clause_not_ex_true J) P).
  
(* ***************************************************************** *)
(*                                                                   *)
(*  DPLL                                                             *)
(*                                                                   *)
(* ***************************************************************** *)

(* Pick P is the first literal of P. *)
Definition pick (P: CNF): ident :=
  match P with
  | ((_, x) :: _) :: _ => x
  | _ => "impossible"%string
  end.

Fixpoint DPLL_UP (P: CNF) (J: partial_asgn) (n: nat): bool :=
  match n with 
  | O => true 
  | S n' =>
    match unit_pro P J with  (* apply unit propagation to improve assignment *)
    | None => false
    | Some kJ => 
      match kJ with
        | nil => DPLL_filter P J n'  (* no unit, filter by assignment *)
        | _ => DPLL_UP P (kJ ++ J) n' (* improve assignment *)
      end
    end
  end
with DPLL_filter (P: CNF) (J: partial_asgn) (n: nat): bool :=
  match n with 
    | O => true
    | S n' => DPLL_pick (CNF_filter P J) nil n' (* eliminate literals that are already known *)
  end
with DPLL_pick (P: CNF) (J: partial_asgn) (n: nat): bool :=
  match n with 
    | O => true
    | S n' =>
      let x := pick P in
      DPLL_UP P ((x, true) :: J) n' || DPLL_UP P ((x, false) :: J) n'  (* DFS *)
  end.

(* ***************************************************************** *)
(*                                                                   *)
(*  Examples                                                         *)
(*                                                                   *)
(* ***************************************************************** *)

Local Open Scope string.

Definition cnf1 :=
  ((true, "x") :: (true, "y") :: nil) :: ((true, "x") :: (false, "y") :: nil) :: nil.

Eval compute in (DPLL_UP cnf1 nil 6).

Definition cnf2 :=
  ((true, "x") :: (true, "y") :: nil) :: ((true, "x") :: (false, "y") :: nil) :: ((false, "x") :: nil) :: nil.

Eval compute in (DPLL_UP cnf2 nil 6).

Definition cnf3 :=
  ((false, "x") :: (true, "y") :: nil) ::
  ((false, "y") :: (true, "z") :: nil) ::
  ((false, "z") :: (true, "w") :: nil) ::
  ((true, "x") :: nil) ::
  ((false, "w") :: nil) :: nil.

Eval compute in (DPLL_UP cnf3 nil 12).
Close Scope string.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Definition of Satisfiability                                     *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Lemma ident_eqdec: forall x y: ident, {x=y}+{x<>y}. 
Proof. apply string_dec. Qed.

Check PV.eqb_eq.

Check PV.eqb_neq.

Check Bool.eqb_true_iff.

Check Bool.eqb_false_iff.

Definition asgn_match(J:partial_asgn)(B:asgn):=
  forall x b, PV.look_up x J = Some b -> B x = b. 

Definition expand(J:partial_asgn): asgn:=
  fun x =>
    match PV.look_up x J with
    | Some b => b
    | None => true
    end.


Definition set_ident(B:asgn)(s:ident)(b:bool):asgn:=
  fun x => if ident_eqdec x s then b else B x.
  
(** CNF_sat: CNF -> asgn -> bool *)
Definition literal_sat(l: bool * ident)(B:asgn):bool:=
  match l with
  | (b,x) => eqb b (B x)
  end. 

Print fold_right.  

 (* Type of fold_right: (B -> A -> A) -> A -> list B -> A. 
Below, A is bool and B is (bool * ident). *)
Definition clause_sat(C:clause)(B:asgn):bool:=
  fold_right (fun l => orb (literal_sat l B)) false C.

(* Below, A is bool and B is clause. *)
Definition CNF_sat (P:CNF)(B:asgn):bool:=
  fold_right (fun c => andb (clause_sat c B)) true P.

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Your goal: prove CNF is not satisfiable if DPLL returns false    *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

(**  Proving following lemmas may be helpful.

     But you can ignore them if you can prove the final theorem
     _[DPLL_sound]_ without these lemmas. *)

Lemma find_unit_pro_in_clause_Conflict:
  forall c J B,
    find_unit_pro_in_clause c J Conflict = Conflict ->
    asgn_match J B ->
    clause_sat c B = false.
Proof. 

Admitted.

Lemma find_unit_pro_in_clause_Conflict_UP:
  forall c J B x b,
    find_unit_pro_in_clause c J Conflict = UP x b ->
    asgn_match J B ->
    clause_sat c B = true ->
    asgn_match ((x, b) :: J) B.
Proof.
  intros.
  unfold asgn_match.
  intros.
  destruct (ident_eqdec x x0).
  + simpl in H2.
     destruct (PV.eqb x x0) eqn:?.
     - injection H2.
        intros.
        subst x0 b0.
        clear Heqb1 H2.
        admit.
        (* induction c.
        * discriminate H.
        * destruct a as (op, x0).
           simpl in H1.
            *)
     - subst x0.
        unfold PV.eqb in Heqb1.
        destruct (PV.eq_dec x x) eqn:?.
        * discriminate Heqb1.
        * contradiction n. tauto.
  + simpl in H2.
     destruct (PV.eqb x x0) eqn:?.
     - destruct (PV.eqb x x0) eqn:?.
       unfold PV.eqb in Heqb0.
       destruct (PV.eq_dec x x0) eqn:?.
       subst x. contradiction n.
       * tauto.
       * discriminate Heqb0.
       * discriminate Heqb1.
     - apply H0. tauto.
Admitted.

Lemma clause_filter_sat: forall c J B,
    asgn_match J B ->
    clause_sat c B = true ->
    clause_sat (clause_filter J c) B = true.
Proof. 
  intros.
  unfold asgn_match in H.
  induction c.
  + unfold clause_sat in H0; unfold fold_right in H0. discriminate.
  + simpl.
    destruct a as [op x].
    destruct (PV.look_up x J) eqn:?; simpl.
    - destruct (eqb b op) eqn:?; simpl; apply H in Heqo.
      --rewrite Heqo. 
        rewrite eqb_true_iff in Heqb0.
        assert (op = b). { auto. }
        rewrite <-eqb_true_iff in H1.
        rewrite H1. simpl; reflexivity. 
      --unfold clause_sat in H0; unfold fold_right in H0; unfold literal_sat in H0.
        rewrite Heqo in H0.
        rewrite eqb_false_iff in Heqb0.
        assert (op <> b). { auto. }
        rewrite <-eqb_false_iff in H1.
        rewrite H1 in H0. 
        simpl in H0.
        specialize (IHc H0); apply IHc.
    - unfold fold_right in H0; unfold literal_sat in H0.
      destruct (eqb op (B x)) eqn:?; simpl.
      --reflexivity.
      --simpl in H0.
        rewrite Heqb in H0. 
        simpl in H0.
        specialize (IHc H0); apply IHc.
Qed.

Lemma CNF_filter_sat: forall P J B,
    asgn_match J B ->
    CNF_sat P B = true ->
    CNF_sat (CNF_filter P J ) B = true.
Proof.
  intros.
  induction P.
  + unfold CNF_sat; unfold fold_right; unfold CNF_filter. 
    simpl; reflexivity.
  + unfold CNF_sat in *; unfold fold_right in *; unfold CNF_filter in *; simpl. 
    destruct (clause_not_ex_true J a) eqn:?; simpl.
    - destruct (clause_sat a B) eqn:?; simpl.
      --pose proof clause_filter_sat a J B.
        pose proof H1 H Heqb0.
        simpl in H0.
        specialize (IHP H0).
        rewrite H2; simpl.
        apply IHP.
      --simpl in H0. discriminate.
    - destruct (clause_sat a B) eqn:?; simpl.
      --pose proof clause_filter_sat a J B.
        pose proof H1 H Heqb0.
        simpl in H0.
        specialize (IHP H0).
        apply IHP.
      --simpl in H0. discriminate.
Qed.

Lemma CNF_sat_pick_fail: forall x J B,
    asgn_match J B ->
    asgn_match ((x,true)::J) B \/ asgn_match ((x,false)::J) B.
Proof.
  intros.
(*   discuss B x = true or false *)
  destruct (B x) eqn:?.
  + left.
      unfold asgn_match.
      intros.
      destruct (ident_eqdec x x0).
      - subst x0.
        simpl in H0.
        destruct (PV.eqb x x) eqn:?.
        * injection H0.
           intros. subst b. tauto.
        * unfold PV.eqb in Heqb0.
           destruct (PV.eq_dec x x). discriminate Heqb0. contradiction n. tauto.
      - simpl in H0.
        destruct (PV.eqb x x0) eqn:?.
        * unfold PV.eqb in Heqb0.
          destruct (PV.eq_dec x x0).
          ++ subst x. contradiction.
          ++ discriminate Heqb0.
        * apply H. tauto.
  + right.
      unfold asgn_match.
      intros.
      destruct (ident_eqdec x x0).
      - subst x0.
        simpl in H0.
        destruct (PV.eqb x x) eqn:?.
        * injection H0.
           intros. subst b. tauto.
        * unfold PV.eqb in Heqb0.
           destruct (PV.eq_dec x x). discriminate Heqb0. contradiction n. tauto.
      - simpl in H0.
        destruct (PV.eqb x x0) eqn:?.
        * unfold PV.eqb in Heqb0.
          destruct (PV.eq_dec x x0).
          ++ subst x. contradiction.
          ++ discriminate Heqb0.
        * apply H. tauto.
Qed.
(* Admitted. *)

(* ***************************************************************** *)
(*                                                                   *)
(*                                                                   *)
(*  Final Theorems: Soundness of DPLL                                *)
(*                                                                   *)
(*                                                                   *)
(* ***************************************************************** *)

Lemma DPLL_UP_false_Jsat: forall n P J B,
    DPLL_UP P J n = false ->
    CNF_sat P B = true ->
    asgn_match J B ->
    False
with
  DPLL_filter_false_Jsat: forall n P J B,
    DPLL_filter P J n = false ->
    CNF_sat P B = true ->
    asgn_match J B ->
    False
with 
  DPLL_pick_false_Jsat: forall n P J B,
    DPLL_pick P J n = false ->
    CNF_sat P B = true ->
    asgn_match J B ->
    False.
Proof.
  + clear DPLL_UP_false_Jsat.
      intros n.
      induction n.
      - intros.
        unfold DPLL_UP in H. discriminate H.
      - intros.
        simpl in H.
        destruct (unit_pro P J) eqn:Hup.
        * destruct p eqn:Hp.
           ++ specialize (DPLL_filter_false_Jsat n P J B).
                 apply DPLL_filter_false_Jsat; tauto.
           ++ specialize (IHn P ((p0 :: p1) ++ J) B).
                 apply IHn; try tauto.
                 assert (asgn_match (p0 :: p1) B).
                 --
                    admit.
                 --
                    admit.
        * (* conflict is derived *)
          unfold unit_pro in Hup.
          admit.
  + clear DPLL_filter_false_Jsat.
      intros n.
      induction n.
      - intros.
        unfold DPLL_filter in H. discriminate H.
      - intros.
        simpl in H.
        specialize (DPLL_pick_false_Jsat n (CNF_filter P J) [] B).
        apply DPLL_pick_false_Jsat; try tauto.
        * specialize (CNF_filter_sat P J B).
           tauto.
        * unfold asgn_match.
           intros.
           unfold PV.look_up in H2. discriminate H2.
  + clear DPLL_pick_false_Jsat.
      admit.
Admitted.

Theorem DPLL_sound: forall n P M,
  DPLL_UP P nil n = false ->
  CNF_sat P M = false.
Proof.
Admitted.
