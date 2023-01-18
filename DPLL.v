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

(* Pick P is the first identifier of P. *)
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

Lemma UP_cannot_to_Conflict: forall c J x op,
  find_unit_pro_in_clause c J (UP x op) = Conflict -> False.
Proof.
  intros.
  induction c.
  + simpl in H. discriminate H.
  + simpl in H.
      destruct a as (op0, x0).
      destruct (PV.look_up x0 J) eqn:?.
      - destruct (eqb op0 b) eqn:?.
        * discriminate H.
        * tauto.
      - discriminate H.
Qed.

Lemma find_unit_pro_in_clause_Conflict:
  forall c J B,
    find_unit_pro_in_clause c J Conflict = Conflict ->
    asgn_match J B ->
    clause_sat c B = false.
Proof.
  intros.
  induction c.
  + simpl. tauto.
  + simpl.
      unfold orb.
      destruct (literal_sat a B) eqn:?.
      - simpl in H.
        destruct a as (op,x).
        destruct (PV.look_up x J) eqn:?.
        * unfold asgn_match in H0.
           specialize (H0 x b).
           specialize (H0 Heqo).
           unfold literal_sat in Heqb.
           rewrite H0 in Heqb.
           rewrite Heqb in H.
           discriminate H.
        * specialize (UP_cannot_to_Conflict c J x op). tauto.
      - apply IHc.
        simpl in H.
        destruct a as (op,x).
        destruct (PV.look_up x J) eqn:?.
        * unfold asgn_match in H0.
           specialize (H0 x b).
           specialize (H0 Heqo).
           unfold literal_sat in Heqb.
           rewrite H0 in Heqb.
           rewrite Heqb in H.
           tauto.
        * specialize (UP_cannot_to_Conflict c J x op). tauto.
Qed.

Lemma UP_remain:
  forall c J x b x0 b0,
    find_unit_pro_in_clause c J (UP x0 b0) = UP x b ->
    (x = x0 /\ b = b0).
Proof.
  intros.
  induction c.
  + simpl in H. injection H. auto.
  + simpl in H. destruct a as (op,x1).
      destruct (PV.look_up x1 J) eqn:H1.
      - destruct (eqb op b1) eqn:Hop.
        * discriminate H.
        * auto.
      - discriminate H.
Qed.

Lemma UP_unchange_implies_unmatch:
  forall c J B x b,
    find_unit_pro_in_clause c J (UP x b) = UP x b ->
    clause_sat c B = true ->
    asgn_match J B ->
    False.
Proof.
  intros.
  induction c.
  + simpl in H0. discriminate H0.
  + destruct a as (b0, x0).
      simpl in H0.
      unfold orb in H0.
      destruct (eqb b0 (B x0)) eqn:Hb0.
      - simpl in H.
        destruct (PV.look_up x0 J) eqn:?.
        * destruct (eqb b0 b1) eqn:Hb1.
          ++ discriminate H.
          ++ unfold asgn_match in H1.
                specialize (H1 x0 b1 Heqo).
                rewrite eqb_true_iff in Hb0.
                rewrite <- Hb0 in H1.
                rewrite eqb_false_iff in Hb1. auto.
        * discriminate H. 
      - apply IHc; try tauto. clear IHc.
        simpl in H.
        destruct (PV.look_up x0 J) eqn:?.
        * destruct (eqb b0 b1) eqn:Hb1.
           ++ discriminate H.
           ++ tauto.
        * discriminate H.
Qed.

Lemma find_unit_pro_in_clause_Conflict_UP:
  forall c J B x b,
    find_unit_pro_in_clause c J Conflict = UP x b ->
    asgn_match J B ->
    clause_sat c B = true ->
    asgn_match ((x, b) :: J) B.
Proof.
  intros.
  induction c; simpl.
  + unfold clause_sat in *; unfold fold_right in *; discriminate.
  + destruct a as [op id].
    unfold find_unit_pro_in_clause in *.
    destruct (PV.look_up id J) eqn:?.
    - destruct (eqb op b0) eqn:?.
      -- discriminate.
      -- pose proof IHc H.
        simpl in H1.
        pose proof H0 id b0.
        specialize (H3 Heqo).
        rewrite H3 in H1.
        rewrite Heqb1 in H1.
        simpl in H1.
        specialize (H2 H1).
        apply H2.
    - simpl in *.
      unfold asgn_match in *. 
      simpl in *.
      intros.
      destruct (PV.eqb x x0) eqn:?.
      -- pose proof PV.eqb_eq x x0.
         rewrite H3 in Heqb1.
         injection H2. intros. subst x0 b0. simpl in *.
         assert (find_unit_pro_in_clause c J (UP id op) = UP x b) by auto. clear H.
         specialize (UP_remain c J x b id op). intros.
         specialize (H H4). destruct H. subst id op. clear H2 H3.
         unfold orb in H1.
         destruct (eqb b (B x)) eqn:HB.
         * rewrite eqb_true_iff in HB. auto.
         * specialize (UP_unchange_implies_unmatch c J B x b). intros.
            specialize (H H4 H1 H0). contradiction H.
      -- pose proof H0 x0 b0.
         specialize (H3 H2).
         apply H3.
Qed.

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
           destruct (PV.eq_dec x x). 
           ++ discriminate Heqb0.
           ++ contradiction n. tauto.
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

Lemma none_implies_none: forall rs,
  fold_left (fun (o: option partial_asgn) (r: UP_result) =>
           match r, o with
           | _, None => None
           | Nothing, _ => o
           | Conflict, _ => None
           | UP x b, Some J => Some ((x, b) :: J)
           end) rs None = None.
Proof.
  induction rs; simpl.
  + tauto.
  + destruct a; tauto.
Qed.

Lemma none_hold: forall rs J1 J2,
  fold_left (fun (o: option partial_asgn) (r: UP_result) =>
           match r, o with
           | _, None => None
           | Nothing, _ => o
           | Conflict, _ => None
           | UP x b, Some J => Some ((x, b) :: J)
           end) rs (Some J1) = None ->
  fold_left (fun (o: option partial_asgn) (r: UP_result) =>
           match r, o with
           | _, None => None
           | Nothing, _ => o
           | Conflict, _ => None
           | UP x b, Some J => Some ((x, b) :: J)
           end) rs (Some J2) = None.
Proof.
  induction rs.
  + simpl. intros. discriminate H.
  + intros. simpl in *.
      destruct a eqn:Ha.
      - specialize (none_implies_none rs). intros. tauto.
      - specialize (IHrs ((x, b) :: J1) ((x, b) :: J2)). tauto.
      - specialize (IHrs J1 J2). tauto.
Qed.

Lemma split_keep_none: forall rs x b,
  fold_UP_result (UP x b :: rs) = None ->
  fold_UP_result rs = None.
Proof.
  intros. unfold fold_UP_result in *. simpl in H.
  specialize (none_hold rs [(x, b)] []). intros. tauto.
Qed.

Lemma none_remain: forall rs x b,
  fold_UP_result rs = None ->
  fold_UP_result (UP x b :: rs) = None.
Proof.
  intros. unfold fold_UP_result in *. simpl.
  specialize (none_hold rs [] [(x,b)]). intros. tauto.
Qed.

Lemma asgn_match_join: forall J1 J2 B,
  asgn_match J1 B ->
  asgn_match J2 B ->
  asgn_match (J1 ++ J2) B.
Proof.
  
Admitted.

Lemma asgn_match_split: forall J1 J2 B,
  asgn_match (J1 ++ J2) B ->
  asgn_match J1 B.
Proof.
  
Admitted.

Lemma asgn_match_impr: forall J1 J2 B x b rs,
  fold_UP_result (UP x b :: rs) = Some J1 ->
  fold_UP_result rs = Some J2 ->
  asgn_match J2 B ->
  B x = b ->
  asgn_match J1 B.
Proof.
  
Admitted.

Lemma unit_pro_keep_match: forall P J J1 B,
  unit_pro P J = Some J1 ->
  CNF_sat P B = true ->
  asgn_match J B ->
  asgn_match (J1 ++ J) B.
Proof.
  induction P.
  + intros.
      unfold unit_pro in H.
      simpl in H.
      unfold fold_UP_result in H.
      simpl in H.
      injection H. intros. rewrite <- H2. simpl. tauto.
  + intros.
      remember (unit_pro P J) as oJ2.
      assert (unit_pro P J = oJ2) by auto.
      destruct oJ2 eqn:?.
      - remember p as J2. clear HeqoJ2 Heqo oJ2 HeqJ2 p.
        simpl in H0. unfold andb in H0.
        destruct (clause_sat a B) eqn:?.
        * specialize (IHP J J2 B H2 H0 H1).
           destruct (find_unit_pro_in_clause a J Conflict) eqn:Ha.
           ++ (* H is impossible *)
                 unfold unit_pro in H. simpl in H.
                 rewrite Ha in H.
                 unfold fold_UP_result in H. simpl in H.
                 specialize (none_implies_none (unit_pro' P J)). intros.
                 rewrite H3 in H. discriminate H.
           ++ pose proof find_unit_pro_in_clause_Conflict_UP a J B x b.
                 specialize (H3 Ha H1 Heqb).
                 unfold unit_pro in H. simpl in H.
                 rewrite Ha in H.
                 assert (asgn_match J1 B). {
                   specialize (asgn_match_split J2 J B). intros.
                   specialize (H4 IHP).
                   unfold unit_pro in H2.
                   assert (B x = b). {
                     unfold asgn_match in H3.
                     specialize (H3 x b). simpl in H3.
                     assert (PV.eqb x x = true). {
                        rewrite PV.eqb_eq. tauto.
                     }
                     rewrite H5 in H3. auto.
                   }
                   specialize (asgn_match_impr J1 J2 B x b (unit_pro' P J)). intros. auto.
                 }
                 specialize (asgn_match_join J1 J B). auto.
           ++ assert (J1 = J2). {
                   unfold unit_pro in H. simpl in H.
                   rewrite Ha in H.
                   unfold fold_UP_result in H. simpl in H.
                   assert (fold_UP_result (unit_pro' P J) = Some J1) by auto.
                   assert (unit_pro P J = Some J1) by auto.
                   rewrite H4 in H2. injection H2. tauto. 
                 }
                 rewrite H3. tauto.
        * discriminate H0.
      - unfold unit_pro in H, H2. simpl in H.
        destruct (find_unit_pro_in_clause a J Conflict) eqn:?.
        * unfold fold_UP_result in H. simpl in H.
           specialize (none_implies_none (unit_pro' P J)). intros.
           rewrite H3 in H. discriminate H.
        * specialize (none_remain (unit_pro' P J) x b).
           intros. specialize (H3 H2). rewrite H3 in H. discriminate H.
        * unfold fold_UP_result in H, H2. simpl in H.
           rewrite H in H2. discriminate H2.
Qed.



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
           ++ rewrite <- Hp in *.
                 specialize (IHn P (p ++ J) B).
                 apply IHn; try tauto.
                 specialize (unit_pro_keep_match P J p B).
                 intros. tauto.
        * (* conflict is derived *)
           (* One clause contradicts with J, so B cannot satisfy P. *)
          induction P.
          ++ unfold unit_pro in Hup.
                simpl in Hup.
                unfold fold_UP_result in Hup.
                simpl in Hup. discriminate Hup.
          ++ (* If _[a]_ contradicts with _[J]_, then _[B]_ cannot satisfy _[a]_.
                O.w., use _[IHP]_. *)
                destruct (find_unit_pro_in_clause a J Conflict) eqn:Ha.
                -- specialize (find_unit_pro_in_clause_Conflict a J B).
                    intros.
                    specialize (H2 Ha H1).
                    simpl in H0.
                    unfold andb in H0.
                    rewrite H2 in H0. discriminate H0.
                -- apply IHP.
                   ** unfold unit_pro in Hup.
                        simpl in Hup.
                        rewrite Ha in Hup.
                        specialize (split_keep_none (unit_pro' P J) x b).
                        tauto.
                   ** simpl in H0.
                        unfold andb in H0.
                        destruct (clause_sat a B).
                        +++ tauto.
                        +++ discriminate H0.
                -- apply IHP.
                   ** unfold unit_pro in Hup.
                        simpl in Hup.
                        rewrite Ha in Hup.
                        assert (fold_UP_result (unit_pro' P J) = None). {
                          unfold fold_UP_result in Hup.
                          simpl in Hup.
                          tauto.
                        }
                        tauto.
                   ** simpl in H0.
                        unfold andb in H0.
                        destruct (clause_sat a B).
                        +++ tauto.
                        +++ discriminate H0.
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
      intros n.
      induction n.
      - intros.
        unfold DPLL_pick in H. discriminate H.
      - intros.
        simpl in H.
        remember (pick P) as x.
        unfold orb in H.
        destruct (DPLL_UP P ((x, true) :: J) n) eqn:?.
        * discriminate H.
        * specialize (CNF_sat_pick_fail x J B).
           intros.
           apply H2 in H1. clear H2.
           destruct H1.
           ++ specialize (DPLL_UP_false_Jsat n P ((x, true) :: J) B).
                 apply DPLL_UP_false_Jsat; try tauto.
           ++ specialize (DPLL_UP_false_Jsat n P ((x, false) :: J) B).
                 apply DPLL_UP_false_Jsat; try tauto.
Qed.

Theorem DPLL_sound: forall n P M,
  DPLL_UP P nil n = false ->
  CNF_sat P M = false.
Proof.
  intros.
  specialize (DPLL_UP_false_Jsat n P nil M).
  intros.
  destruct (CNF_sat P M) eqn:?.
  + apply H0 in H.
      - contradiction H.
      - tauto.
      - unfold asgn_match.
        intros.
        simpl in H1.
        discriminate H1.
  + tauto.
Qed.
