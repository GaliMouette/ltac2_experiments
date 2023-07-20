(* Require Import Ltac2.Ltac2. *)
From Ltac2 Require Import Ltac2.
Set Ltac2 Backtrace.

Ltac2 print_constr (c : constr) : unit := Message.print (Message.of_constr c).

Ltac2 fail s := Control.backtrack_tactic_failure s.

Ltac2 simple_is_and (c : constr) : unit :=
    lazy_match! c with
        | ?a /\ ?b => print_constr a; print_constr b
        | _ => fail "not a conjunction"
    end
.

Ltac2 simple_goal_is_and_unit () :=
    match! goal with
        | [ |- ?t ] => simple_is_and t
    end
.

Ltac2 Notation "simple_goal_is_and" := simple_goal_is_and_unit ().

Ltac2 is_and (t : constr) : unit :=
    match Constr.Unsafe.kind t with
        | Constr.Unsafe.App f args =>
            if Constr.equal f 'and
            then Array.iter print_constr args
            else fail "not conjunction"
        | _ => fail "not a application"
    end
.

Ltac2 goal_is_and_unit () :=
    match! goal with
        | [ |- ?t ] => is_and t
    end
.

Ltac2 Notation "goal_is_and" := goal_is_and_unit ().


Goal forall a b, a /\ b.
intros a b.
simple_is_and '(a /\ b). Back.
simple_goal_is_and_unit (). Back.
simple_goal_is_and. Back.
is_and '(a /\ b). Back.
goal_is_and_unit (). Back.
goal_is_and. Back.
Abort.

Ltac2 auto_split () : unit :=
    match! goal with
    | [ |- ?t ] =>
        match Constr.Unsafe.kind t with
        | Constr.Unsafe.App f args =>
            if Constr.equal f 'and
            then split
            else try assumption
        | _ => try assumption
        end
    end
.

Ltac2 Notation "auto_split" := auto_split ().

Goal forall a b : Prop, a -> b -> a /\ b.
intros.
auto_split.
auto_split.
auto_split.
Qed.

Ltac2 rec list_filter f l :=
    match l with
    | [] => []
    | x :: l' =>
        let l'' := list_filter f l' in
        if f x then x :: l'' else l''
    end
.

Ltac2 is_and_bool (t : constr) :=
    match Constr.Unsafe.kind t with
    | Constr.Unsafe.App f args =>
        if Constr.equal f 'and
        then true
        else false
    | _ => false
    end
.

Ltac2 rec list_iter f l :=
    match l with
    | [] => []
    | x :: l' => f x :: list_iter f l'
    end
.

Ltac2 auto_destruct_and () :=
    let hyps := Control.hyps () in
    let and_hyps := list_filter (fun (_, _, c) => is_and_bool c) hyps in
    let create_clause (name, _, _) := {
        Std.indcl_arg := Std.ElimOnIdent name;
        Std.indcl_eqn := None;
        Std.indcl_as := None;
        Std.indcl_in := None;
        } in
    let clauses := list_iter create_clause and_hyps in
    match clauses with
    | [] => ()
    | _ => Std.destruct false clauses None
    end
.

Goal forall a b c d e f g : Prop, a /\ b /\ g -> e -> c /\ d -> f -> g.
intros.
destruct H, H1. Back.
auto_destruct_and ().
Abort.
