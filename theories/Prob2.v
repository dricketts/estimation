Require Import Setoid.
Require Import Coq.micromega.Psatz.
Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Coquelicot.RInt_gen.

Require Import SMTC.Tactic.
Set SMT Solver "z3".
Axiom by_smt : forall P : Prop, P.

(** Simple hrelations **)
Definition hrelation (A B : Type) : Type := A -> B -> Prop.
Definition hrespects {A B C D : Type}
           (rD : hrelation A B) (rC : hrelation C D)
  : hrelation (A -> C) (B -> D) :=
  fun f g =>
    forall x y, rD x y -> rC (f x) (g y).


Instance Refl_Rle : Reflexive Rle := Rle_refl.

Local Notation "! n" := (mknonnegreal n%R ltac:(psatzl R)) (at level 0).

(* A probability *)
Definition pr := nonnegreal.

Definition pr_plus (a b : pr) : pr.
refine (mknonnegreal (a + b) _).
destruct a; destruct b. simpl. psatzl R.
Defined.

Definition pr_mult (a b : pr) : pr.
refine (mknonnegreal (a * b) _).
destruct a; destruct b. simpl. psatz R.
Defined.

Definition pr_div (a b : pr) (pf : b > 0) : pr.
refine (mknonnegreal (a / b) _).
destruct a. destruct b.
simpl in *.
eapply Rle_div_l.
eapply Rinv_0_lt_compat. psatz R.
smt solve; apply by_smt.
Defined.

(* Probability density function *)
Definition pdf (T : Type) : Type := T -> pr.

Parameter Integrate : forall {T}, (T -> nonnegreal) -> (T -> Prop) -> nonnegreal.

Axiom Integrate_nonneg : forall {T} (f : T -> nonnegreal) c,
    (exists x, f x > 0) ->
    @Integrate T f c > 0.

Axiom R_dec : forall a b : R, {a = b} + {a <> b}.


Definition Pr {T} (p : pdf T) (x : T) : nonnegreal.
refine (
  if R_dec (p x) 0 then
    !0
  else
    pr_div (p x) (Integrate p (fun _ => True)) _).
eapply Integrate_nonneg. exists x.
destruct (p x); simpl in *. psatz R.
Defined.

Definition condition {T} (p : pdf T) (c : T -> bool) : pdf T :=
  fun x =>
    if c x then
      p x
    else !0.

Section discrete.
  Require Import Coq.Lists.List.
  Context {T : Type}.
  Variable T_dec : forall x y : T, {x = y} + {x <> y}.
  Fixpoint discrete (ls : list (T * pr)) : pdf T :=
    match ls with
    | nil => fun _ => !0
    | (x,p) :: ls' => fun x' => if T_dec x x' then p else discrete ls' x'
    end%R.
End discrete.

Definition prod_dec {A B : Type}
           (A_dec : forall x y : A, {x = y} + {x <> y})
           (B_dec : forall x y : B, {x = y} + {x <> y})
: forall x y : A * B, {x = y} + {x <> y}.
  decide equality.
Defined.

Module demo_coin.
  Definition State := bool.

  Definition Step (pre : State) : pdf State :=
    if pre then
      discrete Bool.bool_dec ((true, ! /2) :: (false, ! /2) :: nil)
    else
      discrete Bool.bool_dec ((true, ! /3) :: (false, ! (2 * / 3)) :: nil).

  (* Abstract probability distribution functions *)
  Definition Apdf : Type := pr * pr.

  Definition Rpdf (l : pdf State) (r : Apdf) : Prop :=
    l true = fst r /\
    l false = snd r.

  Definition Integrate_bool (f : bool -> pr) : pr :=
    pr_plus (f true) (f false).

  Definition liftStep (R : State -> pdf State)
             (pre : pdf State) : pdf State :=
    fun to =>
      Integrate_bool (fun from => pr_mult (pre from) (R from to)).

  Definition predict_Step (a : Apdf) : Apdf :=
    (pr_plus (pr_mult (fst a) (!/2))
             (pr_mult (snd a) (!/3)),
     pr_plus (pr_mult (fst a) (!/2))
             (pr_mult (snd a) (!(2*/3)))).

  Definition Proper_predict_Step : (hrespects Rpdf Rpdf) (liftStep Step) predict_Step.
  Proof.
    red. unfold Rpdf. simpl. intros.
    destruct H. unfold liftStep, Integrate_bool, Step. simpl.
    destruct H. destruct H0. tauto.
  Defined.

  (* The Sensor returns a Real number representing the probability of
   * the state being true
   * NOTE: This does not seem accurate because it is communicating too
   *       much information. What I'm trying to express is:
   *       "if the state is true, the sensor should report true with
   *        a probability of [4/5] and if the sensor is false, the
   *        sensor should report true with probability [2/5]"
   * With that explanation, this following definition seems completely wrong.
   *)
  Definition Sensor : pdf (State * nonnegreal) :=
    fun sr =>
      match fst sr with
      | true => if R_dec (snd sr) !(4 * /5) then
                  !1
                else
                  !0
      | false => if R_dec (snd sr) !(2 * /5) then
                   !1
                 else
                   !0
      end.


End demo_coin.

Axiom normal : forall (m : R) (sd : nonnegreal), pdf R.
