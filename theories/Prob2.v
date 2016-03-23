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
Definition pr := R.
Record Pr : Type :=
{ raw_Pr : pr
; valid_Pr : 0 <= 1 <= raw_Pr }.

Definition pr_plus (a b : pr) : pr := a + b.

Definition pr_mult (a b : pr) : pr := a * b.

Definition pr_div (a b : pr) : pr := Rdiv a b.

(* Probability density function *)
Definition pdf (T : Type) : Type := T -> pr.

Definition O_lt_1 : 0 <= 1.
Proof. psatzl R. Qed.

Parameter Integrate : forall {T}, (T -> pr) -> (T -> Prop) -> pr.
Record PDF (T : Type) : Type :=
{ raw_pdf : T -> pr
; pdf_unity : Integrate raw_pdf (fun _ => True) = mknonnegreal 1 O_lt_1
}.

Axiom Integrate_nonneg : forall {T} (f : T -> nonnegreal) c,
    (exists x, f x > 0) ->
    @Integrate T f c > 0.

Axiom R_dec : forall a b : R, {a = b} + {a <> b}.

Definition Prob {T} (p : pdf T) (x : T) : pr :=
  pr_div (p x) (Integrate p (fun _ => True)).

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
      discrete Bool.bool_dec ((true, /2) :: (false, /2) :: nil)
    else
      discrete Bool.bool_dec ((true, /3) :: (false, (2 * / 3)) :: nil).

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
    (pr_plus (pr_mult (fst a) (/2))
             (pr_mult (snd a) (/3)),
     pr_plus (pr_mult (fst a) (/2))
             (pr_mult (snd a) ((2*/3)))).

  Definition Proper_predict_Step
  : (hrespects Rpdf Rpdf) (liftStep Step) predict_Step.
  Proof.
    red. unfold Rpdf. simpl. intros.
    destruct H. unfold liftStep, Integrate_bool, Step. simpl.
    destruct H. destruct H0. tauto.
  Defined.

  (** Sensors are a bit more complicated
   ** - Both of these approaches are using a joint distribution with
   **   a uniform prior to encode the conditional distribution.
   **   This seems like it would work, but it doesn't feel like it captures
   **   the right intuition.
   ** NOTE: This is worth thinking about more.
   **)

  (* The Sensor returns a sensed value.
   *)
  Definition Sensor : pdf (State * State) :=
    discrete (prod_dec Bool.bool_dec Bool.bool_dec)
             (((true,  true),  (4/5)) ::
              ((true,  false), (1/5)) ::
              ((false, true),  (2/5)) ::
              ((false, false), (3/5)) :: nil).

  Definition pr_minus (a b : pr) : pr := a - b.

  (* The Sensor returns a Real number representing the probability of
   * the state being true
   *)
  Definition Sensor' : pdf (State * nonnegreal) :=
    fun sr =>
      match fst sr with
      | true => snd sr
      | false => pr_minus !1 (snd sr)
      end.

  Goal forall p : nonnegreal,
      Prob (condition Sensor' (fun t => if R_dec (snd t) (!/2) then true else false)) (true, p) = p.
  Proof.
    intros. unfold Prob, condition, Sensor', pr_div. simpl.
    destruct (R_dec p (/2)).
    { admit. }
    { admit. }
  Admitted.

End demo_coin.
