Require Import Coq.Reals.Reals.

Local Open Scope R_scope.

(* TODO: There actually needs to be a measure space for T
         and A needs to be a measureable set. *)
(* TODO: This probably needs to return a Prop because
   the integral is not always defined. However, it
   simplifies the presentation if this function
   is total. *)
Definition Lebesgue_int {T : Type} (f : T -> R)
           (A : T -> Prop) : R.
Admitted.

(* Probability density function *)
(* TODO: This should actually return a nonnegreal
   and should have other properties as well. *)
Definition pdf (T : Type) : Type := T -> R.

Section RecursiveBayesian.

  (****************************************************)
  (* The following is a specification of a system.    *)
  (****************************************************)

  (* The physical state of the system. *)
  Variable state : Type.
  (* The physical evolution of the system. Evolution is
     probabilistic. The means that if the system is
     in state s, the next state is a sample from
     evolve s. *)
  Variable evolve : state -> pdf state.

  (* The type of measurements of the system. *)
  Variable measurement : Type.
  (* Given the current state, this gives the distribution
     over possible measurements. If the current state is
     s, then the next measurement will be a sample
     from measure s. *)
  Variable measure : state -> pdf measurement.


  (****************************************************)
  (* The following is a specification of the optimal  *)
  (* sensor fusion algorithm, i.e. recursive Bayesian *)
  (* estimation.                                      *)
  (****************************************************)

  (* This part of estimation takes a previously computed
     pdf for the state and computes a new pdf for the
     state that takes into account the dynamics of the
     system (evolve) since the last time estimation
     was run. It assumes that no new measurements have
     arrived. *)
  Definition predict (pre : pdf state) : pdf state :=
    fun x' =>
      Lebesgue_int (fun x => evolve x x' * pre x)
                   (fun _ => True).

  (* This part of estimation takes a previously computed
     pdf for the state and computes a new pdf for the
     state that takes into account a new measurement
     but assumes that no time has elapsed. *)
  Definition update (pre : pdf state) (y : measurement)
    : pdf state :=
    fun x =>
      (measure x y * pre x)/
      (Lebesgue_int (fun x => measure x y * pre x)
                    (fun _ => True)).

  (* Finally we put together predict and update
     to form estimation, i.e. sensor fusion. *)
  Definition estimate (pre : pdf state) (y : measurement)
    : pdf state :=
    update (predict pre) y.

End RecursiveBayesian.
