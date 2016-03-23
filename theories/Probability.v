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

(********************************************************)
(* The following section specifies the recursive        *)
(*  Bayesian estimator. It is parameterized by a        *)
(* specification of the dynamics of the system (evolve) *)
(* and a specification of the noisiness of the          *)
(* sensor(s) (measure).                                 *)
(********************************************************)
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
  (* estimation. The function estimate is the full    *)
  (* sensor fusion algorithm. The functions predict   *)
  (* and update are subparts of the algorithm         *)
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

(******************************************************)
(* The following is a specification of Gregory's      *)
(* coin flip system, along with a sensor that noisily *)
(* measures the coin. These definitions would be used *)
(* to instantiate state, evolve, measurement, and     *)
(* measure in the above section.                      *)
(******************************************************)
(* Our state is a single coin. *)
Definition state := bool.
(* This is a weird coin because coin flips depend on the
   previous coin flip. *)
Definition evolve (pre : state) : pdf state :=
  fun post =>
    if pre
    then if post then /2 else /2
    else if post then /3 else 2/3.

(* Our sensor measures the coin. *)
Definition measurement := bool.
(* Our sensor measures more accurately if the coin is true
   than if it is false. This might model the fact that
   the sensor is a camera, and the heads side of the coin
   has more contrast than the tails side. *)
Definition measure (pre : state) : pdf measurement :=
  fun y =>
    if pre
    then if y then 4/5 else 1/5
    else if y then 2/5 else 3/5.

(* Gregory's example also attempted to separately model
   the fact that a sensor might, in addition to a
   measurement, also return a confidence. For example,
   the coin camera might return the fact that the camera
   was slightly obscured, or a GPS sensor might return
   the number of satellites. This does not need a separate
   model - all of this information is captured in the
   function measure. In other words, at each time step,
   the sensor passes to the estimate function (aka the
   sensor fusion algorithm) a measurement *and* the
   function measure from which that measurement was sampled.
   The function measure captures the confidence of the
   most recent measurement and might change over time
   (for example, as more satellites are acquired. *)