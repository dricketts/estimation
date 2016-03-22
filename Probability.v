Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.

(* Probability density function *)
Definition pdf (T : Type) : Type := T -> nonnegreal.

(* Conditional probability density function *)
Definition c_pdf (T U : Type) : Type :=
  T -> U -> nonnegreal.

Section RecursiveBayesian.

  Definition state := R.
  Definition measurement := R.
  Definition measurement_noise := R.
  Variable measurement_noise_pdf : pdf measurement_noise.

  Variable evolve_pdf : c_pdf state state.
  Variable measure :
    state -> measurement_noise -> measurement.

  (* Need to integrate over all R. The standard library
     and Coqlicuet do not contain such a definition.
     May need Lebesque integral. *)
  Definition predict
             (pre post : c_pdf state (list measurement)) :
    Prop :=
    forall x' Y,
      integrate (fun x => evolve_pdf x' x * pre x Y)
                post x' Y.

End RecursiveBayesian.