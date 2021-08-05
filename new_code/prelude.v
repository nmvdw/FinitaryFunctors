(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(** The empty hSet *)
Definition emptyset
  : hSet
  := make_hSet empty isasetempty.
