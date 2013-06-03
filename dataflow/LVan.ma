(*
    Giacomo Bergami (c) 2013


    This file is part of Matita Dataflow Library.

    Matita Dataflow Library is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Matita Dataflow Library is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Matita Dataflow Library.  If not, see <http://www.gnu.org/licenses/>.
*)

include "dataflow/VBEan.ma".

definition killLV ≝ λS:stm.λl. 
  match get_lth S l with
    [ aassign n var val ⇒ [var]
    | _ ⇒ []].

definition genLV ≝ λS:stm.λl.
  match get_lth S l with
    [ aassign n x a ⇒ FVe a
    | abval x y ⇒ FVb y
    | _ ⇒ [ ]].

definition LV ≝ λS. mk_framework false false (ℕ) (FV (stmc S)) eqb killLV  genLV true S .


definition LV_bot ≝ λS. make_bot (ℕ) S.
definition LV_step ≝ λs,state. F_step ? s state LV.
definition approx_LV ≝ λn,soft. approx_F ? LV_bot n soft LV.

(*
definition profe_2 ≝ aX <- Nat 2 \jj(
                     aY <- Nat 4 \jj(
                     aX <- Nat 1 \jj((
                     se (vY ≥ vX) allora aZ <- vY altri aZ <- (vY * vY)) \jj(
                     aX <- vZ
                     )))).

example labels_TestLV: (stmc profe_2 )=?. normalize // qed.
example flow_TestLV: flow profe_2=?.  normalize // qed.

example lvt: approx_LV 8 profe_2 =?. normalize // qed.
*)
