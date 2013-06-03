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

include "dataflow/RDan.ma".

definition killVB ≝ killAE.

definition genVB ≝ λS:stm.λl.
  match get_lth S l with
    [ aassign n x a ⇒ AExp_a a 
    | abval l b ⇒ AExp_b b 
    | _ ⇒ [ ]].
    
definition VB_top ≝ AE_top.

definition VB ≝ λS. mk_framework false true expr [] expr_e killVB  genVB false S .

definition VB_step ≝ λs,state. F_step ? s state VB.
definition approx_VB ≝ λn,soft. approx_F ? VB_top n soft VB.

(*
definition profe_1 ≝ se (vA ≥ vB) allora 
                          (aZ <- vB - vA \jj
                           (aY <- vA - vB)) 
                    altri (aZ <- vA - vB \jj
                           (aY <- vB - vA )) .

example vbt: approx_VB 4 profe_1 =?. normalize // qed.
*)
