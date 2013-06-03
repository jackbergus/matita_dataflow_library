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

include "arithmetics/nat.ma".
include "basics/bool.ma".
include "basics/lists/list.ma".

let rec memf (A:Type[0]) (f:A→A→bool) (l: list A) (n:A) on l≝ 
  match l with
  [ nil ⇒ false
  | cons a b ⇒ if (f a n) then true else memf A f b n ].
  
let rec intersect (A:Type[0]) (f:A→A→bool) l m on l ≝ 
  match l with
  [ nil ⇒ nil ? 
  | cons a b ⇒ if (memf A f m a) then a::(intersect A f b m) else (intersect A f b m)].

let rec union (A:Type[0]) f l cup on l ≝ 
  match l with
  [ nil ⇒ cup
  | cons a b ⇒ if (memf A f cup a) then (union A f b cup) else a::(union A f b cup)].

let rec meta_funb (A:Type[0]) (f:A→A→bool) (acc: list A) (l: list (list A)) (fun: (list A)→(list A)→(list A)) on l ≝
  match l with 
  [ nil ⇒ nil ?
  | cons a b ⇒ if eqb (length ? (hd ? b [])) 0 then 
                  fun acc a
               else 
                  meta_funb A f (intersect A f a acc) b fun ].

definition meta_fun ≝λA,f,l,fun.
if (eqb (length (list A) l) 1) then 
    (hd (list A) l []) 
else 
    meta_funb A f (hd (list A) l []) (tail (list A) l) fun. 


definition Intersect ≝ λA,f,l. meta_fun A f l (intersect A f).
definition Union ≝λA,f,l. meta_fun A f l (union A f).

let rec difference (A:Type[0]) f l diff on l≝
  match l with
  [ nil ⇒ nil ?
  | cons a b ⇒  if memf A f diff a then (difference A f b diff) else a::(difference A f b diff)].

(*
inductive sign : Type[0] ≝ min : sign | eqs : sign | mag : sign.
definition sign_e ≝ λ x,y. match x with
    [ min ⇒ match y with [ min ⇒ true | _ ⇒ false]
    | eqs ⇒ match y with [ eqs ⇒ true | _ ⇒ false]
    | mag ⇒ match y with [ mag ⇒ true | _ ⇒ false]].

let rec cmp_sign a b  ≝ 
  match a with
  [ O ⇒ match b with [ O ⇒ eqs | _ ⇒ min]
  | S x ⇒ match b with [ S y ⇒ (cmp_sign x y) | _ ⇒ mag]].
  
let rec leq_cpnat a b  ≝
  andb 
  (leq_nat (fst nat nat a) (fst nat nat b))
  (leq_nat (snd nat nat a) (snd nat nat b)).

let rec insert A (l:list A) cmp e on l ≝ 
  match l with
    [ nil ⇒ [e]
    | cons h t ⇒ if (cmp e h) then e :: l else h :: (insert A t cmp e) ].

let rec sort A (l:list A) cmp on l ≝ 
  match l with 
    [ nil ⇒ []
    | cons h t ⇒ insert A (sort A t cmp) cmp h ].

example sort_nat: sort nat [0;11;2;9;3;1;2;3;4;3;5;7] eqb =?. normalize
*)
inductive rop: Type[0] ≝ 
  | Ge : rop
  | Le : rop.  

definition rop_e ≝ λx,y.
  match x with
  [ Ge ⇒ match y with [ Ge ⇒ true | _ ⇒ false ]
  | Le ⇒ match y with [ Le ⇒ true | _ ⇒ false ]].

inductive aop: Type[0] ≝
  | sum : aop
  | dif : aop
  | tim : aop.

definition aop_e ≝ λx,y.
  match x with
  [ sum ⇒ match y with [ sum ⇒ true | _ ⇒ false]
  | dif ⇒ match y with [ dif ⇒ true | _ ⇒ false]
  | tim ⇒ match y with [ tim ⇒ true | _ ⇒ false]].

inductive bop: Type[0] ≝ 
  | aand : bop
  | oor : bop.

definition bop_e ≝ λx,y. 
  match x with 
  [ aand ⇒ match y with [ aand ⇒ true | _ ⇒ false]
  | oor ⇒ match y with [ oor ⇒ true | _ ⇒ false]].

inductive expr : Type[0] ≝
  | Var : nat → expr
  | Nat : nat → expr
  | Val : expr → aop → expr → expr.
  
let rec expr_e x y ≝ 
  match x with
  [ Var a ⇒ match y with [ Var c ⇒ eqb a c | _ ⇒ false]
  | Nat a ⇒ match y with [ Var c ⇒ eqb a c | _ ⇒ false]
  | Val a b c ⇒ match y with [Val d e f ⇒ (andb (expr_e a d) (andb (expr_e c f) (aop_e b e))) | _ ⇒ false]].

inductive bexpr : Type[0] ≝ 
  | tt : bexpr
  | ff : bexpr
  | Not : bexpr → bexpr
  | BVal : bexpr → bop → bexpr → bexpr
  | AVal : expr → rop → expr → bexpr.

let rec bexpr_e x y ≝ 
match x with
  [ tt ⇒ match y with [ tt ⇒ true | _ ⇒ false]
  | ff ⇒ match y with [ ff ⇒ true | _ ⇒ false]
  | Not a ⇒ match y with [ Not b ⇒ bexpr_e a b | _ ⇒ false]
  | BVal a b c ⇒ match y with [ BVal d e f ⇒ (andb (bexpr_e a d) (andb (bop_e b e) (bexpr_e c f))) | _ ⇒ false]
  | AVal a b c ⇒ match y with [ AVal d e f ⇒ (andb (expr_e a d) (andb (rop_e b e) (expr_e c f))) | _ ⇒ false]].
  
notation "hvbox(⊤)"
  with precedence 47 for @{tt}.

notation "hvbox(⊥)"
  with precedence 46 for @{ff}.

inductive stm : Type[0] ≝ 
  | assign : nat → expr → stm
  | dskip : stm
  | concat : stm → stm → stm
  | ifte  : bexpr → stm → stm → stm
  | while : bexpr → stm → stm.

inductive idxstm : Type[0] ≝ 
  | iassign : nat → nat → expr → idxstm
  | idskip : nat → idxstm
  | iconcat : idxstm → idxstm → idxstm
  | iifte  : nat → bexpr → idxstm → idxstm → idxstm
  | iwhile : nat → bexpr → idxstm → idxstm.

(* XXX
notation > "'While' term 45 e 'do' term 45 t 'done'" non associative with precedence 45
 for @{ while $e $t  }.
notation < "hvbox('While' \nbsp term 45 e  \nbsp 'do' \nbsp term 48 f  \nbsp 'done')" non associative with precedence 45
 for @{ while $e $f }.

notation > "'se' term 45 e 'allora' term 45 t 'altri' term 45 f \nbsp" non associative with precedence 45
 for @{ ifte $e $t $f  }.
notation < "hvbox('se' \nbsp  term 45 e  \nbsp 'allora' \nbsp term 45 t  \nbsp 'altri' \nbsp term 45 f \nbsp)" non associative with precedence 45
 for @{ ifte $e $t $f }.

notation > "hvbox(c1 break \jj c2)"
  left associative with precedence 45 for @{concat $c1 $c2}.
notation < "hvbox(c1 break ; c2)"
  left associative with precedence 45 for @{concat $c1 $c2}.
  
notation "hvbox(var break <- val)"
  left associative with precedence 45 for @{assign $var $val}.
*)
notation > "'While' term 45 e 'do' term 45 t 'done'" non associative with precedence 45
 for @{ while $e $t  }.
notation < "hvbox('While' \nbsp term 45 e  \nbsp 'do' \nbsp term 48 f  \nbsp 'done')" non associative with precedence 45
 for @{ while $e $f }.

notation > "'se' term 45 e 'allora' term 45 t 'altri' term 45 f" non associative with precedence 45
 for @{ ifte $e $t $f  }.
notation < "hvbox('se' \nbsp  term 45 e  \nbsp 'allora' \nbsp term 45 t  \nbsp 'altri' \nbsp term 45 f)" non associative with precedence 45
 for @{ ifte $e $t $f }.

notation > "hvbox(c1 break \jj c2)"
  left associative with precedence 45 for @{concat $c1 $c2}.
notation < "hvbox(c1 break ; c2)"
  left associative with precedence 45 for @{concat $c1 $c2}.
  
notation "hvbox(var break <- val)"
  left associative with precedence 45 for @{assign $var $val}.

let rec depth s ≝ match s with
  [ assign a b ⇒ 0
  | dskip      ⇒ 0
  | concat a b ⇒ 1+(depth a)+(depth b)
  | ifte a b c ⇒ 2+(depth b)+(depth c)
  | while a b  ⇒ 1+(depth b)].

let rec stm_to_idx_list n s on s:  idxstm ≝match s with
  [ assign a b ⇒ iassign n a b
  | dskip      ⇒ idskip   n
  | concat a b ⇒ iconcat  (stm_to_idx_list ( n) a) (stm_to_idx_list ( (S (depth a))+n) b)
  | ifte a b c ⇒ iifte    n a (stm_to_idx_list (S (n)) b) (stm_to_idx_list ((S (S (depth b)))+n) c)
  | while a b  ⇒ iwhile   n a (stm_to_idx_list (S n) b)].


definition stmc ≝ λs.    stm_to_idx_list 0 s.

(*
notation > "'While'⌊ term 45 e ⌋^(term 45 l) 'do' term 45 t 'done'" non associative with precedence 45
 for @{ iwhile $l $e $t  }.


notation > "⌊'se' term 45 e 'allora' term 45 t 'altri' term 45 f⌋^(term 45 l)" non associative with precedence 45
 for @{ iifte $l $e $t $f  }.


notation > "hvbox(c1 break \jj c2)"
  non associative with precedence 45 for @{iconcat  $c1 $c2}.




notation "'While' \nbsp ⌊ term 45 e ⌋^(term 45 l) \nbsp 'do' break \nbsp  f  break \nbsp 'done'" non associative with precedence 45
 for @{ iwhile $l $e $f }.
notation  "hvbox('se' ⌊\nbsp  term 45 e ⌋^(term 45 l) \nbsp 'allora' \nbsp term 45 t  \nbsp 'altri' \nbsp term 45 f ';;' )" non associative with precedence 45
 for @{ iifte $l $e $t $f }.
notation  "hvbox(c1 break ;; c2)"
  non associative with precedence 44 for @{iconcat  $c1 $c2}.
notation  "hvbox(⌊var break <- val⌋^(term 45 l))"
  non associative with precedence 43 for @{iassign $l $var $val}.
*)
(*
notation > "'While'⌊ term 45 e ⌋^(term 45 l) 'do' term 45 t 'done'" non associative with precedence 45
 for @{ iwhile $l $e $t  }.


notation < "'While' \nbsp ⌊ term 45 e ⌋^(term 45 l) \nbsp 'do' \nbsp term 48 f  \nbsp 'done'" non associative with precedence 45
 for @{ iwhile $l $e $f }.
notation < "hvbox('se' ⌊\nbsp  term 45 e  \nbsp⌋^(term 45 l) 'allora' \nbsp term 45 t  \nbsp 'altri' \nbsp term 45 f)" non associative with precedence 45
 for @{ iifte $l $e $t $f }. *)

notation > "hvbox(c1 break \jj c2)"
  non associative with precedence 45 for @{iconcat  $c1 $c2}.
notation < "hvbox(c1 break ;; c2)"
  non associative with precedence 45 for @{iconcat  $c1 $c2}.

notation "hvbox(⌊var break <- val⌋^(term 45 l))"
  non associative with precedence 45 for @{iassign $l $var $val}.

example ex: stmc  ((5<- Nat 2) \jj (6 <- Nat 3)\jj While ⊤ do 6<- Nat 3 done)=?.
normalize // qed.

interpretation "Aexp plus" 'plus x y = (Val x sum y).
interpretation "Aexp minus" 'minus x y = (Val x dif y).
interpretation "Aexp times" 'times x y = (Val x tim y).
interpretation "Bexp not" 'not x = (Not x).
interpretation "Bexp and" 'and x y = (BVal x aand y).
interpretation "Bexp or" 'or x y = (BVal x oor y).
interpretation "Bexp 'less or equal to'" 'leq x y = (AVal x Le y).
interpretation "Bexp 'less or equal to'" 'geq x y = (AVal x Ge y).


inductive asset: Type[0] ≝
  | aassign : nat → nat → expr → asset
  | abval   : nat → bexpr → asset
  | askip   : nat → asset.

definition get_label_of_asset ≝ λx. 
  match x with
  [ aassign n _ _ ⇒ n
  | abval n _ ⇒ n
  | askip n ⇒ n].
  
  
  
let rec asset_e a b ≝ match a with
  [ aassign x y z ⇒ match b with
                    [ aassign g h i ⇒ (andb (eqb x g) (andb (eqb y h) (expr_e z i))) 
                    | _ ⇒ false]
  | abval x y ⇒ match b with 
                    [ abval c d ⇒ (andb (eqb x c) (bexpr_e y d))
                    | _ ⇒ false]
  | askip x ⇒ match b with
                    [ askip y ⇒ eqb x y
                    | _ ⇒ false]]. 

(*
notation "hvbox(⌈var break <- val⌉^(term 45 l))"
  non associative with precedence 45 for @{aassign $l $var $val}.

notation "hvbox(⌈b⌉^(term 45 l))"
  non associative with precedence 45 for @{abval $l $b}.

notation "hvbox(⌈b⌉)"
  non associative with precedence 45 for @{askip $b}.
*)

let rec iinit s ≝ match s with
[ iassign n a b ⇒ n
| idskip  n     ⇒ n
| iconcat a b   ⇒ iinit a
| iifte n a b c ⇒ n
| iwhile n a b  ⇒ n].

definition init ≝ λs. iinit (stmc s).

let rec ffinal s ≝ match s with
[ iassign n a b ⇒ [n]
| idskip n ⇒ [n]
| iconcat a b ⇒ ffinal b
| iifte n a b c ⇒ union nat eqb (ffinal b) (ffinal c)
| iwhile n a b ⇒ [n]].

definition final ≝ λs. ffinal (stmc s).

let rec bblocks s ≝ 
match s with
[ iassign n a b ⇒ [aassign n a b]
| idskip  n     ⇒ [askip n ]
| iconcat a b ⇒ union ? asset_e (bblocks a) (bblocks b)
| iifte n a b c ⇒ union ? asset_e [(abval n a)] (union ? asset_e (bblocks b) (bblocks c))
| iwhile n a b  ⇒ union ? asset_e [(abval n a)] (bblocks b)].

definition blocks ≝ λs. bblocks (stmc s).

(* XXX: Se io restituisco un qualsiasi askip, viene comunque ignorato sia
   nel calcolo dell'AEkill sia in AEgen *)
let rec  get_lth_of_list ls l ≝ 
  match ls with
  [ nil ⇒ askip 99
  | cons a b ⇒ if (eqb (get_label_of_asset a) l) then a else get_lth_of_list b l].
definition get_lth ≝ λs,l. get_lth_of_list (blocks s) l.
definition get_blth ≝ λs,l. get_lth_of_list (bblocks s) l.
(*
example ex: blocks  (stmc  ((5<- Nat 2); (6 <- Nat 3); While ⊤ do 6<- Nat 3 done))=?.
normalize
*)

definition llabels ≝λs. map ?? (λx. match x with [ aassign n a b ⇒ n | abval n b ⇒ n | askip n ⇒ n]) s.

definition labels ≝ λs. llabels (blocks s).

(* Funzione delle coppie di flusso *)
let rec fflow s : list (nat×nat) ≝ 
match s with
[ iassign n a b ⇒ [ ]
| idskip n ⇒  [ ]
| iconcat a b ⇒ (fflow a)@(fflow b)@(map ?? (λx. 〈x,iinit b〉)  (ffinal a))
| iifte n a b c ⇒ (fflow b)@(fflow c)@(cons ? 〈n,iinit b〉 (cons ? 〈n, iinit c〉 (nil ?)))
| iwhile n a b ⇒ (fflow b)@[〈n,iinit b〉]@(map ?? (λx. 〈x,n〉) (ffinal b))].

definition flow ≝ λs. fflow (stmc s).

definition fflowR ≝ λs. map ?? (λx. match x with [mk_Prod a b ⇒ mk_Prod ?? b a]) (flow s).

let rec FVe e ≝ match e with
[ Var n ⇒ [n]
| Nat n ⇒ [ ]
| Val a b c ⇒ union nat eqb  (FVe a) (FVe c)].

let rec FVb e ≝ match e with
  [ tt ⇒ []
  | ff ⇒ []
  | Not e ⇒ FVb e
  | BVal a b c ⇒  union nat eqb  (FVb a) (FVb c)
  | AVal a b c ⇒  union nat eqb (FVe a) (FVe c)].

(* Ottiene tutte le variabili presenti nel codice *)
let rec FV s ≝  match s with
[ iassign n a b ⇒ union nat eqb [a] (FVe b)
| idskip n ⇒ [ ]
| iconcat a b ⇒ union nat eqb (FV a) (FV b)
| iifte n a b c ⇒ union nat eqb (FVb a) (union nat eqb (FV b) (FV c))
| iwhile n a b ⇒ union nat eqb (FVb a) (FV b)].


let rec AExp_a e ≝ match e with
[ Var n ⇒ [ ]
| Nat n ⇒ [ ]
| Val a b c ⇒ union expr expr_e [e] (union expr expr_e  (AExp_a a) (AExp_a c))].

let rec AExp_b e ≝ match e with
  [ tt ⇒ []
  | ff ⇒ []
  | Not u ⇒ []
  | BVal a b c ⇒  union expr expr_e (AExp_b a) (AExp_b c)
  | AVal a b c ⇒  union expr expr_e  (AExp_a a) (AExp_a c)].

(* Ottiene tutte le espressioni presenti nel codice *)
let rec AExp s ≝  match s with
[ iassign n a b ⇒ (AExp_a b)
| idskip n ⇒ [ ]
| iconcat a b ⇒ union expr expr_e (AExp a) (AExp b)
| iifte n a b c ⇒ union expr expr_e(AExp_b a)( union expr expr_e (AExp b) (AExp c))
| iwhile n a b ⇒ union expr expr_e (AExp_b a) (AExp b)].

