(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat poly.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import realalg complex fingroup perm.
From mathcomp.analysis Require Import forms.
Require Import ssr_ext euclidean angle vec_angle frame rot quaternion.

(******************************************************************************)
(*                            Octonions                                       *)
(*                                                                            *)
(* This file develops the theory of quaternions. It defines the type of       *)
(* octonions and that octionions form a ZmodType and a LmodType. It also      *)
(* defines the multiple that is neither commutative nor associative           *)
(*                                                                            *)
(*       oct R == type of octonions over the ringType R                       *)
(*         x.1 == left part of the octonion x                                 *)
(*         x.2 == right part of the octonion x                                *)
(*        x^*o == conjugate of octonion x                                     *)
(*      x *o y == product of two octonions                                    *)
(* x \is realo == x is a real ie only the real part of the left quaternion    *)
(*                is not zero                                                 *)
(*      normo x == the norm of the octonion                                   *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x %:ol" (at level 2, format "x %:ol").
Reserved Notation "x %:or" (at level 2, format "x %:or").
Reserved Notation "x '^*o'" (at level 2, format "x '^*o'").
Reserved Notation "a *o b" (at level 40, left associativity, format "a  *o  b").

Declare Scope oct_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section octonion0.
Variable R : ringType.

Record oct := mkOct {octl : quat R ; octr : quat R }.

Local Notation "x %:ol" := (mkOct x%quat 0).
Local Notation "x %:or" := (mkOct 0 x%quat).

Coercion pair_of_oct (a : oct) := let: mkOct a0 a1 := a in (a0, a1).
Let oct_of_pair (x : quat R * quat R) :=
  let: (x0, x1) := x in mkOct x0 x1.

Lemma oct_of_pairK : cancel pair_of_oct oct_of_pair.
Proof. by case. Qed.

Definition oct_eqMixin := CanEqMixin oct_of_pairK.
Canonical Structure oct_eqType := EqType oct oct_eqMixin.
Definition oct_choiceMixin := CanChoiceMixin oct_of_pairK.
Canonical Structure oct_choiceType := ChoiceType oct oct_choiceMixin.

Lemma eq_oct (a b : oct) : (a == b) = (a.1 == b.1) && (a.2 == b.2).
Proof.
case: a b => [a0 a1] [b0 b1] /=.
apply/idP/idP => [/eqP [ -> ->]|/andP[/eqP -> /eqP -> //]]; by rewrite !eqxx.
Qed.

Definition addo (a b : oct) := nosimpl (mkOct (a.1 + b.1) (a.2 + b.2)).

Lemma addoC : commutative addo.
Proof. move=> *; congr mkOct; by rewrite addrC. Qed.

Lemma addoA : associative addo.
Proof. move=> *; congr mkOct; by rewrite addrA. Qed.

Lemma add0o : left_id 0%:ol addo.
Proof. case=> *; by rewrite /addo /= 2!add0r. Qed.

Definition oppo (a : oct) := nosimpl (mkOct (- a.1) (- a.2)).

Lemma addNo : left_inverse 0%:ol oppo addo.
Proof. move=> *; congr mkOct; by rewrite addNr. Qed.

Definition oct_ZmodMixin := ZmodMixin addoA addoC add0o addNo.
Canonical oct_ZmodType := ZmodType oct oct_ZmodMixin.

Lemma addoE (a b : oct) : a + b = addo a b. Proof. done. Qed.

Lemma oppoE (a : oct) : - a = oppo a. Proof. done. Qed.

Lemma octE (a : oct) : a = (a.1)%:ol + (a.2)%:or.
Proof. by apply/eqP; rewrite eq_oct /= !(add0r,addr0) !eqxx. Qed.

Lemma oct_leftE (a b : quat R) : (a%:ol == b%:ol) = (a == b).
Proof. by apply/idP/idP => [/eqP[] ->|/eqP -> //]. Qed.

Lemma oct_leftN (x: quat R) : (-x)%:ol = -(x%:ol).
Proof. by rewrite oppoE /oppo /= oppr0. Qed.

Lemma oct_rightN (x: quat R) : (-x)%:or = -(x%:or).
Proof. by rewrite oppoE /oppo /= oppr0. Qed.

Lemma oct_leftD (x y : quat R) : (x + y)%:ol = x%:ol + y%:ol.
Proof. by rewrite addoE /addo /= add0r. Qed.

Lemma oct_rightD (x y : quat R) : (x + y)%:or = x%:or + y%:or.
Proof. by rewrite addoE /addo /= addr0. Qed.

Lemma oct_leftB (x y : quat R) : (x - y)%:ol = x%:ol - y%:ol.
Proof. by rewrite oct_leftD oct_leftN. Qed.

Lemma oct_rightB (x y : quat R) : (x - y)%:or = x%:or - y%:or.
Proof. by rewrite oct_rightD oct_rightN. Qed.

End octonion0.

Delimit Scope oct_scope with oct.
Local Open Scope oct_scope.

Notation "x %:or" := (mkOct 0 x) : oct_scope.
Notation "x %:ol" := (mkOct x 0) : oct_scope.

Section octonion.

Variable R : comRingType.

Definition mulo (a b : oct R) := nosimpl
  (mkOct (a.1 * b.1 - ((b.2)^*q)%quat * a.2) 
         (b.2 * a.1 + a.2 * ((b.1)^*q)%quat)).

Lemma mulo1 : right_id 1%:ol mulo.
Proof.
by case=> a a'; rewrite /mulo /= !quat_realC !mul0r !mulr1 subr0 add0r.
Qed.

Lemma mul1o : left_id 1%:ol mulo.
Proof.
by case=> a a'; rewrite /mulo /=; congr mkOct; Simp.r => /=.
Qed.

Lemma mulor1 : right_id 1%:ol mulo.
Proof.
case=> a a'; rewrite /mulo /=; congr mkOct.
  by rewrite linear0 mul0r subr0 mulr1.
by rewrite quat_realC mulr1 mul0r add0r.
Qed.

Lemma mulo1r : left_id 1%:ol mulo.
Proof.
case=> a a'; rewrite /mulo /=; congr mkOct.
  by rewrite mulr0 subr0 mul1r.
by rewrite mulr1 mul0r addr0.
Qed.

Lemma mulo0r : left_zero 0%:ol mulo.
Proof.
case=> a a'; rewrite /mulo /=; congr mkOct.
  by rewrite mul0r mulr0 subrr.
by rewrite mul0r mulr0 addr0.
Qed.

Lemma mulor0 : right_zero 0%:ol mulo.
Proof.
case=> a a'; rewrite /mulo /=; congr mkOct.
  by rewrite linear0 mul0r mulr0 subrr.
by rewrite linear0 mul0r mulr0 addr0.
Qed.

Lemma muloDl : left_distributive mulo +%R.
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulo /=; congr mkOct => /=.
  rewrite !(mulrDl, mulrDr) -!addrA; congr (_ + _).
  by rewrite addrCA opprD.
rewrite !(mulrDl, mulrDr) -!addrA; apply: f_equal2; first by [].
by rewrite addrCA.
Qed.

Lemma muloDr : right_distributive mulo (+%R).
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulo /=; congr mkOct => /=.
  rewrite !(mulrDl, mulrDr, linearD) /= -!addrA; congr (_ + _).
  by rewrite addrCA.
rewrite !(mulrDl, mulrDr, linearD) /= -!addrA; apply: f_equal2; first by [].
by rewrite addrCA.
Qed.

Lemma oneq_neq0 : 1%:ol != 0 :> oct R.
Proof. apply/eqP => -[]; apply/eqP. exact: oner_neq0. Qed.

Notation "a *o b" := (mulo a b).

Lemma muloNl (x y : oct R) : (- x) *o y = - (x *o y).
Proof.
case: x => [x1 x2]; case: y => [y1 y2]; congr mkOct => /=.
  by rewrite opprD !mulrN !mulNr.
by rewrite opprD !mulrN !mulNr.
Qed.

Lemma muloNr (x y : oct R) : x *o (- y) = - (x *o y).
Proof.
case: x => [x1 x2]; case: y => [y1 y2]; congr mkOct => /=.
  by rewrite linearN /= opprD !mulrN !mulNr.
by rewrite linearN /= opprD !mulrN !mulNr.
Qed.

Lemma muloBl x y z : (x - y) *o z = x *o z - y *o z.
Proof. by rewrite muloDl muloNl. Qed.

Lemma muloBr x y z : z *o (x - y) = z *o x - z *o y.
Proof. by rewrite muloDr muloNr. Qed.

(* Alternative algebra *)

Lemma muloAlt1 a b : (a *o a) *o  b = a *o (a *o b).
Proof.
case: a => [a0 a1]; case: b => [b0 b1]; apply: (f_equal2 (@mkOct _)) => /=;
    rewrite !{1}(mulrBr, mulrDr, mulrBl, mulrDl, mulrA, linearD) /= 
              !{1}conjqM ?{1}conjqI !{1}addrA.
  rewrite -!{1}addrA; apply: f_equal2; first by []. (* congr take time *)
  rewrite addrC !addrA; apply: f_equal2; last first. 
    by rewrite realq_comm ?mulrA // conjq_comm realq_conjM.
  by rewrite -opprD -mulrDr -realq_comm ?realq_conjD // mulrDl opprD !mulrA.
rewrite -!addrA linearN /= !conjqM !conjqI !mulrN !mulrA; congr (_ + _).
rewrite -mulrA conjq_comm -[b1 * _]realq_comm ?realq_conjM //.
rewrite addrC !addrA; apply: f_equal2; last by [].
by rewrite -!mulrDl -!mulrDr -mulrA (realq_comm _ (realq_conjD _)) mulrA.
Qed.

Lemma muloAlt2 a b : (a *o b) *o a = a *o (b *o a).
Proof.
case: a => [a0 a1]; case: b => [b0 b1]; apply: (f_equal2 (@mkOct _)) => /=;
    rewrite !(mulrBr, mulrDr, mulrBl, mulrDl, mulrA, linearD) /= 
              !conjqM ?conjqI !addrA.
  rewrite [RHS]addrC !{1}addrA; apply: f_equal2; last first.
    by rewrite conjq_comm (realq_comm _ (realq_conjM _)) -conjq_comm mulrA.
  rewrite [X in _ = X - _]addrC -!{1}addrA; apply: f_equal2; first by [].
  rewrite -!opprD -mulrDl realq_comm ?mulrDr ?mulrA //.
  by rewrite -{2}[b1]conjqI -conjqM realq_conjD. 
rewrite -!addrA linearN /= !conjqM !conjqI !mulrN !mulrA {1}addrA.
rewrite [X in X + _ = _]addrC !{1}addrA [RHS]addrC -!{1}addrA.
apply: f_equal2; first by [].
rewrite [LHS]addrC [RHS]addrC -!{1}addrA; congr (_ + _).
  by rewrite -mulrA -conjq_comm mulrA.
rewrite -2!{1}mulrA -mulrDr -conjqM -2!{1}mulrA -mulrDr.
by rewrite addrC conjq_addMC addrC conjqM.
Qed.

Local Notation "`il" := (`i%quat)%:ol.
Local Notation "`ir" := (`i%quat)%:or.
Local Notation "`jl" := (`j%quat)%:ol.
Local Notation "`jr" := (`j%quat)%:or.
Local Notation "`kl" := (`k%quat)%:ol.
Local Notation "`kr" := (`k%quat)%:or.

Lemma oct_leftM (x y : quat R) : (x * y)%:ol = x%:ol *o y%:ol.
Proof. by congr mkOct; rewrite ?(linear0, mul0r, addr0). Qed.

Lemma ililN1 : `il *o `il = - 1%:ol.
Proof. by rewrite -oct_leftM iiN1 oct_leftN. Qed.

Lemma irirN1 : `ir *o `ir = - 1%:ol.
Proof.
congr mkOct; rewrite /= !(conjqI, linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr iiN1 opprK.
Qed.

Lemma ilirN1 : `il *o `ir = - 1%:or.
Proof.
by congr mkOct; rewrite /= !(iiN1, linear0, mul0r, mulr0, add0r, addr0).
Qed.

Lemma iril1 : `ir *o `il = 1%:or.
Proof. 
congr mkOct; rewrite /= !(iiN1, linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN iiN1 opprK.
Qed.

Lemma iljlkl : `il *o `jl = `kl.
Proof. by rewrite -oct_leftM ijk. Qed.

Lemma irjrkl : `ir *o `jr = - `kl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr jiNk opprK.
Qed.

Lemma iljrkl : `il *o `jr = - `kr.
Proof.
by congr mkOct; rewrite /= !(linear0, jiNk, mul0r, mulr0, add0r, addr0).
Qed.

Lemma irjlkl : `ir *o `jl = - `kr.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN ijk.
Qed.

Lemma ilklNjl : `il *o `kl = - `jl.
Proof. by rewrite -oct_leftM ikNj oct_leftN. Qed.

Lemma irkrNjl : `ir *o `kr = `jl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr kij opprK.
Qed.

Lemma ilkrNjl : `il *o `kr = `jr.
Proof.
by congr mkOct; rewrite /= !(linear0, kij, mul0r, mulr0, add0r, addr0).
Qed.

Lemma irklNjl : `ir *o `kl = `jr.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN ikNj opprK.
Qed.

Lemma ilorir : `il *o (1%:or) = `ir.
Proof.
by congr mkOct; rewrite /= !(linear0, mul0r, mulr0, mul1r, add0r, addr0).
Qed.

Lemma orilNir : (1%:or) *o `il = - `ir.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mul1r.
Qed.

Lemma irorNil : `ir *o (1%:or) = -`il.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_realC mul1r.
Qed.

Lemma oriril : (1%:or) *o `ir = `il.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulr1 opprK.
Qed.

Lemma jlilNkl : `jl *o `il = - `kl.
Proof. by rewrite -oct_leftM jiNk oct_leftN. Qed.

Lemma jrirNkl : `jr *o `ir = `kl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr ijk opprK.
Qed.

Lemma jlirNkl : `jl *o `ir = `kr.
Proof.
by congr mkOct; rewrite /= !(linear0, ijk, mul0r, mulr0, add0r, addr0).
Qed.

Lemma jrilNkl : `jr *o `il = `kr.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN jiNk opprK.
Qed.

Lemma jljlN1 : `jl *o `jl = - 1%:ol.
Proof. by rewrite -oct_leftM jjN1 oct_leftN. Qed.

Lemma jrjrN1 : `jr *o `jr = - 1%:ol.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr jjN1 opprK.
Qed.

Lemma jljrN1 : `jl *o `jr = - 1%:or.
Proof.
by congr mkOct; rewrite /= !(linear0, jjN1, mul0r, mulr0, add0r, addr0).
Qed.

Lemma jrjlN1 : `jr *o `jl = 1%:or.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN jjN1 opprK.
Qed.

Lemma jlklNil : `jl *o `kl = `il.
Proof. by rewrite -oct_leftM jkNi. Qed.

Lemma jrkrNil : `jr *o `kr = - `il.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr kjNi opprK.
Qed.

Lemma jlkrNil : `jl *o `kr = - `ir.
Proof.
by congr mkOct; rewrite /= !(linear0, kjNi, mul0r, mulr0, add0r, addr0).
Qed.

Lemma jrklNil : `jr *o `kl = - `ir.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN jkNi.
Qed.

Lemma jlorjr : `jl *o (1%:or) = `jr.
Proof.
by congr mkOct; rewrite /= !(linear0, mul0r, mulr0, mul1r, add0r, addr0).
Qed.

Lemma orjlNjr : (1%:or) *o `jl = - `jr.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mul1r.
Qed.

Lemma jrorNjl : `jr *o (1%:or) = -`jl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_realC mul1r.
Qed.

Lemma orjrjl : (1%:or) *o `jr = `jl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulr1 opprK.
Qed.

Lemma klilNkl : `kl *o `il = `jl.
Proof. by rewrite -oct_leftM kij. Qed.

Lemma krirNjl : `kr *o `ir = - `jl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr ikNj opprK.
Qed.

Lemma klirNjl : `kl *o `ir = - `jr.
Proof.
by congr mkOct; rewrite /= !(linear0, ikNj, mul0r, mulr0, add0r, addr0).
Qed.

Lemma krilNjl : `kr *o `il = - `jr.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN kij.
Qed.

Lemma kljlNil : `kl *o `jl = - `il.
Proof. by rewrite -oct_leftM kjNi oct_leftN. Qed.

Lemma krjril : `kr *o `jr = `il.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr jkNi opprK.
Qed.

Lemma kljrir : `kl *o `jr = `ir.
Proof.
by congr mkOct; rewrite /= !(linear0, jkNi, mul0r, mulr0, add0r, addr0).
Qed.

Lemma krjlir : `kr *o `jl = `ir.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN kjNi opprK.
Qed.

Lemma klklNor : `kl *o `kl = - 1%:ol.
Proof. by rewrite -oct_leftM kkN1 oct_leftN. Qed.

Lemma krkrNor : `kr *o `kr = - 1%:ol.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulNr kkN1 opprK.
Qed.

Lemma klkrNor : (`k%quat)%:ol *o (`k%quat)%:or = -1%:or.
Proof.
by congr mkOct; rewrite /= !(linear0, kkN1, mul0r, mulr0, add0r, addr0).
Qed.

Lemma krklNor : (`k%quat)%:or *o (`k%quat)%:ol = 1%:or.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulrN kkN1 opprK.
Qed.

Lemma klorkr : `kl *o (1%:or) = `kr.
Proof.
by congr mkOct; rewrite /= !(linear0, mul0r, mulr0, mul1r, add0r, addr0).
Qed.

Lemma orklNir : (1%:or) *o `il = - `ir.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mul1r.
Qed.

Lemma krorNkl : `kr *o (1%:or) = -`kl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_realC mul1r.
Qed.

Lemma orkrkl : (1%:or) *o `kr = `kl.
Proof.
congr mkOct; rewrite /= !(linear0, mul0r, mulr0, add0r, addr0) //.
by rewrite quat_vectC mulr1 opprK.
Qed.

Definition scaleoct k (a : oct R) := mkOct (k *: a.1) (k *: a.2).

Lemma scaleoctA a b w : scaleoct a (scaleoct b w) = scaleoct (a * b) w.
Proof. by rewrite /scaleoct /=; congr mkOct; rewrite scalerA. Qed.

Lemma scaleoct1 : left_id 1 scaleoct.
Proof.
by move=> q; rewrite /scaleoct !scale1r; apply/eqP; rewrite eq_oct /= !eqxx.
Qed.

Lemma scaleoctDr : @right_distributive R (oct R) scaleoct +%R.
Proof. move=> a b c; by rewrite /scaleoct /= !scalerDr. Qed.

Lemma scaleoctDl w : {morph (scaleoct^~ w : R -> oct R) : a b / a + b}.
Proof. by move=> m n; rewrite /scaleoct !scalerDl; congr mkOct. Qed.

Definition oct_lmodMixin := LmodMixin scaleoctA scaleoct1 scaleoctDr scaleoctDl.
Canonical oct_lmodType := Eval hnf in LmodType R (oct R) oct_lmodMixin.

Lemma scaleoctE (k : R) (a : oct R) :
  k *: a = k *: (a .1) %:ol + k *: (a .2) %:or.
Proof. by apply/eqP; rewrite eq_oct //=; Simp.r. Qed.

Lemma oct_leftZ (k : R) (x : quat R) : (k *: x)%:ol = k *: x%:ol.
Proof. by congr mkOct; rewrite scaler0. Qed.

Lemma oct_rightZ (k : R) (x : quat R) : (k *: x)%:or = k *: x%:or.
Proof. by congr mkOct; rewrite scaler0. Qed.

Lemma octAl k (a b : oct R) : k *: (a *o b) = k *: a *o b.
Proof.
case: a b => [a0 a1] [b0 b1]; congr mkOct => /=.
  by rewrite scalerBr quatAl quatAr.
rewrite scalerDr !quatAr; congr (_ + _).
by rewrite -quatAr quatAl.
Qed.

Lemma octAr k (a b : oct R) : k *: (a *o b) = a *o (k *: b).
Proof.
case: a b => [a0 a1] [b0 b1]; congr mkOct => /=.
  by rewrite scalerBr !linearZ /= scalerN -!quatAr -!quatAl.
by rewrite scalerDr !linearZ /= -!quatAr -!quatAl.
Qed.

Definition conjo (a : oct R) :=
  nosimpl (mkOct (a.1 + (a.1)^*q -a.1) (- a.2)).

Local Notation "x '^*o'" := (conjo x).

Lemma conjo_linear : linear conjo.
Proof.
move=> /= k [a0 a1] [b0 b1] /=; rewrite [in LHS]/conjo /= [in RHS]/conjo /=.
congr mkOct => /=; last by rewrite scalerN opprD.
rewrite !(linearD, linearZ) /= !scalerN -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrCA !addrA subrK [_ + b0 + _]addrC addrA addrK addrC.
Qed.

Canonical conjo_is_additive := Additive conjo_linear.
Canonical conjo_is_linear := AddLinear conjo_linear.

Lemma conjoI a : (a^*o)^*o = a.
Proof. 
case: a => a0 a1; congr mkOct => /=; last by rewrite opprK.
by rewrite [a0 + _]addrC addrK conjqI [_ + a0]addrC addrK.
Qed.

Lemma conjo0 : (0%:ol)^*o = 0.
Proof. by congr mkOct; rewrite oppr0 //= linear0 !add0r. Qed.

Lemma conjoxxE (a : oct R) :
  a *o a^*o = (a.1 * a.1^*q + a.2 * a.2^*q)%:ol.
Proof.
case: a => a0 a1; congr mkOct => /=; last first.
  by rewrite [a0 + _]addrC addrK conjqI addrC mulNr subrr.
by rewrite [a0 + _]addrC addrK linearN /= mulNr opprK conjq_comm.
Qed.

Lemma conjo_comm (a : oct R) : a^*o *o a = a *o a^*o.
Proof.
case: a => a0 a1; apply: (f_equal2 (@mkOct _)) => /=.
  rewrite !(mulrBl, mulrBr, mulrDr, mulrDl, linearN, mulNr, mulrN, opprK) /=.
  by rewrite conjq_comm.
rewrite !(linearB, linearD) /=.
rewrite !(mulrBl, mulrBr, mulrDr, mulrDl, linearN, mulNr, mulrN, opprK) /=.
rewrite [a1 * _ + _]addrC addrK subrr conjqI [_ + _ * a0]addrC addrK.
by rewrite addrC subrr.
Qed.

Lemma conjo_comm2 (a b : oct R) :
  b^*o *o a + a^*o *o b = a *o b^*o + b *o a^*o.
Proof.
apply: (addIr (a *o a ^*o + b *o b ^*o)).
rewrite [RHS]addrAC !{1}addrA -muloDr.
rewrite -[RHS]addrA -muloDr -muloDl -linearD /=.
rewrite addrC !addrA -conjo_comm -muloDr -addrA -conjo_comm.
rewrite -muloDr -muloDl.
rewrite -linearD /= [b + a]addrC.
by apply: conjo_comm.
Qed.

Lemma conjoM a b : (a *o b)^*o = b^*o *o a^*o.
Proof.
case: a b => [a0 a1] [b0 b1]; congr mkOct => /=; last first.
  rewrite !(linearB, linearD, mulrBl, mulrDl, mulrBr, mulrDr) /= conjqI.
rewrite !(mulNr, opprK) [-(a1 * _) - _]addrC subrK [_ - b1 * _]addrC subrK.
  by rewrite addrC.
rewrite !(linearN, linearB, mulrBl, mulrDl, mulrBr, mulrDr) /= 
          !conjqM /= !conjqI opprK.
rewrite [b0 * _ + _]addrC addrK [_ * a0 + _]addrC addrK.
rewrite opprD opprK subrK [_ + _ * a0^*q]addrC addrK.
rewrite [_ - _ * a1 + _]addrC -!addrA; congr (_ + _).
by rewrite [-(_ * b0) + _]addrC !addrA subrK addrK mulNr mulrN opprK.
Qed.

(* This part from altermate algebra -> Moufang equations comes from           *)
(* An Introduction to Nonassociative Algebras, by Schafer                     *)

Lemma muloAlt3 a b : (b *o a) *o a = b *o (a *o a).
Proof.
rewrite -[LHS]conjoI conjoM [(b *o a)^*o]conjoM -muloAlt1.
by rewrite -2!conjoM conjoI.
Qed.

Definition associator x y z := (x *o y) *o z - x *o (y *o z).
Local Notation "`a[ x , y , z ]" := (associator x y z).

Lemma associatorDl x1 x2 y z : 
  `a[x1 + x2, y, z] = `a[x1, y, z] + `a[x2, y, z].
Proof.
by rewrite /associator !muloDl opprD !addrA [X in X + _ = _]addrAC.
Qed.

Lemma associatorDm x1 x2 y z : 
  `a[y, x1 + x2, z] = `a[y, x1, z] + `a[y, x2, z].
Proof.
rewrite /associator !(muloDl, muloDr) !opprD {1}addrA.
by rewrite [X in X + _ = _]addrAC {1}[RHS]addrA.
Qed.

Lemma associatorDr x1 x2 y z : 
  `a[y, z, x1 + x2] = `a[y, z, x1] + `a[y, z, x2].
Proof.
rewrite /associator !(muloDl, muloDr) !opprD {1}addrA.
by rewrite [X in X + _ = _]addrAC {1}[RHS]addrA.
Qed.

Lemma associatorP1 x y : `a[x, x, y] =  0.
Proof. by rewrite /associator muloAlt1 subrr. Qed.

Lemma associatorP2 x y : `a[x, y, y] =  0.
Proof. by rewrite /associator muloAlt3 subrr. Qed.

Lemma associator_swap x y z : `a[x, y, z] =  - `a[y, x, z].
Proof.
apply: subr0_eq; rewrite opprK.
have H := associatorP1 (x + y) z.
by rewrite !associatorDl !associatorDm !associatorP1
            {1}add0r addrA {1}addr0 in H.
Qed.

Lemma associator_rot x y z : `a[x, y, z] =  `a[z, x, y].
Proof.
rewrite [RHS]associator_swap.
apply: subr0_eq; rewrite opprK.
have H := associatorP2 x (y + z).
by rewrite !associatorDr !associatorDm !associatorP2
            {1}add0r addrA {1}addr0 addrC in H.
Qed.

(* Moufang equality *)

Lemma mulo_moufang1 x a y : x *o a *o x *o y = x *o (a *o (x *o y)).
Proof.
apply: subr0_eq.
apply: etrans (_ : `a[x *o a, x, y] + `a[x, a, x *o y] = 0).
  by rewrite /associator {1}addrA subrK.
rewrite associator_swap [X in _ + X = _]associator_rot 
                        [X in _ + X = _]associator_swap /associator.
rewrite -{1}muloAlt1 -{1}muloAlt1 {1}opprD {1}opprK {1}opprD opprK {1}addrA.
rewrite -{1}[X in X + _ = _]addrAC.
have -> : - (x *o x *o a *o y) - x *o  x *o y *o a  = 
             -`a[x *o x, a, y] - `a[x *o x, y, a] - 
               x *o x *o (a *o y) - x *o x *o (y *o a).
  rewrite /associator {1}opprD opprK {1}opprD opprK.
  rewrite [X in _ = X - _]addrC {1}[X in _ = X - _]addrA.
  rewrite {1}[X in _ = X - _]addrA {1}addrK.
  by rewrite [X in _ = X - _]addrC addrK.
rewrite associator_rot associator_swap opprK {1}[X in X - _ - _ + _ + _]subrr.
rewrite sub0r muloAlt1 muloAlt1 -{1}addrA addrC {1}addrA.
rewrite -{1}muloNr -[X in _ + X = _]muloNr -3!{1}muloDr.
rewrite [X in _ *o (X - _)]addrAC -{1}addrA -/(associator _ _ _) 
         -/(associator _ _ _) associator_rot associator_swap addrC subrr.
by rewrite mulor0.
Qed.

Lemma mulo_moufang3 x a y : (x *o y) *o (a *o x) = x *o (y *o a) *o x.
Proof.
apply: subr0_eq.
apply: etrans (_ : `a[x, y, a *o x] + 
                     x *o (y *o (a *o x) - (y *o a) *o x) = 0).
  by rewrite /associator muloBr addrA subrK -{1}muloAlt2 .
rewrite -opprB -/(associator _ _ _).
rewrite associator_rot associator_swap {1}/associator {1}opprD opprK.
rewrite -{1}addrA -muloDr.
rewrite -muloAlt2 mulo_moufang1 -muloNr -muloDr.
rewrite {1}addrA [- _ + _]addrC -/(associator _ _ _).
by rewrite associator_rot subrr mulor0.
Qed.

Definition realo := [qualify x : oct R | (x.1 \is realq) && (x.2 == 0)].
Fact realo_key : pred_key realo. Proof. by []. Qed.
Canonical realo_keyed := KeyedQualifier realo_key.

Lemma realo_comm (a b : oct R) : a \is realo -> a *o b = b *o a.
Proof.
rewrite !qualifE; case: a => [[a0 a1] a2]; case: b => [b1 b2].
rewrite /= => /andP[/eqP-> /eqP->]; apply: (f_equal2 (@mkOct _)) => /=.
  by rewrite mulr0 subr0 linear0 mul0r subr0 realq_comm // realq_real.
by rewrite !mul0r addr0 add0r quat_realC.
Qed.

Lemma realo_real (a : quat R) : a \is realq -> a%:ol \is realo.
Proof. by rewrite !qualifE /= eqxx andbT. Qed.

Lemma realoE (a : oct R) : a \is realo -> a = (a.1.1%:q%quat)%:ol.
Proof. 
by rewrite !qualifE; case: a => [[a0 a1] a2] /= /andP[/eqP-> /eqP->].
Qed.

Lemma realoMEl (a b : oct R) : a \is realo -> a *o b = a.1.1 *: b.
Proof.
move=> /realoE {1}->; congr mkOct; rewrite /= (mul0r, mulr0).
  by rewrite quat_algE -scalerAl mul1r subr0.
by rewrite quat_algE -scalerAr mulr1 addr0.
Qed.

Lemma realoMEr (a b : oct R) : a \is realo -> b *o a = a.1.1 *: b.
Proof.
move=> /realoE {1}->; congr mkOct; rewrite /= ?linear0 (mul0r, mulr0).
  by rewrite quat_algE -scalerAr mulr1 subr0.
by rewrite quat_realC quat_algE -scalerAr mulr1 add0r.
Qed.

Lemma realoMAl (a b c : oct R) : a \is realo -> a *o (b *o c) = (a *o b) *o c.
Proof.
by move=> aR; rewrite (realoMEl _ aR) octAl - (realoMEl _ aR).
Qed.

Lemma realoMAm (a b c : oct R) : b \is realo -> a *o (b *o c) = (a *o b) *o c.
Proof.
by move=> bR; rewrite (realoMEl _ bR) -octAr octAl -(realoMEr _ bR).
Qed.

Lemma realoMAr (a b c : oct R) : c \is realo -> a *o (b *o c) = (a *o b) *o c.
Proof.
by move=> cR; rewrite (realoMEr _ cR) -octAr -(realoMEr _ cR).
Qed.

Lemma realo_conjD (a : oct R) : a + a^*o \is realo.
Proof. by rewrite !qualifE /= !subrr sub0r subrr eqxx /=. Qed.

Lemma realo_conjM (a : oct R) : a *o a^*o \is realo.
Proof.
rewrite !qualifE; case: a => a0 a1; apply/andP => /=; split;
    rewrite !(mulrBl, mulrBr, mulrDr, mulrDl, linearN, mulNr, mulrN, opprK) /=;
    last first.
  by rewrite [a0 + _]addrC addrK conjqI addrC subrr.
rewrite [- _ *: a1.2 + _]addrC !scaleNr !subrr addrK !sub0r !scalerN  add0r.
rewrite [- _ + _]addrC subrr add0r linearN /=.
by rewrite !rv3LieAlgebra.liexx subr0 oppr0.
Qed.

End octonion.

Arguments realo {R}.

Notation "x '^*o'" := (conjo x) : oct_scope.
Notation "a *o b" := (mulo a b) : oct_scope.

Section octonion1.
Variable R : rcfType.

Definition sqro (a : oct R) := sqrq a.1 + sqrq a.2.

Lemma sqro0 : sqro 0 = 0.
Proof. 
by apply/eqP; rewrite /sqro paddr_eq0 ?sqrq_ge0 // sqrq_eq0 eqxx.
Qed.

Lemma sqro_ge0 x : 0 <= sqro x.
Proof. by rewrite addr_ge0 // sqrq_ge0. Qed.

Lemma sqro_eq0 a : (sqro a == 0) = (a == 0).
Proof.
by rewrite /sqro paddr_eq0 ?sqrq_ge0// !sqrq_eq0 eq_oct.
Qed.

Lemma sqroN (a : oct R) : sqro (- a) = sqro a.
Proof. by rewrite /sqro !sqrqN. Qed.

Lemma sqro_conj (a : oct R) : sqro (a^*o) = sqro a.
Proof. by rewrite /sqro /conjo /= [a.1 + _]addrC addrK sqrq_conj sqrqN. Qed.

Lemma conjoZ k (a : oct R) : (k *: a) ^*o = k *: a ^*o.
Proof. 
by congr mkOct; rewrite ?scalerN // !conjqZ /= -scalerDr -scalerBr.
Qed.

Lemma conjoP (a : oct R) : a *o a^*o = ((sqro a)%:q%quat)%:ol.
Proof.
rewrite /mulo /=; congr mkOct.
  rewrite [a.1 + _]addrC addrK linearN /= mulNr opprK conjq_comm !conjqP.
  by rewrite -quat_realD.
by rewrite [a.1 + _]addrC addrK conjqI addrC mulNr subrr.
Qed.

Local Notation "`il" := (`i%quat)%:ol.
Local Notation "`ir" := (`i%quat)%:or.
Local Notation "`jl" := (`j%quat)%:ol.
Local Notation "`jr" := (`j%quat)%:or.
Local Notation "`kl" := (`k%quat)%:ol.
Local Notation "`kr" := (`k%quat)%:or.


Lemma conjoE (a : oct R) :
  a^*o = 
    - (1 / 6%:R) *: (a + `il *o a *o `il + `jl *o a *o `jl + `kl *o a *o `kl
                       + 1%:or *o a *o 1%:or
                       + `ir *o a *o `ir + `jr *o a *o `jr + `kr *o a *o `kr).
Proof.
rewrite (_  : - (1/6%:R) = ((1/3%:R) * -(1/2%:R))); last first.
  by rewrite mulrN !mulrA mulr1 -mulrA -invfM -natrM.
rewrite -3!addrA scalerDr.
apply/eqP; rewrite eq_oct; apply/andP; split; apply/eqP.
  rewrite [in LHS]/= scaleoctE /=.
  rewrite !{1}(linear0, mul0r, mulr0, sub0r, add0r, subr0).
  rewrite [a.1 + _^*q]addrC addrK -scalerA addr0 -conjqE !mulrA !conjq_comm.
  rewrite !conjqP /sqrq /= norm0 !expr0n  expr1n /= !add0r !addr0.
  rewrite !normeE !mul1r expr1n mul1r -3!opprD addrA -!mulr2n scalerN.
  rewrite -mulrnA -scaler_nat !scalerA -scalerBl.
  rewrite -{1}[3%:R^-1]mulr1 -mulrA -mulrBr natrM mulrA mulNr.
  rewrite  mulVf ?(eqr_nat _ _ 0) //.
  by rewrite mulNr opprK mul1r -(natrD _ 1) mulVf ?(eqr_nat _ _ 0) // scale1r.
rewrite [in LHS]/= scaleoctE /=.
rewrite !{1}(linear0, mul0r, mulr0, sub0r, add0r, subr0).
apply: etrans (_ : -(2%:R / 3%:R) *: a.2 + -(1 / 3%:R) *: a.2 = _).
  rewrite -scalerDl -opprD -mulrDl -(natrD _ _ 1) mulfV ?scaleN1r //.
  by rewrite (eqr_nat _ _ 0).
congr (_ + _).
  rewrite 3!addr0 -scalerA -!{1}mulrA !{1}conjqP /sqrq !normeE /= 
          !expr0n !expr1n /=.
  rewrite !add0r !mul1r !mulr1 mulrC -mulrN -scalerA.
  rewrite -addrA -!mulr2n -mulrnA -scaler_nat !scalerA natrM mulrA.
  by rewrite !mulrN !mulNr divfK // (eqr_nat _ 2 0).
rewrite -{1}[a.2]conjqI conjqE -scalerA scaleNr -scalerN; congr (_ *: _).
rewrite -scalerN; congr (_ *: _); rewrite !opprD.
rewrite !(mulNr, mulrN) 4!mulrA mul1r mulr1.
by rewrite 4!{1}[_ + 0]addr0 -!{1}opprD !{1}addrA.
Qed.

Lemma conjo_scalar (a : oct R) : 
  (a.1.1)%:q%quat%:ol = (1 / 2%:R) *: (a + a^*o).
Proof.
rewrite /conjo [a.1 + _]addrC addrK addoE.
have {2}->/= : a = mkOct a.1 a.2 by case: a.
by rewrite /addo /= subrr conjq_scalar oct_leftZ.
Qed.

Definition invo (a : oct R) : oct R := (1 / sqro a) *: (a ^*o).

Lemma mulVo a : a !=0 -> invo a *o a = 1%:ol.
Proof.
move => aNZ.
rewrite /invo -octAl conjo_comm conjoP.
congr mkOct => /=; last by rewrite scaler0.
by rewrite -quat_realZ mul1r mulVf // sqro_eq0.
Qed.

Lemma muloV a : a != 0 -> a *o invo a = 1%:ol.
Proof.
move => aNZ.
rewrite /invo -octAr conjoP.
congr mkOct => /=; last by rewrite scaler0.
by rewrite -quat_realZ mul1r mulVf // sqro_eq0.
Qed.

Lemma realo_realq (x : R) : x%:q%quat%:ol \in realo.
Proof. by apply/realo_real/realq_real. Qed.

Lemma conjoMA (a b : oct R) : 
  (a *o b) *o (a *o b)^*o = a *o (b *o b ^*o) *o a^*o.
Proof.
rewrite conjoM -[a^*o](addrK a) [a ^*o + _]addrC (realoE (realo_conjD _)).
set x := _%:ol.
rewrite !{1}muloBr {1}mulo_moufang3.
rewrite {1}(realoMAr _ _ (realo_realq _)) -/x.
rewrite -{1 3}[b^*o](addrK b) [b ^*o + _]addrC (realoE (realo_conjD _)).
set y := _%:ol.
rewrite !{1}muloBr {1}muloAlt3.
by rewrite {1}(realoMAr _ _ (realo_realq _)).
Qed.

Lemma sqroM a b : sqro (a *o b) = sqro a * sqro b.
Proof.
have F (x y : R) : (x%:q = y%:q -> x = y)%quat by case.
apply: F.
have F (x y : quat R) : (x%:ol = y%:ol -> x = y)%quat by case.
apply: F.
rewrite quat_realM oct_leftM -!conjoP conjoMA.
rewrite -{1}(realoMAm _ _ (realo_conjM _)).
rewrite {1}(realo_comm _ (realo_conjM _)).
by rewrite {1}(realoMAr _ _ (realo_conjM _)).
Qed.

Lemma sqroZ k a : sqro (k *: a) = k ^+ 2 * sqro a.
Proof.
have F (x y : R) : (x%:q = y%:q -> x = y)%quat by case.
apply: F.
have F (x y : quat R) : (x%:ol = y%:ol -> x = y)%quat by case.
apply: F.
rewrite -!conjoP -octAl conjoZ octAr scalerA -octAr -expr2.
by rewrite quat_realZ oct_leftZ -conjoP.
Qed.

Lemma oct_integral (x y : oct R) : (x *o y == 0) = ((x == 0) || (y == 0)).
Proof.
case: (x =P 0) => [->|/eqP xNZ] /=; first by rewrite mulo0r eqxx.
apply/eqP/eqP => [xyZ|->]; last by rewrite mulor0.
rewrite -[y]mulo1r -(@mulVo x) // /invo -2!{1}octAl.
rewrite -[x^*o](addrK x) [x ^*o + _]addrC (realoE (realo_conjD _)).
set a := _%:ol.
rewrite 2!muloBl muloAlt1 -(realoMAl  _ _ (realo_realq _)) -/a.
by rewrite -muloBl xyZ mulor0 scaler0.
Qed.

Definition normo (a : oct R) : R := Num.sqrt (sqro a).

Lemma normo0 : normo 0 = 0.
Proof. by rewrite /normo sqro0 sqrtr0. Qed.

Lemma normoc a : normo a ^*o = normo a.
Proof. by rewrite /normo sqro_conj. Qed.

Lemma normoE a : (normo a ^+ 2)%:q%quat%:ol = a ^*o *o a.
Proof.
rewrite -normoc /normo sqr_sqrtr ?sqro_ge0 //.
by rewrite -conjoP conjoI.
Qed.

Lemma normo_ge0 a : 0 <= normo a.
Proof. by apply sqrtr_ge0. Qed.

Lemma normo_eq0 a : (normo a == 0) = (a == 0).
Proof. 
rewrite /normo sqrtr_eq0 -sqro_eq0.
by case: ltrgt0P (sqro_ge0 a).
Qed.

Lemma normoM (a b : oct R) : normo (a *o b) = normo a * normo b.
Proof. by rewrite /normo sqroM sqrtrM // sqro_ge0. Qed.

Lemma normoZ (k : R) (a : oct R) : normo (k *: a) = `|k| * normo a.
Proof.
by rewrite /normo sqroZ sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma normoV (a : oct R) : normo (invo a) = normo a / sqro a.
Proof.
rewrite /invo normoZ normoc ger0_norm.
  by rewrite mulrC mul1r.
by rewrite mul1r invr_ge0 sqro_ge0.
Qed.

End octonion1.
