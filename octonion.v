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
(* x \is realo == x is a real ie only the real part of the left quaternion    *)
(*                is not zero                                                 *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x %:ol" (at level 2, format "x %:ol").
Reserved Notation "x %:or" (at level 2, format "x %:or").
Reserved Notation "x '^*o'" (at level 2, format "x '^*o'").

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

Definition addoct (a b : oct) := mkOct (a.1 + b.1) (a.2 + b.2).

Lemma addoctC : commutative addoct.
Proof. move=> *; congr mkOct; by rewrite addrC. Qed.

Lemma addoctA : associative addoct.
Proof. move=> *; congr mkOct; by rewrite addrA. Qed.

Lemma add0oct : left_id 0%:ol addoct.
Proof. case=> *; by rewrite /addoct /= 2!add0r. Qed.

Definition oppoct (a : oct) := mkOct (- a.1) (- a.2).

Lemma addNoct : left_inverse 0%:ol oppoct addoct.
Proof. move=> *; congr mkOct; by rewrite addNr. Qed.

Definition oct_ZmodMixin := ZmodMixin addoctA addoctC add0oct addNoct.
Canonical oct_ZmodType := ZmodType oct oct_ZmodMixin.

Lemma addoctE (a b : oct) : a + b = addoct a b. Proof. done. Qed.

Lemma oppoctE (a : oct) : - a = oppoct a. Proof. done. Qed.

Lemma octE (a : oct) : a = (a.1)%:ol + (a.2)%:or.
Proof. by apply/eqP; rewrite eq_oct /= !(add0r,addr0) !eqxx. Qed.

Lemma oct_leftE (a b : quat R) : (a%:ol == b%:ol) = (a == b).
Proof. by apply/idP/idP => [/eqP[] ->|/eqP -> //]. Qed.

Lemma oct_leftN (x: quat R) : (-x)%:ol = -(x%:ol).
Proof. by rewrite oppoctE /oppoct /= oppr0. Qed.

Lemma oct_rightN (x: quat R) : (-x)%:or = -(x%:or).
Proof. by rewrite oppoctE /oppoct /= oppr0. Qed.

Lemma oct_leftD (x y : quat R) : (x + y)%:ol = x%:ol + y%:ol.
Proof. by rewrite addoctE /addoct /= add0r. Qed.

Lemma oct_rightD (x y : quat R) : (x + y)%:or = x%:or + y%:or.
Proof. by rewrite addoctE /addoct /= addr0. Qed.

Lemma oct_leftB (x y : quat R) : (x - y)%:ol = x%:ol - y%:ol.
Proof. by rewrite oct_leftD oct_leftN. Qed.

Lemma oct_rightB (x y : quat R) : (x - y)%:or = x%:or - y%:or.
Proof. by rewrite oct_rightD oct_rightN. Qed.

End octonion0.

Delimit Scope oct_scope with oct.
Local Open Scope oct_scope.

Notation "x %:ol" := (mkOct x 0) : oct_scope.
Notation "x %:or" := (mkOct 0 x) : oct_scope.

Section octonion.

Variable R : comRingType.

Definition muloct (a b : oct R) :=
  mkOct (a.1 * b.1 - ((b.2)^*q)%quat * a.2) (b.2 * a.1 + a.2 * ((b.1)^*q)%quat).

Lemma mul1oct : left_id 1%:ol muloct.
Proof.
by case=> a a'; rewrite /muloct /=; congr mkOct; Simp.r => /=.
Qed.

Lemma muloct1 : right_id 1%:ol muloct.
Proof.
case=> a a'; rewrite /muloct /=; congr mkOct.
  by rewrite linear0 mul0r subr0 mulr1.
by rewrite quat_realC mulr1 mul0r add0r.
Qed.

Lemma muloctDl : left_distributive muloct +%R.
Proof.
move=> [a a'] [b b'] [c c']; rewrite /muloct /=; congr mkOct => /=.
  rewrite !(mulrDl, mulrDr) -!addrA; congr (_ + _).
  by rewrite addrCA opprD.
rewrite !(mulrDl, mulrDr) -!addrA; congr (_ + _).
by rewrite addrCA.
Qed.

Lemma muloctDr : right_distributive muloct (+%R).
Proof.
move=> [a a'] [b b'] [c c']; rewrite /muloct /=; congr mkOct => /=.
  rewrite !(mulrDl, mulrDr, linearD) /= -!addrA; congr (_ + _).
  by rewrite addrCA.
rewrite !(mulrDl, mulrDr, linearD) /= -!addrA; congr (_ + _).
by rewrite addrCA.
Qed.

Lemma oneq_neq0 : 1%:ol != 0 :> oct R.
Proof. apply/eqP => -[]; apply/eqP. exact: oner_neq0. Qed.

Local Notation "a *o b" :=
  (muloct a b) (at level 40, left associativity, format "a  *o  b").

(* sanity check *)
Lemma muloAW a b : (a *o a) *o  b = a *o (a *o b).
Proof.
case: a => [a0 a1]; case: b => [b0 b1]; congr mkOct => /=;
    rewrite !(mulrBr, mulrDr, mulrBl, mulrDl, mulrA, linearD) /= 
              !conjqM ?conjqI !addrA.
  rewrite -!addrA; congr (_ + _).
  rewrite addrC !addrA; congr (_ + _); last first.
    by rewrite realq_comm ?mulrA // conjq_comm realq_conjM.
  by rewrite -opprD -mulrDr -realq_comm ?realq_conjD // mulrDl opprD !mulrA.
rewrite -!addrA linearN /= !conjqM !conjqI !mulrN !mulrA; congr (_ + _).
rewrite -mulrA conjq_comm -[b1 * _]realq_comm ?realq_conjM //.
rewrite addrC !addrA; congr (_ + _).
by rewrite -!mulrDl -!mulrDr -mulrA (realq_comm _ (realq_conjD _)) mulrA.
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

Definition conjoct (a : oct R) := mkOct (a.1 + (a.1)^*q -a.1) (- a.2).
Local Notation "x '^*o'" := (conjoct x).

Lemma conjoct_linear : linear conjoct.
Proof.
move=> /= k [a0 a1] [b0 b1] /=; rewrite [in LHS]/conjoct /= [in RHS]/conjoct /=.
congr mkOct => /=; last by rewrite scalerN opprD.
rewrite !(linearD, linearZ) /= !scalerN -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrCA !addrA subrK [_ + b0 + _]addrC addrA addrK addrC.
Qed.

Canonical conjoct_is_additive := Additive conjoct_linear.
Canonical conjoct_is_linear := AddLinear conjoct_linear.

Lemma conjoctI a : (a^*o)^*o = a.
Proof. 
case: a => a0 a1; congr mkOct => /=; last by rewrite opprK.
by rewrite [a0 + _]addrC addrK conjqI [_ + a0]addrC addrK.
Qed.

Lemma conjoct0 : (0%:ol)^*o = 0.
Proof. by congr mkOct; rewrite oppr0 //= linear0 !add0r. Qed.

Lemma conjoctxxE (a : oct R) :
  a *o a^*o = (a.1 * a.1^*q + a.2 * a.2^*q)%:ol.
Proof.
case: a => a0 a1; congr mkOct => /=; last first.
  by rewrite [a0 + _]addrC addrK conjqI addrC mulNr subrr.
by rewrite [a0 + _]addrC addrK linearN /= mulNr opprK conjq_comm.
Qed.

Lemma conjoct_comm (a : oct R) : a^*o *o a = a *o a^*o.
Proof.
case: a => a0 a1; congr mkOct => /=.
  rewrite !(mulrBl, mulrBr, mulrDr, mulrDl, linearN, mulNr, mulrN, opprK) /=.
  by rewrite conjq_comm.
rewrite !(linearB, linearD) /=.
rewrite !(mulrBl, mulrBr, mulrDr, mulrDl, linearN, mulNr, mulrN, opprK) /=.
rewrite [a1 * _ + _]addrC addrK subrr conjqI [_ + _ * a0]addrC addrK.
by rewrite addrC subrr.
Qed.

Lemma conjoct_comm2 (a b : oct R) :
  b^*o *o a + a^*o *o b = a *o b^*o + b *o a^*o.
Proof.
apply: (addIr (a *o a ^*o + b *o b ^*o)).
rewrite [RHS]addrAC !addrA -muloctDr.
rewrite -[RHS]addrA -muloctDr -muloctDl -linearD /=.
rewrite addrC !addrA -conjoct_comm -muloctDr -addrA -conjoct_comm.
rewrite -muloctDr -muloctDl.
rewrite -linearD /= [b + a]addrC.
by apply: conjoct_comm.
Qed.

Lemma conjoctM a b : (a *o b)^*o = b^*o *o a^*o.
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

Definition realo := [qualify x : oct R | (x.1 \is realq R) && (x.2 == 0)].
Fact realo_key : pred_key realo. Proof. by []. Qed.
Canonical realo_keyed := KeyedQualifier realo_key.

Lemma realo_comm (a b : oct R) : a \is realo -> a *o b = b *o a.
Proof.
rewrite !qualifE; case: a => [[a0 a1] a2]; case: b => [b1 b2].
rewrite /= => /andP[/eqP-> /eqP->]; congr mkOct => /=.
  by rewrite mulr0 subr0 linear0 mul0r subr0 realq_comm // realq_real.
by rewrite !mul0r addr0 add0r quat_realC.
Qed.

Lemma realo_real (a : quat R) : a \is realq R -> a%:ol \is realo.
Proof. by rewrite !qualifE /= eqxx andbT. Qed.

Lemma realoE (a : oct R) : a \is realo -> a = (a.1.1%:q%quat)%:ol.
Proof. 
by rewrite !qualifE; case: a => [[a0 a1] a2] /= /andP[/eqP-> /eqP->].
Qed.

Lemma realo_conj (a : oct R) : a *o a^*o \is realo.
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

Notation "x '^*o'" := (conjoct x) : oct_scope.
