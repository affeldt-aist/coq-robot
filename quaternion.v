(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat poly.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import realalg complex fingroup perm.
Require Import ssr_ext euclidean angle vec_angle frame rot.
From mathcomp.analysis Require Import forms.

(******************************************************************************)
(*                            Quaternions                                     *)
(*                                                                            *)
(* This file develops the theory of quaternions. It defines the type of       *)
(* quaternions and the type of unit quaternions and show that quaternions     *)
(* form a ZmodType, a RingType, a LmodType, a UnitRingType. It also defines   *)
(* polar coordinates and dual quaternions.                                    *)
(*                                                                            *)
(*        quat R == type of quaternions over the ringType R                   *)
(*          x%:q == quaternion with scalar part x and vector part 0           *)
(*          u%:v == pure quaternion with scalar part 0 and vector part u      *)
(*   x \is pureq == the quaternion x has no scalar part                       *)
(*   x \is realq == the quaternion x has no vector part                       *)
(*    `i, `j, `k == basic quaternions                                         *)
(*           x.1 == scalar part of the quaternion x                           *)
(*           x.2 == vector part of the quaternion x                           *)
(*          a^*q == conjugate of quaternion a                                 *)
(*       normq a == norm of the quaternion a                                  *)
(*       uquat R == type of unit quaternions, i.e., quaternions with norm 1   *)
(* conjugation x == v |-> x v x^*                                             *)
(*                                                                            *)
(* Polar coordinates:                                                         *)
(*     polar_of_quat a == polar coordinates of the quaternion a               *)
(*   quat_of_polar a u == quaternion corresponding to the polar coordinates   *)
(*                        angle a and vector u                                *)
(*          quat_rot x == snd \o conjugation x (rotation of angle 2a about    *)
(*                        vector v where a,v are the polar coordinates of x,  *)
(*                        a unit quaternion                                   *)
(* Dual numbers:                                                              *)
(*     dual R == the type of dual numbers over a ringType R                   *)
(*        x.1 == left part of the dual number x                               *)
(*        x.2 == right part of the dual number x                              *)
(* Dual numbers are equipped with a structure of ZmodType, RingType, and of   *)
(* LmodType when R is a ringType, of Com/UnitRingType when R is a             *)
(* Com/UnitRingType.                                                          *)
(*                                                                            *)
(* Dual quaternions:                                                          *)
(*     x +ɛ* y  == dual number formed by x and y                              *)
(*        dquat == type of dual quaternions                                   *)
(* x \is puredq == the dual quaternion x is pure                              *)
(*   a \is dnum == a has no vector part                                       *)
(*        x^*dq == conjugate of dual quaternion x                             *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "x %:q" (at level 2, format "x %:q").
Reserved Notation "x %:v" (at level 2, format "x %:v").
Reserved Notation "Q '_i'" (at level 1, format "Q '_i'").
Reserved Notation "Q '_j'" (at level 1, format "Q '_j'").
Reserved Notation "Q '_k'" (at level 1, format "Q '_k'").
Reserved Notation "'`i'".
Reserved Notation "'`j'".
Reserved Notation "'`k'".
Reserved Notation "x '^*q'" (at level 2, format "x '^*q'").
Reserved Notation "a *`i" (at level 3).
Reserved Notation "a *`j" (at level 3).
Reserved Notation "a *`k" (at level 3).
Reserved Notation "x +ɛ* y"
  (at level 40, left associativity, format "x  +ɛ*  y").
Reserved Notation "x -ɛ* y"
  (at level 40, left associativity, format "x  -ɛ*  y").
Reserved Notation "x '^*d'" (at level 2, format "x '^*d'").

Declare Scope quat_scope.
Declare Scope dual_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section quaternion0.
Variable R : ringType.

Record quat := mkQuat {quatl : R ; quatr : 'rV[R]_3 }.

Local Notation "x %:q" := (mkQuat x 0).
Local Notation "x %:v" := (mkQuat 0 x).
Local Notation "'`i'" := ('e_0)%:v.
Local Notation "'`j'" := ('e_1)%:v.
Local Notation "'`k'" := ('e_2%:R)%:v.
Local Notation "Q '_i'" := ((Q.2)``_0).
Local Notation "Q '_j'" := ((Q.2)``_1).
Local Notation "Q '_k'" := ((Q.2)``_(2%:R : 'I_3)).

Coercion pair_of_quat (a : quat) := let: mkQuat a0 a1 := a in (a0, a1).
Let quat_of_pair (x : R * 'rV[R]_3) :=
  let: (x0, x1) := x in mkQuat x0 x1.

Lemma quat_of_pairK : cancel pair_of_quat quat_of_pair.
Proof. by case. Qed.

Definition quat_eqMixin := CanEqMixin quat_of_pairK.
Canonical Structure quat_eqType := EqType quat quat_eqMixin.
Definition quat_choiceMixin := CanChoiceMixin quat_of_pairK.
Canonical Structure quat_choiceType := ChoiceType quat quat_choiceMixin.

Lemma eq_quat (a b : quat) : (a == b) = (a.1 == b.1) && (a.2 == b.2).
Proof.
case: a b => [a0 a1] [b0 b1] /=.
apply/idP/idP => [/eqP [ -> ->]|/andP[/eqP -> /eqP -> //]]; by rewrite !eqxx.
Qed.

Definition addq (a b : quat) := nosimpl (mkQuat (a.1 + b.1) (a.2 + b.2)).

Lemma addqC : commutative addq.
Proof. move=> *; congr mkQuat; by rewrite addrC. Qed.

Lemma addqA : associative addq.
Proof. move=> *; congr mkQuat; by rewrite addrA. Qed.

Lemma add0q : left_id 0%:q addq.
Proof. case=> *; by rewrite /addq /= 2!add0r. Qed.

Definition oppq (a : quat) := nosimpl (mkQuat (- a.1) (- a.2)).

Lemma addNq : left_inverse 0%:q oppq addq.
Proof. move=> *; congr mkQuat; by rewrite addNr. Qed.

Definition quat_ZmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical quat_ZmodType := ZmodType quat quat_ZmodMixin.

Lemma addqE (a b : quat) : a + b = addq a b. Proof. done. Qed.

Lemma oppqE (a : quat) : - a = oppq a. Proof. done. Qed.

Local Notation "a *`i" := (mkQuat 0 (a *: 'e_0)) (at level 3).
Local Notation "a *`j" := (mkQuat 0 (a *: 'e_1)) (at level 3).
Local Notation "a *`k" := (mkQuat 0 (a *: 'e_2%:R)) (at level 3).

Lemma quatE (a : quat) : a = a.1%:q + a.2%:v.
Proof. by apply/eqP; rewrite eq_quat /=; Simp.r. Qed.

Lemma quatrE (a : quat) : a.2%:v = a _i *`i + a _j *`j + a _k *`k.
Proof. by apply/eqP; rewrite eq_quat /=; Simp.r; rewrite -vec3E. Qed.

Lemma quat_scalarE (a b : R) : (a%:q == b%:q) = (a == b).
Proof. by apply/idP/idP => [/eqP[] ->|/eqP -> //]. Qed.

Lemma quat_realN (x: R) : (-x)%:q = -(x%:q).
Proof. by rewrite oppqE /oppq /= oppr0. Qed.

Lemma quat_vectN (x: 'rV[R]_3) : (-x)%:v = -(x%:v).
Proof. by rewrite oppqE /oppq /= oppr0. Qed.

Lemma quat_realD (x y : R) : (x + y)%:q = x%:q + y%:q.
Proof. by rewrite addqE /addq /= add0r. Qed.

Lemma quat_vectD (x y : 'rV[R]_3) : (x + y)%:v = x%:v + y%:v.
Proof. by rewrite addqE /addq /= addr0. Qed.

Lemma quat_realB (x y : R) : (x - y)%:q = x%:q - y%:q.
Proof. by rewrite quat_realD quat_realN. Qed.

Lemma quat_vectB (x y : 'rV[R]_3) : (x - y)%:v = x%:v - y%:v.
Proof. by rewrite quat_vectD quat_vectN. Qed.

Definition pureq := [qualify x : quat | x.1 == 0].
Fact pureq_key : pred_key pureq. Proof. by []. Qed.
Canonical pureq_keyed := KeyedQualifier pureq_key.

Definition realq := [qualify x : quat | x.2 == 0].
Fact realq_key : pred_key realq. Proof. by []. Qed.
Canonical realq_keyed := KeyedQualifier realq_key.

End quaternion0.

Delimit Scope quat_scope with quat.
Local Open Scope quat_scope.

Notation "x %:q" := (mkQuat x 0) : quat_scope.
Notation "x %:v" := (mkQuat 0 x) : quat_scope.
Notation "'`i'" := ('e_0)%:v : quat_scope.
Notation "'`j'" := ('e_1)%:v : quat_scope.
Notation "'`k'" := ('e_2%:R)%:v : quat_scope.
Notation "Q '_i'" := ((Q.2)``_0) : quat_scope.
Notation "Q '_j'" := ((Q.2)``_1) : quat_scope.
Notation "Q '_k'" := ((Q.2)``_(2%:R : 'I_3)) : quat_scope.
Notation "a *`i" := (mkQuat 0 (a *: 'e_0)) : quat_scope.
Notation "a *`j" := (mkQuat 0 (a *: 'e_1)) : quat_scope.
Notation "a *`k" := (mkQuat 0 (a *: 'e_2%:R)) : quat_scope.

Arguments pureq {R}.

Import rv3LieAlgebra.Exports.

Structure Conjugate := { conjugate_type : Type ;
                         conjugate_op : conjugate_type -> conjugate_type }.

Definition conjugate_op_nosimpl := nosimpl conjugate_op.

Notation "a '^*q'" := (@conjugate_op_nosimpl _ a).

Section quaternion.
Variable R : comRingType.

Definition mulq (a b : quat R) := nosimpl
  (mkQuat (a.1 * b.1 - a.2 *d b.2) (a.1 *: b.2 + b.1 *: a.2 + a.2 *v b.2)).

Lemma mulqA : associative mulq.
Proof.
move=> [a a'] [b b'] [c c']; congr mkQuat => /=.
- rewrite mulrDr mulrDl mulrA -!addrA; congr (_ + _).
  rewrite mulrN !dotmulDr !dotmulDl !opprD !addrA dot_crossmulC; congr (_ + _).
  rewrite addrC addrA; congr (_ + _ + _).
  by rewrite mulrC dotmulvZ mulrN.
  by rewrite dotmulZv.
  by rewrite dotmulvZ dotmulZv.
- rewrite 2![in LHS]scalerDr 1![in RHS]scalerDl scalerA.
  rewrite -4![in LHS]addrA -3![in RHS]addrA; congr (_ + _).
  rewrite [in RHS]scalerDr [in RHS]addrCA
         -[in RHS]addrA -[in LHS]addrA; congr (_ + _).
    by rewrite scalerA mulrC -scalerA.
  rewrite [in RHS]scalerDr [in LHS]scalerDl [in LHS]addrCA
         -[in RHS]addrA -addrA; congr (_ + _).
    by rewrite scalerA mulrC.
  rewrite (addrC (a *: _)) linearD /= (addrC (a' *v _)) linearD /=.
  rewrite -![in LHS]addrA ![in LHS]addrA (addrC (- _ *: a'))
          -![in LHS]addrA; congr (_ + _).
    by rewrite linearZ.
  rewrite [in RHS]lieC /= linearD /= opprD [in RHS]addrCA
         ![in LHS]addrA addrC -[in LHS]addrA.
  congr (_ + _); first by rewrite linearZ /= lieC scalerN.
  rewrite addrA addrC linearD /= opprD [in RHS]addrCA; congr (_ + _).
    by rewrite !linearZ /= lieC.
  rewrite 2!double_crossmul opprD opprK
         [in RHS]addrC addrA; congr (_ + _); last first.
    by rewrite scaleNr.
  by rewrite dotmulC scaleNr; congr (_ + _); rewrite dotmulC.
Qed.

Lemma mul1q : left_id 1%:q mulq.
Proof.
case=> a a'; rewrite /mulq /=; congr mkQuat; Simp.r => /=.
  by rewrite dotmul0v subr0.
by rewrite linear0l addr0.
Qed.

Lemma mulq1 : right_id 1%:q mulq.
Proof.
case=> a a'; rewrite /mulq /=; congr mkQuat; Simp.r => /=.
  by rewrite dotmulv0 subr0.
by rewrite linear0r addr0.
Qed.

Lemma mulqDl : left_distributive mulq (@addq R).
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulq /=; congr mkQuat => /=.
  by rewrite [in RHS]addrCA 2!addrA -mulrDl (addrC a) dotmulDl opprD addrA.
rewrite scalerDl -!addrA; congr (_ + _).
rewrite [in RHS](addrCA (a' *v c')) [in RHS](addrCA (c *: a')); congr (_ + _).
rewrite scalerDr -addrA; congr (_ + _).
rewrite addrCA; congr (_ + _).
by rewrite lieC linearD /= lieC opprD opprK (lieC b').
Qed.

Lemma mulqDr : right_distributive mulq (@addq R).
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulq /=; congr mkQuat => /=.
  rewrite mulrDr -!addrA; congr (_ + _).
  rewrite addrCA; congr (_ + _).
  by rewrite dotmulDr opprD.
rewrite scalerDr -!addrA; congr (_ + _).
rewrite [in RHS](addrCA (a' *v b')) [in RHS](addrCA (b *: a')); congr (_ + _).
rewrite scalerDl -addrA; congr (_ + _).
by rewrite addrCA linearD.
Qed.

Lemma oneq_neq0 : 1%:q != 0 :> quat R.
Proof. apply/eqP => -[]; apply/eqP. exact: oner_neq0. Qed.

Definition quat_RingMixin :=
  RingMixin mulqA mul1q mulq1 mulqDl mulqDr oneq_neq0.
Canonical Structure quat_Ring := Eval hnf in RingType (quat R) quat_RingMixin.

Lemma mulqE a b : a * b = mulq a b. Proof. done. Qed.

Lemma realq_comm (a b : quat R) : a \is realq R -> a * b = b * a.
Proof.
rewrite qualifE; case: a => [a0 a1]; case: b => [b1 b2] /= /eqP->.
congr mkQuat => /=; first by rewrite dotmul0v dotmulv0 mulrC.
by rewrite scaler0 !linear0 add0r addr0 -/(crossmulr _ _) linear0 addr0.
Qed.

Lemma realq_real (a : R) : a%:q \is realq R.
Proof. by rewrite qualifE. Qed.

Lemma realqE (a : quat R) : a \is realq R -> a = (a.1)%:q.
Proof. by rewrite qualifE; case: a => [a0 a1] /= /eqP->. Qed.

Lemma quat_realM (x y : R) : (x * y)%:q = x%:q * y%:q.
Proof. by congr mkQuat; rewrite /= (dotmul0v, linear0l); Simp.r. Qed.

Lemma iiN1 : `i * `i = -1.
Proof. by congr mkQuat; rewrite (dote2, liexx) /=; Simp.r. Qed.

Lemma ijk : `i * `j = `k.
Proof. by congr mkQuat; rewrite /= (dote2, vecij); Simp.r. Qed.

Lemma ikNj : `i * `k = - `j.
Proof. by congr mkQuat; rewrite /= (dote2, vecik); Simp.r. Qed.

Lemma jiNk : `j * `i = - `k.
Proof. by congr mkQuat; rewrite /= (dote2, vecji); Simp.r. Qed.

Lemma jjN1 : `j * `j = -1.
Proof. by congr mkQuat; rewrite /= (dote2, liexx); Simp.r. Qed.

Lemma jkNi : `j * `k = `i.
Proof. by congr mkQuat; rewrite /= ?(dote2, vecjk) //; Simp.r. Qed.

Lemma kij : `k * `i = `j.
Proof. by congr mkQuat; rewrite /= (dote2, vecki); Simp.r. Qed.

Lemma kjNi : `k * `j = - `i.
Proof. by congr mkQuat; rewrite /= (dote2, veckj); Simp.r. Qed.

Lemma kkN1 : `k * `k = -1.
Proof. by congr mkQuat; rewrite /= (dote2, liexx); Simp.r. Qed.

Definition scaleq k (a : quat R) := mkQuat (k * a.1) (k *: a.2).

Lemma scaleqA a b w : scaleq a (scaleq b w) = scaleq (a * b) w.
Proof.
rewrite /scaleq /=; congr mkQuat; by [rewrite mulrA | rewrite scalerA].
Qed.

Lemma scaleq1 : left_id 1 scaleq.
Proof.
by move=> q; rewrite /scaleq mul1r scale1r; apply/eqP; rewrite eq_quat /= !eqxx.
Qed.

Lemma scaleqDr : @right_distributive R (quat R) scaleq +%R.
Proof. move=> a b c; by rewrite /scaleq /= mulrDr scalerDr. Qed.

Lemma scaleqDl w : {morph (scaleq^~ w : R -> quat R) : a b / a + b}.
Proof. move=> m n; rewrite /scaleq mulrDl /= scalerDl; congr mkQuat. Qed.

Definition quat_lmodMixin := LmodMixin scaleqA scaleq1 scaleqDr scaleqDl.
Canonical quat_lmodType := Eval hnf in LmodType R (quat R) quat_lmodMixin.

Lemma scaleqE (k : R) (a : quat R) : k *: a = k *: a.1%:q + k *: a.2%:v.
Proof. by apply/eqP; rewrite eq_quat /=; Simp.r. Qed.

Lemma quat_realZ (k : R) (x : R) : (k * x)%:q = k *: x%:q.
Proof. by congr mkQuat; rewrite scaler0. Qed.

Lemma quat_vectZ (k : R) (x : 'rV[R]_3) : (k *: x)%:v = k *: x%:v.
Proof. by congr mkQuat; rewrite /= mulr0. Qed.

Lemma quatAl k (a b : quat R) : k *: (a * b) = k *: a * b.
Proof.
case: a b => [a0 a1] [b0 b1]; apply/eqP.
rewrite !mulqE /mulq /= scaleqE /= eq_quat /=.
apply/andP; split; first by Simp.r; rewrite mulrBr mulrA dotmulZv.
apply/eqP; Simp.r; rewrite 2!scalerDr scalerA -2!addrA; congr (_ + _).
by rewrite linearZl_LR /=; congr (_ + _); rewrite scalerA mulrC -scalerA.
Qed.
Canonical quat_lAlgType := Eval hnf in LalgType _ (quat R) quatAl.

Lemma quatAr k (a b : quat R) : k *: (a * b) = a * (k *: b).
Proof.
case: a b => [a0 a1] [b0 b1]; apply/eqP.
rewrite !mulqE /mulq /= scaleqE /= eq_quat /=.
apply/andP; split; first by Simp.r; rewrite /= mulrBr mulrCA mulrA dotmulvZ.
apply/eqP; Simp.r; rewrite 2!scalerDr scalerA mulrC -scalerA -!addrA.
by congr (_ + _); rewrite linearZr_LR /= scalerA.
Qed.
Canonical quat_algType := Eval hnf in AlgType _ (quat R) quatAr.

Lemma quat_algE x : x%:q = x%:A.
Proof. by apply/eqP; rewrite eq_quat //=; Simp.r. Qed.

Definition conjq (a : quat R) := nosimpl (mkQuat (a.1) (- a.2)).
Canonical Conjugate_quaternion := @Build_Conjugate (quat R) conjq.

Lemma conjq_def (x : quat R) : x^*q = mkQuat x.1 (- x.2).
Proof. by case: x. Qed.

Lemma conjq_linear : linear (@conjugate_op_nosimpl Conjugate_quaternion).
Proof.
move=> k /= x y; rewrite !conjq_def /= scaleqE addqE /addq /=; Simp.r.
by rewrite linearN /= linearD.
Qed.

Canonical conjq_is_additive := Additive conjq_linear.
Canonical conjq_is_linear := AddLinear conjq_linear.

Lemma conjqI (a : quat R) : (a ^*q) ^*q = a.
Proof. by rewrite conjq_def; case: a => x1 x2 /=; rewrite opprK. Qed.

Lemma conjq0 : (0%:v)^*q = 0.
Proof. by rewrite conjq_def oppr0. Qed.

Lemma conjq_comm (a : quat R) : a^*q * a = a * a^*q.
Proof.
apply/eqP; rewrite eq_quat /=.
do ! rewrite (linearNl,linearNr,liexx,dotmulvN,dotmulNv,subr0,opprK,
              scaleNr,scalerN,eqxx) /=.
by rewrite addrC.
Qed.

Lemma conjq_addMC (a b : quat R) : a * b + (a * b)^*q  = b * a + (b * a) ^*q.
Proof.
case: a => a1 a2; case: b => b1 b2; congr mkQuat => /=.
  by rewrite [b1 * _]mulrC [b2 *d _]dotmulC.
rewrite !opprD !addrA [_ + a1 *:b2]addrC -!addrA; congr (_ + (_ + _)).
by rewrite [LHS]addrC [RHS]addrC !addrA !subrK addrC.
Qed.

Lemma realq_conjD (a : quat R) : a + a^*q \is realq R.
Proof.  by case: a => [a1 a0]; rewrite addqE /addq /= subrr qualifE. Qed.

Lemma realq_conjM (a : quat R) : a * a^*q \is realq R.
Proof.
case: a => [a1 a0].
rewrite mulqE /mulq /= scalerN linearN /=.
by rewrite liexx subr0 [- _ + _]addrC subrr qualifE.
Qed.

Lemma conjq_comm2 (a b : quat R) :
  b^*q * a + a^*q * b = a * b^*q + b * a^*q.
Proof.
apply: (addIr (a * a ^*q + b * b ^*q)).
rewrite [RHS]addrAC !addrA -mulrDr -[RHS]addrA -mulrDr -mulrDl -linearD /=.
rewrite addrC !addrA -conjq_comm -mulrDr -addrA -conjq_comm -mulrDr -mulrDl.
rewrite -linearD /= [b + a]addrC.
by apply: conjq_comm.
Qed.

Lemma conjqM (a b : quat R) : (a * b)^*q = b^*q * a^*q.
Proof.
case: a b => [a0 a1] [b0 b1] /=.
rewrite 2!conjq_def /= mulqE /mulq /= mulrC dotmulC dotmulvN dotmulNv opprK;
    congr mkQuat.
by rewrite 2!opprD 2!scalerN linearN /= -(lieC a1) linearN
           /= -2!scaleNr -addrA addrCA addrA.
Qed.

Lemma quat_realC (x : R) : (x%:q)^*q = x%:q.
Proof. by congr mkQuat; rewrite /= oppr0. Qed.

Lemma quat_vectC (x : 'rV_3) : (x%:v)^*q = -(x%:v).
Proof. by congr mkQuat; rewrite /= oppr0. Qed.

End quaternion.

Arguments pureq {R}.
Arguments realq {R}.


Section quaternion1.
Variable R : rcfType.

Definition sqrq (a : quat R) := a.1 ^+ 2 + norm (a.2) ^+ 2.

Lemma sqrq0 : sqrq 0 = 0. Proof. by rewrite /sqrq norm0 expr0n add0r. Qed.

Lemma sqrq_ge0 x : 0 <= sqrq x. Proof. by rewrite addr_ge0 // sqr_ge0. Qed.

Lemma sqrq_eq0 a : (sqrq a == 0) = (a == 0).
Proof.
rewrite /sqrq paddr_eq0 ?sqr_ge0// !sqrf_eq0 norm_eq0 -xpair_eqE.
by rewrite -surjective_pairing.
Qed.

Lemma sqrqN (a : quat R) : sqrq (- a) = sqrq a.
Proof. by rewrite /sqrq /= normN sqrrN. Qed.

Lemma sqrq_conj (a : quat R) : sqrq (a^*q) = sqrq a.
Proof. by rewrite /sqrq normN. Qed.

Lemma conjqP (a : quat R) : a * a^*q = (sqrq a)%:q.
Proof.
rewrite /mulq /=; congr mkQuat.
  by rewrite /= dotmulvN dotmulvv opprK -expr2.
by rewrite scalerN addNr add0r linearNr liexx oppr0.
Qed.

Lemma conjqZ k (q : quat R) : (k *: q) ^*q = k *: q ^*q.
Proof. by congr mkQuat; rewrite /= scalerN. Qed.

Lemma conjqE (a : quat R) :
  a^*q = - (1 / 2%:R) *: (a + `i * a * `i + `j * a * `j + `k * a * `k).
Proof.
apply/eqP; rewrite eq_quat; apply/andP; split; apply/eqP.
  rewrite [in LHS]/= scaleqE /=.
  rewrite !(mul0r,mulr0,addr0) scale0r !add0r !dotmulDl.
  rewrite dotmulZv dotmulvv normeE expr1n mulr1 dotmulC
          dot_crossmulC liexx dotmul0v addr0.
  rewrite subrr add0r dotmulZv dotmulvv normeE expr1n mulr1
          dotmulC dot_crossmulC liexx.
  rewrite dotmul0v addr0 dotmulZv dotmulvv normeE expr1n mulr1
          opprD addrA dotmulC dot_crossmulC.
  rewrite liexx dotmul0v subr0 -opprD mulrN mulNr
          opprK -mulr2n -(mulr_natl (a.1)) mulrA.
  by rewrite div1r mulVr ?mul1r // unitfE pnatr_eq0.
rewrite /= !(mul0r,scale0r,add0r,addr0).
rewrite [_ *v 'e_0]lieC /= ['e_0 *v _]linearD /= ['e_0 *v _]linearZ /= liexx.
rewrite scaler0 add0r double_crossmul dotmulvv normeE expr1n scale1r.
rewrite [_ *v 'e_1]lieC /= ['e_1 *v _]linearD /= ['e_1 *v _]linearZ /= liexx.
rewrite scaler0 add0r double_crossmul dotmulvv normeE expr1n scale1r.
rewrite [_ *v 'e_2%:R]lieC /= ['e_2%:R *v _]linearD /=
        ['e_2%:R *v _]linearZ /= liexx.
rewrite scaler0 add0r double_crossmul dotmulvv normeE expr1n scale1r.
rewrite [X in _ = - _ *: X](_ : _ = 2%:R *:a.2).
  by rewrite scalerA mulNr div1r mulVr ?unitfE ?pnatr_eq0 // scaleN1r.
rewrite !opprB (addrCA _ a.2) addrA -mulr2n scaler_nat -[RHS]addr0 -3!addrA;
    congr (_ + _).
do 3 rewrite (addrCA _ a.2).
do 2 rewrite addrC -!addrA.
rewrite -opprB (scaleNr _ 'e_0) opprK -mulr2n addrA -mulr2n.
rewrite addrC addrA -opprB scaleNr opprK -mulr2n.
rewrite opprD.
rewrite (addrCA (- _ *: 'e_2%:R)).
rewrite -opprB scaleNr opprK -mulr2n.
rewrite -!mulNrn -3!mulrnDl -scaler_nat.
apply/eqP; rewrite scalemx_eq0 pnatr_eq0 /=.
rewrite addrA addrC eq_sym -subr_eq add0r opprB opprD 2!opprK.
rewrite !['e__ *d _]dotmulC !dotmul_delta_mx /=.
by rewrite addrA addrAC -addrA addrC [X in _ == X]vec3E.
Qed.

Lemma conjq_scalar (a : quat R) : (a.1)%:q = (1 / 2%:R) *: (a + a^*q).
Proof.
case: a => a0 a1.
rewrite /conjq /= addqE /addq /= subrr quat_realD scalerDr -scalerDl.
by rewrite -mulr2n -mulr_natr div1r mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Lemma conjq_vector (a : quat R) : (a.2)%:v = (1 / 2%:R) *: (a - a^*q).
Proof.
case: a => a0 a1.
rewrite /conjq /= addqE /addq /= subrr opprK quat_vectD scalerDr -scalerDl.
by rewrite -mulr2n -mulr_natr div1r mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Definition invq a := (1 / sqrq a) *: (a ^*q).

Definition unitq : pred (quat R) := [pred a | a != 0%:q].

Lemma mulVq : {in unitq, left_inverse 1 invq (@mulq R)}.
Proof.
move=> a; rewrite inE /= => a0.
rewrite /invq -mulqE -quatAl conjq_comm conjqP.
by rewrite -quat_realZ mul1r mulVf // sqrq_eq0.
Qed.

Lemma mulqV : {in unitq, right_inverse 1 invq (@mulq R)}.
Proof.
move=> a; rewrite inE /= => a0.
by rewrite /invq -mulqE -quatAr conjqP -quat_realZ mul1r mulVf // sqrq_eq0.
Qed.

Lemma quat_integral (x y : quat R) : (x * y == 0) = ((x == 0) || (y == 0)).
Proof.
case: (x =P 0) => [->|/eqP xNZ] /=; first by rewrite mul0r eqxx.
apply/eqP/eqP => [xyZ|->]; last by rewrite mulr0.
by rewrite -[y]mul1r -(@mulVq x) // -mulrA xyZ mulr0.
Qed.

Lemma unitqP a b : b * a = 1 /\ a * b = 1 -> unitq a.
Proof.
move=> [ba1 ab1]; rewrite /unitq inE; apply/eqP => x0.
move/esym: ab1; rewrite x0 mul0r.
apply/eqP; exact: oneq_neq0.
Qed.

Lemma invq0id : {in [predC unitq], invq =1 id}.
Proof.
move=> a; rewrite !inE negbK => /eqP ->.
by rewrite /invq /= conjq0 scaler0.
Qed.

Definition quat_UnitRingMixin := UnitRingMixin mulVq mulqV unitqP invq0id.
Canonical quat_unitRing := UnitRingType (quat R) quat_UnitRingMixin.

Lemma invqE a : a^-1 = invq a. Proof. by done. Qed.

Definition normq (a : quat R) : R := Num.sqrt (sqrq a).

Lemma normq0 : normq 0 = 0.
Proof. by rewrite /normq /sqrq expr0n /= norm0 add0r expr0n sqrtr0. Qed.

Lemma normqc a : normq a^*q = normq a.
Proof. by rewrite /normq /sqrq /= normN. Qed.

Lemma normqE a : (normq a ^+ 2)%:q = a^*q * a.
Proof.
rewrite -normqc /normq sqr_sqrtr; last by rewrite /sqrq addr_ge0 // sqr_ge0.
by rewrite -conjqP conjqI.
Qed.

Lemma normq_ge0 a : 0 <= normq a.
Proof. by apply sqrtr_ge0. Qed.

Lemma normq_eq0 a : (normq a == 0) = (a == 0).
Proof. by rewrite /normq -{1}sqrtr0 eqr_sqrt ?sqrq_ge0// sqrq_eq0. Qed.

Lemma normqM (Q P : quat R) : normq (Q * P) = normq Q * normq P.
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?normq_ge0 //; last first.
  by rewrite mulr_ge0 // normq_ge0.
rewrite -quat_scalarE normqE conjqM -mulrA (mulrA (Q^*q)) -normqE.
rewrite quat_algE mulr_algl -scalerAr exprMn quat_realM.
by rewrite (normqE P) -mulr_algl quat_algE.
Qed.

Lemma normqZ (k : R) (q : quat R) : normq (k *: q) = `|k| * normq q.
Proof.
by rewrite /normq /sqrq /= normZ 2!exprMn sqr_normr -mulrDr sqrtrM ?sqr_ge0 //
           sqrtr_sqr.
Qed.

Lemma normqV (q : quat R) : normq (q^-1) = normq q / sqrq q.
Proof.
rewrite invqE /invq normqZ ger0_norm; last first.
  by rewrite divr_ge0 // ?ler01 // /sqrq addr_ge0 // sqr_ge0.
by rewrite normqc mulrC mul1r.
Qed.

Definition normQ Q := (normq Q)%:q.

Lemma normQ_eq0 x : (normQ x == 0) = (x == 0).
Proof. by rewrite /normQ quat_scalarE normq_eq0. Qed.

Definition normalizeq (q : quat R) : quat R := 1 / normq q *: q.

Lemma normalizeq1 (q : quat R) : q != 0 -> normq (normalizeq q) = 1.
Proof.
move=> q0.
rewrite /normalizeq normqZ normrM normr1 mul1r normrV; last first.
  by rewrite unitfE normq_eq0.
by rewrite ger0_norm ?normq_ge0 // mulVr // unitfE normq_eq0.
Qed.

Definition lequat (Q P : quat R) :=
  let: mkQuat Q1 Q2 := Q in let: mkQuat P1 P2 := P in
  (Q2 == P2) && (Q1 <= P1).

Lemma lequat_normD x y : lequat (normQ (x + y)) (normQ x + normQ y).
Proof.
rewrite /lequat /= add0r eqxx andTb /normq /sqrq !sqr_norm !sum3E /= !mxE.
pose X := nth 0 [:: x.1; x _i; x _j; x _k].
pose Y := nth 0 [:: y.1; y _i; y _j; y _k].
suff: Num.sqrt (\sum_(i < 4) (X i + Y i)^+2) <=
      Num.sqrt (\sum_(i < 4) (X i) ^+ 2) + Num.sqrt (\sum_(i < 4) (Y i) ^+ 2).
  by rewrite !sum4E /X /Y /= !addrA.
have sqr_normE (x1 : R) : `|x1| ^+2 = x1 ^+ 2.
  by case: (ltrgt0P x1); rewrite ?sqrrN // => ->.
have ler_mul_norm (x1 y1 : R) : x1 * y1 <= `|x1| * `|y1|.
  rewrite {1}(numEsign x1) {1}(numEsign y1) mulrAC mulrA -signr_addb.
  rewrite -mulrA [_ * `|x1|]mulrC.
  case: (_ (+) _); rewrite !(expr0, expr1, mulNr, mul1r) //.
  rewrite -subr_gte0 opprK -mulr2n; apply: mulrn_wge0.
  by apply: mulr_ge0; apply: normr_ge0.
apply: le_trans (_ : Num.sqrt (\sum_(i < 4) (`|X i| + `|Y i|) ^+ 2) <= _).
  rewrite -ler_sqr ?nnegrE; try by apply: sqrtr_ge0.
  rewrite !sqr_sqrtr; try by apply: sumr_ge0 => i _; apply: sqr_ge0.
  apply: ler_sum => i _; rewrite !sqrrD.
  by rewrite !sqr_normE; do ! apply: ler_add => //.
rewrite -ler_sqr ?nnegrE; last 2 first.
- by apply: sqrtr_ge0.
- by apply: addr_ge0; apply: sqrtr_ge0.
rewrite [in X in _ <= X]sqrrD !sqr_sqrtr;
    try by apply: sumr_ge0 => i ; rewrite sqr_ge0.
under eq_bigr do rewrite sqrrD.
rewrite 2!big_split /= sumrMnl.
under [X in _ <= X + _ + _]eq_bigr do rewrite -sqr_normE.
under [X in _ <= _ + _ X * _ *+2  + _]eq_bigr do rewrite -sqr_normE.
under [X in _ <= _ + _ + X]eq_bigr do rewrite -sqr_normE.
under [X in _ <= _ + _ * _ X *+2  + _]eq_bigr do rewrite -sqr_normE.
do 2 (apply: ler_add => //); rewrite ler_muln2r /=.
rewrite -ler_sqr ?nnegrE; last 2 first.
- by apply: sumr_ge0 => i _; apply: mulr_ge0; apply: normr_ge0.
- by apply: mulr_ge0; apply: sqrtr_ge0.
rewrite exprMn !sqr_sqrtr; last 2 first.
- by apply: sumr_ge0=> i _; apply: sqr_ge0.
- by apply: sumr_ge0=> i _; apply: sqr_ge0.
(* This is Cauchy Schwartz *)
rewrite -[_ <= _]orFb -[false]/(2 == 0)%nat -ler_muln2r.
pose u := \sum_(i < 4) \sum_(j < 4) (`|X i| * `|Y j| - `|X j| * `|Y i|) ^+ 2.
set z1 := \sum_(i < _) _; set z2 := \sum_(i < _) _; set z3 := \sum_(i < _) _.
suff ->: z2 * z3 *+ 2 = z1 ^+ 2 *+ 2 + u.
  rewrite -{1}(addr0 (_ *+ 2)).
  apply: ler_add => //.
  by apply: sumr_ge0 => i _; apply: sumr_ge0 => j _; apply: sqr_ge0.
under [X in _ = _ + X]eq_bigr do
  (under eq_bigr do (rewrite sqrrB !exprMn); rewrite !(sumrN, big_split));
  rewrite !(sumrN, big_split, addrA) /=.
under eq_bigr do rewrite -mulr_sumr; rewrite -mulr_suml -/z2 -/z3.
have mswap (a b c d : R) : a * b * (c * d) = (c * b) * (a * d).
  by rewrite mulrC mulrAC [a * _]mulrC !mulrA.
under [X in _ = _ - (X + _) + _]eq_bigr do
  (under eq_bigr do rewrite mswap; rewrite -mulr_suml);
  rewrite -mulr_sumr -expr2 -/z1.
under [X in _ = _ - (_ + X) + _]eq_bigr do
  (under eq_bigr do rewrite mswap; rewrite -mulr_suml);
  rewrite -mulr_sumr -expr2 -/z1 -mulr2n.
under [X in _ = _ + X]eq_bigr do rewrite -mulr_suml;
  rewrite -mulr_sumr -/z2 -/z3.
by rewrite [_ *+ 2 + _]addrC addrK mulr2n.
Qed.

Definition ltquat (Q P : quat R) :=
  let: mkQuat Q1 Q2 := Q in let: mkQuat P1 P2 := P in
  (Q2 == P2) && (Q1 < P1).

Lemma ltquat0_add x y : ltquat 0 x -> ltquat 0 y -> ltquat 0 (x + y).
Proof.
case: x => x0 x1; case: y => y0 y1 /andP[/eqP<- x0P] /andP[/eqP<- u0P] /=.
by rewrite addr0 eqxx addr_gt0.
Qed.

Lemma ge0_lequat_total x y :
  lequat 0 x -> lequat 0 y -> lequat x y || lequat y x.
Proof.
case: x => x0 x1; case: y => y0 y1 /andP[/eqP<- x0P] /andP[/eqP<- y0P] /=.
case:  (lerP x0 y0); rewrite eqxx //=.
by apply: ltW.
Qed.

Lemma normQM x y : normQ (x * y) = normQ x * normQ y.
Proof. by rewrite {1}/normQ normqM quat_realM. Qed.

Lemma lequat_def x y : lequat x y = (normQ (y - x) == y - x).
Proof.
case: x => x0 x1; case: y => y0 y1; rewrite /normQ /normq  /sqrq /=.
apply/idP/idP.
  case/andP => /eqP<- x0Ly0.
  apply/eqP; congr mkQuat; rewrite ?subrr ?expr0n ?addr0 //=.
  rewrite norm0 expr0n addr0 sqrtr_sqr.
  by apply/eqP; rewrite eqr_norm_id subr_ge0.
case/eqP => /eqP H H1.
move: (sym_equal H1) H => /subr0_eq->; rewrite eqxx /=.
by rewrite subrr norm0 expr0n addr0 sqrtr_sqr eqr_norm_id subr_ge0.
Qed.

Lemma ltquat_def x y : ltquat x y = (y != x) && lequat x y.
Proof.
case: x => x0 x1; case: y => y0 y1 /=.
apply/andP/and3P => [[/eqP<- x0Ly0] | ].
  split=> //.
    by apply/negP; case/eqP => y0E; rewrite y0E // ltxx in x0Ly0.
  by apply: ltW.
rewrite eq_quat negb_and /= => [] [/orP[y0Dx0 | y1Dx1] x1Ey1 x0Ly0];
  split => //.
  by rewrite lt_neqAle eq_sym y0Dx0.
by rewrite eq_sym x1Ey1 in y1Dx1.
Qed.

Fail Definition quat_POrderedMixin :=
  NumMixin lequat_normD ltquat0_add eq0_normQ ge0_lequat_total
           normQM lequat_def ltquat_def.
Fail Canonical Structure quat_numDomainType :=
  NumDomainType _ quat_POrderedMixin.

Definition uquat := [qualify x : quat R | normq x == 1].
Fact uquat_key : pred_key uquat. Proof. by []. Qed.
Canonical uquat_keyed := KeyedQualifier uquat_key.

Lemma uquatE (q : quat R) : (q \is uquat) = (sqrq q == 1).
Proof. by rewrite qualifE /normq -{1}sqrtr1 eqr_sqrt // ?sqrq_ge0// ler01. Qed.

Lemma muluq_proof a b : a \is uquat -> b \is uquat -> a * b \is uquat.
Proof. rewrite 3!qualifE => /eqP Hq /eqP Hp; by rewrite normqM Hq Hp mulr1. Qed.

Lemma invq_uquat a : a \is uquat -> a^-1 = a^*q.
Proof.
rewrite uquatE => /eqP Hq; by rewrite invqE /invq Hq invr1 mul1r scale1r.
Qed.

Lemma invuq_proof a : a \is uquat -> normq (a^-1) == 1.
Proof. by move=> ua; rewrite invq_uquat // normqc. Qed.

Lemma cos_atan_uquat q : q \is uquat -> q \isn't pureq ->
  let a := atan (norm q.2 / q.1) in cos a ^+ 2 = q.1 ^+ 2.
Proof.
move=> nq q00 a.
rewrite /a cos_atan exprMn expr1n mul1r.
have /divrr <- : q.1 ^+ 2 \in GRing.unit by rewrite unitfE sqrf_eq0.
rewrite uquatE /sqrq in nq.
rewrite expr_div_n -mulrDl (eqP nq) sqrtrM ?ler01 // sqrtr1 mul1r.
by rewrite -exprVn sqrtr_sqr normrV ?unitfE // invrK sqr_normr.
Qed.

Lemma sin_atan_uquat q : q \is uquat -> q \isn't pureq ->
  let a := atan (norm q.2 / q.1) in sin a ^+ 2 = norm q.2 ^+ 2.
Proof.
move=> nq q00 a.
rewrite /a sqr_sin_atan.
have /divrr <- : q.1 ^+ 2 \in GRing.unit by rewrite unitfE sqrf_eq0.
rewrite uquatE /sqrq in nq.
rewrite expr_div_n -mulrDl.
by rewrite (eqP nq) mul1r invrK -mulrA mulVr ?mulr1 // unitrX // unitfE.
Qed.

End quaternion1.
Arguments uquat {R}.

Section conjugation.
Variable R : rcfType.
Implicit Types (a : quat R) (v : 'rV[R]_3).

Definition conjugation x v : quat R := x * v%:v * x^*q.

Lemma conjugationE x v : conjugation x v =
  ((x.1 ^+ 2 - norm x.2 ^+ 2) *: v +
   ((x.2 *d v) *: x.2) *+ 2 +
   (x.1 *: (x.2 *v v)) *+ 2)%:v.
Proof.
case: x => x1 x2 /=; rewrite /conjugation /= /conjq /= mulqE /mulq /=.
rewrite mulr0 scale0r addr0 add0r; congr mkQuat.
  rewrite dotmulvN opprK dotmulDl (dotmulC (_ *v _) x2) dot_crossmulC.
  by rewrite liexx dotmul0v addr0 dotmulZv mulNr mulrC dotmulC addrC subrr.
rewrite scalerDr scalerA -expr2 addrCA scalerBl -!addrA; congr (_ + _).
rewrite [in X in _ + X = _]linearN /= (lieC _ x2) linearD /= opprK.
rewrite linearZ /= (addrA (x1 *: _ )) -mulr2n.
rewrite [in LHS]addrCA 2![in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite scalerN scaleNr opprK -addrA addrCA; congr (_ + _).
by rewrite double_crossmul [in RHS]addrC dotmulvv.
Qed.

Lemma conjugation_is_pure x v : conjugation x v \is pureq.
Proof. by rewrite conjugationE qualifE. Qed.

Lemma conjugation_axis x k : x \is uquat ->
  conjugation x (k *: x.2) = (k *: x.2)%:v.
Proof.
rewrite uquatE /sqrq => /eqP q_is_uquat; rewrite conjugationE.
rewrite [in X in (_ + _ + X)%:v = _]linearZ /= liexx 2!scaler0 mul0rn addr0.
rewrite dotmulvZ dotmulvv scalerBl !scalerA (mulrC (norm _ ^+ 2)) mulr2n addrA.
by rewrite subrK -scalerDl mulrC -mulrDr q_is_uquat mulr1.
Qed.

End conjugation.

Section polar_coordinates.
Variable R : rcfType.
Implicit Types (x : quat R) (v : 'rV[R]_3) (a : angle R).

Definition quat_of_polar a v := mkQuat (cos a) (sin a *: v).

Lemma quat_of_polar01 : quat_of_polar 0 'e_1 = 1%:q.
Proof. by rewrite /quat_of_polar /= cos0 sin0 scale0r. Qed.

Lemma quat_of_polarpi1 : quat_of_polar pi 'e_1 = (-1)%:q.
Proof. by rewrite /quat_of_polar cospi sinpi scale0r. Qed.

Lemma quat_of_polarpihalf v : quat_of_polar (pihalf R) v = v%:v.
Proof. by rewrite /quat_of_polar cos_pihalf sin_pihalf scale1r. Qed.

Lemma uquat_of_polar a v (v1 : norm v = 1) : quat_of_polar a v \is uquat.
Proof.
by rewrite qualifE /quat_of_polar /normq /sqrq /= normZ v1 mulr1 sqr_normr
           cos2Dsin2 sqrtr1.
Qed.

Lemma conjugation_quat_of_polarii v a : norm v = 1 ->
  (conjugation (quat_of_polar a v) v).2 = v.
Proof.
move=> v1; rewrite conjugationE /= normZ exprMn v1 expr1n mulr1 sqr_normr.
rewrite dotmulZv dotmulvv v1 expr1n mulr1 linearZl_LR liexx 2!scaler0 mul0rn.
rewrite addr0 scalerA -expr2 mulr2n scalerBl addrA subrK -scalerDl cos2Dsin2.
by rewrite scale1r.
Qed.

Local Open Scope frame_scope.

Lemma conjugation_quat_of_polarij v a : norm v = 1 ->
  (conjugation (quat_of_polar a v) (Base.frame v)|,1).2 =
  cos (a *+ 2) *: (Base.frame v)|,1 + sin (a *+ 2) *: (Base.frame v)|,2%:R.
Proof.
move=> v1; rewrite conjugationE /= normZ v1 mulr1 sqr_normr dotmulZv.
have v0 : v != 0 by rewrite -norm_eq0 v1 oner_neq0.
move: (noframe_idotj (Base.frame v)); rewrite Base.frame0E// normalizeI// => ->.
rewrite mulr0 scale0r mul0rn addr0 linearZl_LR /=.
move: (frame_icrossj (Base.frame v)); rewrite Base.frame0E// normalizeI// => ->.
rewrite scalerA [in RHS]mulr2n cosD sinD -!expr2; congr (_ + _).
by rewrite (mulrC (sin a)) -mulr2n -scalerMnl.
Qed.

Lemma conjugation_quat_of_polarik v a : norm v = 1 ->
  (conjugation (quat_of_polar a v) (Base.frame v)|,2%:R).2 =
  - sin (a *+ 2) *: (Base.frame v)|,1 + cos (a *+ 2) *: (Base.frame v)|,2%:R.
Proof.
move=> v1; rewrite conjugationE /= normZ v1 mulr1 sqr_normr dotmulZv.
have v0 : v != 0 by rewrite -norm_eq0 v1 oner_neq0.
move: (noframe_idotk (Base.frame v)); rewrite Base.frame0E// normalizeI// => ->.
rewrite mulr0 scale0r mul0rn addr0 linearZl_LR /=.
move: (frame_icrossk (Base.frame v)); rewrite Base.frame0E// normalizeI// => ->.
rewrite 2!scalerN scalerA sinD cosD -!expr2 addrC scaleNr; congr (_ + _).
by rewrite (mulrC (sin a)) -mulr2n -scalerMnl mulNrn.
Qed.

Definition polar_of_quat x : ('rV_3 * angle R)%type :=
  if x.2 == 0 then
    if x.1 == 1 then ('e_1, 0) else ('e_1, pi)
  else if x.1 == 0 then (x.2, pihalf R) else
  let: u := normalize x.2 in
  let: a := atan (norm x.2 / x.1) in
  if 0 < x.1 then (u, a) else (u, a + pi).

Lemma polar_of_quat0 : polar_of_quat 0 = ('e_1, pi).
Proof. by rewrite /polar_of_quat eqxx eq_sym oner_eq0. Qed.

Lemma norm_polar_of_quat x : x \is uquat ->
  let: (u, _) := polar_of_quat x in norm u = 1.
Proof.
case: x => a0 a1; rewrite /= qualifE /polar_of_quat /normq /sqrq /=.
have [/eqP ->|a10] := ifPn; first by case: ifPn; rewrite norm_delta_mx.
case: (sgzP a0) => [-> /eqP| |]; try by rewrite norm_normalize.
by rewrite expr0n add0r sqrtr_sqr ger0_norm // norm_ge0.
Qed.

Lemma polar_of_quatK x : x \is uquat ->
  let: (u, a) := polar_of_quat x in x = quat_of_polar a u.
Proof.
case: x => a0 a1; rewrite /= qualifE /polar_of_quat /normq /sqrq /=.
have [->|/eqP a1N u1] := a1 =P 0.
  rewrite norm0 expr0n addr0 sqrtr_sqr; have [?/eqP->|?|_] := ltrgt0P a0.
  - by rewrite eqxx quat_of_polar01.
  - by rewrite eqr_oppLR => /eqP ->; rewrite Neqxx oner_eq0 quat_of_polarpi1.
  - by rewrite eq_sym oner_eq0.
move: u1; have [-> _|a0P /eqP u1 |a0N /eqP u1] := sgzP a0.
- by rewrite quat_of_polarpihalf.
- congr mkQuat.
    by rewrite cos_atan sqrtr_1sqr2 ?gt_eqF// gtr0_norm// invrK mul1r.
  rewrite sin_atan sqrtr_1sqr2 ?gt_eqF// gtr0_norm// invrK -mulrA.
  by rewrite mulVf ?gt_eqF// mulr1 norm_scale_normalize.
- congr mkQuat.
    rewrite cosDpi cos_atan sqrtr_1sqr2 ?lt_eqF// mul1r invrK ltr0_norm//.
    by rewrite opprK.
  rewrite sinDpi sin_atan sqrtr_1sqr2// ?lt_eqF// ltr0_norm// 2!invrN mulrN.
  by rewrite invrK opprK -mulrA mulVf ?lt_eqF// mulr1 norm_scale_normalize.
Qed.

Definition quat_rot x : 'rV[R]_3 -> 'rV[R]_3 := snd \o locked (conjugation x).

Lemma quat_rot_is_linear x : linear (quat_rot x).
Proof.
move=> k u v.
rewrite /quat_rot /=; unlock; rewrite !conjugationE.
rewrite scalerDr scalerA (mulrC _ k) -scalerA.
rewrite 2![in RHS]scalerDr -2![in LHS]addrA -3![in RHS]addrA; congr (_ + _).
rewrite [in RHS]addrA [in RHS]addrCA -[in RHS]addrA; congr (_ + _).
rewrite dotmulDr scalerDl mulrnDl -addrA addrCA; congr (_ + _).
rewrite dotmulvZ -scalerA scalerMnr -addrA; congr (_ + _).
rewrite linearD /= scalerDr mulrnDl; congr (_ + _).
by rewrite linearZ /= scalerA mulrC -scalerA -scalerMnr.
Qed.
Canonical quat_rot_linear x := Linear (quat_rot_is_linear x).

Lemma quat_rot_isRot_polar v a : norm v = 1 ->
  isRot (a *+2) v [linear of quat_rot (quat_of_polar a v)].
Proof.
move=> v1 /=; apply/isRotP; split; rewrite /= /quat_rot /=; unlock.
- by rewrite conjugation_quat_of_polarii.
- by rewrite conjugation_quat_of_polarij.
- by rewrite conjugation_quat_of_polarik.
Qed.

Lemma quat_rot_isRot x : x \is uquat ->
  let: (u, a) := polar_of_quat x in
  isRot (a *+ 2) u [linear of quat_rot x].
Proof.
move=> aH /=.
have := norm_polar_of_quat aH.
have := polar_of_quatK aH.
case: (polar_of_quat x) => u theta -> u1.
by apply: quat_rot_isRot_polar.
Qed.

End polar_coordinates.

Section dual_number.
Variable R : ringType.
Implicit Types r : R.
Record dual := mkDual {ldual : R ; rdual : R}.
Implicit Types x y : dual.

Local Notation "x +ɛ* y" := (mkDual x y).
Local Notation "x -ɛ* y" := (mkDual x (- y)).

Definition dual0 : dual := 0 +ɛ* 0.
Definition dual1 : dual := 1 +ɛ* 0.

Coercion pair_of_dual x : R * R := let: mkDual x1 x2 := x in (x1, x2).

Let dual_of_pair (z : R * R) := let: (z1, z2) := z in z1 +ɛ* z2.

Lemma dual_of_pairK : cancel pair_of_dual dual_of_pair.
Proof. by case. Qed.

Definition dual_eqMixin := CanEqMixin dual_of_pairK.
Canonical Structure dual_eqType := EqType dual dual_eqMixin.
Definition dual_choiceMixin := CanChoiceMixin dual_of_pairK.
Canonical Structure dual_choiceType := ChoiceType dual dual_choiceMixin.

Definition oppd x := (- x.1) +ɛ* (- x.2).

Definition addd x y := (x.1 + y.1) +ɛ* (x.2 + y.2).

Definition muld x y := x.1 * y.1 +ɛ* (x.1 * y.2 + x.2 * y.1).

Definition deps : 'M[R]_2 :=
  \matrix_(i < 2, j < 2) ((i == 0) && (j == 1))%:R.

Lemma deps2 : deps ^+2 = 0.
Proof.
rewrite expr2; apply/matrixP => i j.
by rewrite !mxE sum2E !mxE /= mulr0 addr0 -ifnot01 eqxx andbF mul0r.
Qed.

Definition mat_of_dual x : 'M[R]_2 := x.1%:M + x.2 *: deps.

Definition dual_of_mat (M : 'M[R]_2) := (M 0 0) +ɛ* (M 0 1).

Lemma adddE x y : addd x y = dual_of_mat (mat_of_dual x + mat_of_dual y).
Proof.
rewrite /addd /dual_of_mat /mat_of_dual /= !mxE; congr mkDual.
by rewrite !eqxx !(mulr1n,andbF,mulr1,mulr0,addr0).
by rewrite !mulr0n !eqxx !mulr1 !add0r.
Qed.

Lemma muldE x y : muld x y = dual_of_mat (mat_of_dual x * mat_of_dual y).
Proof.
rewrite /muld /dual_of_mat /mat_of_dual /= !mxE !sum2E !mxE; congr mkDual.
by rewrite !eqxx !(mulr0n,mulr1n,mulr0,mulr1,addr0).
by rewrite !eqxx !(mulr0n,mulr1n,mulr0,add0r,addr0,mulr1).
Qed.

Lemma adddA : associative addd.
Proof. by move=> x y z; rewrite /addd 2!addrA. Qed.

Lemma adddC : commutative addd.
Proof. by move=> x y; rewrite /addd addrC [in X in _ +ɛ* X = _]addrC. Qed.

Lemma add0d : left_id dual0 addd.
Proof. by move=> x; rewrite /addd 2!add0r; case: x. Qed.

Lemma addNd : left_inverse dual0 oppd addd.
Proof. by move=> x; rewrite /addd 2!addNr. Qed.

Definition dual_ZmodMixin := ZmodMixin adddA adddC add0d addNd.
Canonical dual_ZmodType := ZmodType dual dual_ZmodMixin.

Lemma addd_def x y : x + y = (x.1 + y.1) +ɛ* (x.2 + y.2).
Proof. by []. Qed.

Lemma muldA : associative muld.
Proof.
move=> x y z; rewrite /muld; congr mkDual; first by rewrite mulrA.
by rewrite mulrDr mulrDl !mulrA addrA.
Qed.

Lemma mul1d : left_id dual1 muld.
Proof. by case=> x0 x1; rewrite /muld 2!mul1r mul0r addr0. Qed.

Lemma muld1 : right_id dual1 muld.
Proof. by case=> x0 x1; rewrite /muld 2!mulr1 mulr0 add0r. Qed.

Lemma muldDl : left_distributive muld addd.
Proof.
move=> x y z; rewrite /muld /addd mulrDl; congr mkDual.
by rewrite mulrDl -!addrA; congr (_ + _); rewrite mulrDl addrCA.
Qed.

Lemma muldDr : right_distributive muld addd.
Proof.
move=> x y z; rewrite /muld /addd mulrDr; congr mkDual.
by rewrite mulrDr -!addrA; congr (_ + _); rewrite mulrDr addrCA.
Qed.

Lemma oned_neq0 : dual1 != 0 :> dual.
Proof. by apply/eqP; case; apply/eqP; exact: oner_neq0. Qed.

Definition dual_RingMixin := RingMixin muldA mul1d muld1 muldDl muldDr oned_neq0.
Canonical Structure dual_Ring := Eval hnf in RingType dual dual_RingMixin.

Lemma muld_def x y : x * y = x.1 * y.1 +ɛ* (x.1 * y.2 + x.2 * y.1).
Proof. by []. Qed.

Definition scaled r x := r * x.1 +ɛ* (r * x.2).

Lemma scaledA a b x : scaled a (scaled b x) = scaled (a * b) x.
Proof. by rewrite /scaled /=; congr mkDual; rewrite mulrA. Qed.

Lemma scaled1 : left_id 1 scaled.
Proof. by rewrite /left_id /scaled /=; case=> ? ? /=; rewrite !mul1r. Qed.

Lemma scaledDr : @right_distributive R dual scaled +%R.
Proof. by move=> r x y; rewrite /scaled /= !mulrDr. Qed.

Lemma scaledDl x : {morph (scaled^~ x : R -> dual) : a b / a + b}.
Proof. by move=> a b; rewrite /scaled !mulrDl. Qed.

Definition dual_lmodMixin := LmodMixin scaledA scaled1 scaledDr scaledDl.
Canonical dual_lmodType := Eval hnf in LmodType R dual dual_lmodMixin.

Definition conjd x := x.1 -ɛ* x.2.
Local Notation "x '^*d'" := (conjd x).

Definition duall (r : R) := r +ɛ* 0.

Local Notation "*%:dl" := duall (at level 2).
Local Notation "r %:dl" := (duall r) (at level 2).

Fact duall_is_rmorphism : rmorphism *%:dl.
Proof.
split => [p q|]; first by congr mkDual; rewrite /= subrr.
split => [p q|] //; by congr mkDual; rewrite /=; Simp.r.
Qed.
Canonical duall_rmorphism := RMorphism duall_is_rmorphism.

(* Sanity check : Taylor series for polynomial *)
Lemma dual_deriv_poly (p : {poly R}) r :
  (map_poly *%:dl p).[r +ɛ* 1] = p.[r] +ɛ* p^`().[r].
Proof.
elim/poly_ind : p => [|p b IH]; first by rewrite map_poly0 deriv0 !horner0.
rewrite !(rmorphD, rmorphM) /= map_polyX (map_polyC duall_rmorphism) /=.
rewrite derivD derivC derivM derivX; Simp.r.
rewrite !hornerMXaddC hornerD hornerMX IH; congr mkDual => /=.
by Simp.r; rewrite addrC.
Qed.

End dual_number.

Notation "a +ɛ* b" := (mkDual a b) : dual_scope.
Notation "a -ɛ* b" := (mkDual a (- b)) : dual_scope.

Section dual_comm.
Variable R : comRingType.

Fact muld_comm (p q : dual R) : p * q = q * p.
Proof.
case: p => p1 p2; case: q => q1 q2; rewrite !muld_def /=.
by rewrite addrC mulrC [p2 * _]mulrC [q2 * _]mulrC.
Qed.
Canonical dual_comRingType := Eval hnf in ComRingType (dual R) muld_comm.

End dual_comm.

Section dual_number_unit.
Variable R : unitRingType.
Local Open Scope dual_scope.
Implicit Types x y : dual R.

Definition unitd : pred (dual R) := [pred x : dual R | x.1 \is a GRing.unit].

Definition invd x :=
  if x \in unitd then x.1^-1 -ɛ* (x.1^-1 * x.2 * x.1^-1) else x.

(* NB: invd was previously written using matrices *)
Fact invdE x : x \in unitd ->
  invd x = dual_of_mat (x.1^-1%:M * (1 - deps R * x.2%:M * (x.1)^-1%:M)).
Proof.
move : x => [q r] /=; rewrite inE /= => qu; rewrite /invd inE /= qu.
by rewrite /dual_of_mat !(mxE,sum2E) /=; Simp.r.
Qed.

Lemma mulVd : {in unitd, left_inverse 1 invd *%R}.
Proof.
move=> [q r]; rewrite inE /= => qu.
by rewrite /invd inE qu muld_def /= mulNr -mulrA !mulVr// mulr1 subrr.
Qed.

Lemma muldV : {in unitd, right_inverse 1 invd *%R}.
Proof.
move=> [q r]; rewrite inE /= => qu; rewrite /invd inE qu /= muld_def /=.
by rewrite mulrN 2!mulrA divrr// mul1r addrC subrr.
Qed.

Lemma unitdP x y : y * x = 1 /\ x * y = 1 -> unitd x.
Proof. by rewrite 2!muld_def => -[[? _] [? _]]; apply/unitrP; exists y.1. Qed.

(* The inverse of a non-unit x is constrained to be x itself *)
Lemma invd0id : {in [predC unitd], invd =1 id}.
Proof. by move=> x; rewrite inE /= /invd => /negbTE ->. Qed.

Definition dual_UnitRingMixin := UnitRingMixin mulVd muldV unitdP invd0id.
Canonical dual_unitRing := UnitRingType (dual R) dual_UnitRingMixin.

End dual_number_unit.

Section dual_quaternion.
Variable R : rcfType (*realType*).
Local Open Scope dual_scope.

Definition dquat := @dual (quat_unitRing R).

Implicit Types x y : dquat.

Definition conjdq x : dquat := (x.1)^*q +ɛ* (x.2)^*q.

Canonical Conjugate_dquaternion := @Build_Conjugate (@dual (quat_unitRing R)) conjdq.

Lemma conjdq_def x : x^*q = (x.1)^*q +ɛ* (x.2)^*q.
Proof. by case: x. Qed.

Lemma conjdqD x y : (x + y)^*q = x^*q + y^*q.
Proof. by rewrite conjdq_def /= 2!linearD. Qed.

Lemma conjdqI x : (x^*q)^*q = x.
Proof. by rewrite !conjdq_def /= !conjqI; case: x. Qed.

Lemma conjdq0 : (0 : dquat)^*q = 0.
Proof. by rewrite conjdq_def /= conjq0. Qed.

Lemma conjdqM x y : (x * y)^*q = y^*q * x^*q.
Proof.
rewrite /= conjdq_def /= !muld_def /= !conjqM; congr mkDual.
by rewrite linearD /= !conjqM addrC.
Qed.

Lemma conjdq_comm x : x^*q * x = x * x^*q.
Proof. by rewrite conjdq_def /= !muld_def /= conjq_comm conjq_comm2 addrC. Qed.

Lemma conjdq_unit x : (x^*q \is a GRing.unit) = (x \is a GRing.unit).
Proof.
case: x => [] [a0 av] [b0 bv].
by rewrite !qualifE /= /unitd /= !qualifE /= /unitq /= !eq_quat /= oppr_eq0.
Qed.

Definition puredq := [qualify x : dquat | (x.1 \is pureq) && (x.2 \is pureq)].
Fact puredq_key : pred_key puredq. Proof. by []. Qed.
Canonical puredq_keyed := KeyedQualifier puredq_key.

Definition dnum := [qualify x : dquat | x^*q == x].
Fact dnum_key : pred_key dnum. Proof. by []. Qed.
Canonical dnum_keyed := KeyedQualifier dnum_key.

Lemma dnumE x : (x \is dnum) = (x^*q == x).
Proof. by []. Qed.

Lemma dnumE' x : (x \is dnum) = (x.1.2 == 0) && (x.2.2 == 0).
Proof.
case: x => [] [a1 a2] [b1 b2]; rewrite dnumE /conjdq /=.
by rewrite -[a2 == 0]andTb -[b2 == 0]andTb;
   congr ((_ && _) && (_ && _)); rewrite ?eqxx //= eq_sym
     -subr_eq0 opprK -mulr2n -scaler_nat scalemx_eq0 (eqr_nat _ 2 0).
Qed.

Lemma dnumE'' x : (x \is dnum) = (x == (x.1.1)%:q +ɛ* (x.2.1)%:q).
Proof.
case: x => [] [a1 a2] [b1 b2]; rewrite dnumE' /=.
by rewrite -[a2 == 0]andTb -[b2 == 0]andTb;
   congr ((_ && _) && (_ && _)); rewrite /= !eqxx.
Qed.

Lemma dnumD x y : x \is dnum -> y \is dnum -> x + y \is dnum.
Proof. by rewrite 3!dnumE conjdqD => /eqP-> /eqP->. Qed.

Lemma dnum0 : 0 \is dnum.
Proof. by rewrite dnumE' eqxx. Qed.

Lemma dnum1 : 1 \is dnum.
Proof. by rewrite dnumE' eqxx. Qed.

Lemma dnum_nat n : n%:R \is dnum.
Proof.
elim: n => [|n IH]; first by rewrite dnum0.
by rewrite -add1n natrD dnumD // dnum1.
Qed.

Lemma dnumM x y : x \is dnum -> y \is dnum -> x * y \is dnum.
Proof.
rewrite 3!dnumE' muld_def /= => /andP[/eqP-> /eqP->] /andP[/eqP-> /eqP->].
by rewrite !linear0r !scaler0 !add0r eqxx.
Qed.

Lemma dnumM_comm x y : x \is dnum -> y * x = x * y.
Proof.
case: y => done1 y2; rewrite dnumE'' => /eqP->.
by rewrite !muld_def /= !quat_algE -!quatAr -!quatAl !mulr1 !mul1r addrC.
Qed.

(* squared norm *)
Definition sqrdq x : dquat := x * x^*q.

Lemma dnum_sqrdq x : sqrdq x \in dnum.
Proof. by rewrite dnumE conjdqM conjdqI. Qed.

(* inverse *)
Definition invdq x : dquat := x^-1.

Lemma invdqEl x : x.1 != 0 -> invdq x = (sqrdq x)^-1 * (x^*q).
Proof.
move=> aD; rewrite /sqrdq -conjdq_comm invrM  ?conjdq_unit //.
by rewrite divrK ?conjdq_unit.
Qed.

Lemma invdqEr x : x.1 != 0 -> invdq x = (x^*q) * (sqrdq x)^-1.
Proof.
move=> aD; rewrite /sqrdq invrM  ?conjdq_unit // mulrA.
by rewrite mulrV ?mul1r // ?conjdq_unit.
Qed.

(* unit dual quaternions *)
Definition udquat := [qualify x : dquat | sqrdq x == 1].
Fact udquat_key : pred_key udquat. Proof. by []. Qed.
Canonical udquat_keyed := KeyedQualifier udquat_key.

Lemma udquatE x : (x \is udquat) = (sqrdq x == 1).
Proof. by []. Qed.

Lemma invdq_udquat x : x \is udquat -> x^-1 = x^*q.
Proof.
rewrite udquatE => /eqP sqE.
suff x1NZ : x.1 != 0 by rewrite [x^-1]invdqEl // sqE invr1 mul1r.
apply/eqP=> x1Z.
move/eqP: sqE; rewrite [sqrdq _]muld_def x1Z !mul0r => /andP[] /=.
by rewrite eq_sym oner_eq0.
Qed.

End dual_quaternion.

(* TODO: dual quaternions and rigid body transformations *)
Section dquat_rbt.
Variable R : rcfType (*realType*).
Local Open Scope dual_scope.
Implicit Types x : dquat R.

Definition dquat_from_rot_trans (r t : quat R)
  (_ : r \is uquat) (_ : r \isn't pureq) (_ : (polar_of_quat r).1 != 0)
  (* i.e., rotation around (polar_of_quat r).1 of angle (polar_of_quat r).2 *+ 2 *)
  (_ : t \is pureq)
  : dquat R := r +ɛ* t.

Definition rot_trans_from_dquat x := (x.1, 2%:R *: (x.2 * x.1^*q)).

End dquat_rbt.
