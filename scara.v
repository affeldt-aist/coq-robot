(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg ssrint div.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

Require Import ssr_ext angle euclidean3 skew vec_angle rot frame rigid screw.

From mathcomp.analysis Require Import reals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

(* SCARA robot manipulator as an example *)
Section scara.

Variable R : realType.
Let vector := 'rV[R]_3.

Variable theta1 : angle R.
Variable a1 : R.
Variable theta2 : angle R.
Variable a2 : R.
Variable d3 : R.
Variable theta4 : angle R.
Variable d4 : R.

Definition scara_rot := Rz (theta1 + theta2 + theta4).

Definition scara_trans := row3
  (a2 * cos (theta2 + theta1) + a1 * cos theta1)
  (a2 * sin (theta2 + theta1) + a1 * sin theta1)
  (d4 + d3).

(* [spong] p. 81, eqn. 3.49 *)
Section hom_scara.

Definition A10 := hom (Rz theta1) (row3 (a1 * cos theta1) (a1 * sin theta1) 0).
Definition A21 := hom (Rz theta2) (row3 (a2 * cos theta2) (a2 * sin theta2) 0).
Definition A32 := hTz d3.
Definition A43 := hom (Rz theta4) (row3 0 0 d4).

Lemma hom_SCARA_forward : A43 * A32 * A21 * A10 = hom scara_rot scara_trans.
Proof.
rewrite /A43 /A32.
rewrite homM mulr1 mulmx1 row3D. Simp.r.
rewrite /A21.
rewrite homM RzM mulmx_row3_col3 !scale0r !add0r e2row !row3Z row3D. Simp.r.
rewrite homM RzM addrC (addrC _ theta2) addrA; congr hom.
rewrite mulmx_row3_col3 e2row !row3Z !row3D. Simp.r.
by rewrite -!mulrA -mulrBr -cosD -mulrDr (addrC (_ * sin theta1)) -sinD.
Qed.

End hom_scara.

Section dh_scara.

Definition B10 := hTx a1 * hRz theta1.
Definition B21 := hTx a2 * hRz theta2.
Definition B32 := hTz d3.
Definition B43 := hTz d4 * hRz theta4.

Lemma dh_SCARA_forward : B43 * B32 * B21 * B10 = hom scara_rot scara_trans.
Proof.
rewrite -hom_SCARA_forward /B10 hTxRz -/A10 /B21 hTxRz -/A21.
by rewrite /B32 -/A32 /B43 /A43 hTzRz.
Qed.

End dh_scara.

(* [murray] example 3.1, p.87 *)
Section screw_scara.

(* initial configuration *)
Definition g0 := hom 1 (row3 (a1 + a2) 0 d4).

Definition w1 : vector := 'e_2%:R.
Definition w2 : vector := 'e_2%:R.
Definition v3 : vector := 'e_2%:R.
Definition w4 : vector := 'e_2%:R.

(* axis points *)
Definition q1 : vector := 0.
Definition q2 : vector := row3 a1 0 0.
Definition q4 : vector := row3 (a1 + a2) 0 0.

Definition t1 := rjoint_twist w1 q1.
Definition t2 := rjoint_twist w2 q2.
Definition t3 := pjoint_twist v3.
Definition t4 := rjoint_twist w4 q4.

Definition g := g0 * `e$(theta4, t4) *
  `e$(Rad.angle_of d3, t3) * `e$(theta2, t2) * `e$(theta1, t1).

Lemma S1 : `e$(theta1, t1) = hRz theta1.
Proof.
rewrite /t1 /rjoint_twist crossmulNv crossmulv0 oppr0 etwist_Rz; last first.
  by rewrite -norm_eq0 normeE oner_eq0.
by rewrite -Rz_eskew.
Qed.

(* TODO: generalize *)
Lemma point_axis_twist (d : R) :
  \pt( axis \T((- 'e_2%:R *v row3 d 0 0), 'e_2%:R) ) = row3 d 0 0.
Proof.
rewrite {1}/axis ang_tcoorE (negbTE (norm1_neq0 (normeE _ _))) /=.
rewrite normeE expr1n invr1 scale1r lin_tcoorE crossmulNv crossmulvN.
rewrite double_crossmul dotmulvv normeE expr1n scale1r /w2 /q2 e2row.
rewrite dotmulE sum3E !mxE /=. by Simp.r.
Qed.

Lemma S2_helper th d :
  `e$(th, \T(- w2 *v row3 d 0 0, w2)) =
  hom (Rz th) (row3 (d * (1 - cos th)) (- d * sin th) 0).
Proof.
rewrite etwistE (negbTE (norm1_neq0 (normeE _ _))).
rewrite pitch_perp ?normeE // mulr0 scale0r add0r.
rewrite point_axis_twist -Rz_eskew; congr hom.
rewrite mulmxBr mulmx1 mulmx_row3_col3 !scale0r !addr0 row3Z row3N row3D.
Simp.r.
by rewrite mulrBr mulr1.
Qed.

Lemma S2 : `e$(theta2, t2) =
  hom (Rz theta2) (row3 (a1 * (1 - cos theta2)) (- a1 * sin theta2) 0).
Proof. by rewrite /t2 S2_helper. Qed.

Hypothesis Hd3 : d3 \in Rad.f_codom R.

Lemma S3 : `e$(Rad.angle_of d3, t3) = hTz d3.
Proof.
rewrite etwistE eqxx eskew_v0 Rad.angle_ofK.
  rewrite /hTz /v3 e2row row3Z. by Simp.r.
exact Hd3.
Qed.

Lemma S4 : `e$(theta4, t4) = hom (Rz theta4)
  (row3 ((a1 + a2) * (1 - cos theta4)) (- (a1 + a2) * sin theta4) 0).
Proof. by rewrite /t4 /q4 S2_helper. Qed.

Lemma screw_SCARA_forward : g = hom scara_rot scara_trans.
Proof.
rewrite /g /g0 S1 S2 S3 S4 homM mul1r.
rewrite mulmx_row3_col3 scale0r addr0 e2row 2!row3Z 2!row3D. Simp.r.
rewrite mulrBr mulr1 addrCA subrr addr0 subrr.
rewrite homM mulr1 mulmx1 row3D. Simp.r.
rewrite homM RzM mulmx_row3_col3 e2row !row3Z !row3D. Simp.r.
rewrite (addrC _ (a1 * (1 - cos theta2))) mulrBr mulr1 mulrDl !addrA subrK.
rewrite mulrDl addrAC subrr add0r.
rewrite homM RzM mulmx_row3_col3 e2row !row3Z !row3D. Simp.r.
rewrite addrC (addrC theta4) addrA; congr hom.
rewrite /scara_trans; congr row3.
- by rewrite mulrDl -addrA -!mulrA -mulrBr -cosD addrC.
- by rewrite mulrDl -addrA -!mulrA -mulrDr (addrC (cos theta2 * _)) -sinD addrC.
Qed.

End screw_scara.

End scara.
