Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp
Require Import complex.
From mathcomp
Require Import finset fingroup perm.

Require Import aux angle euclidean3 skew vec_angle frame rot rigid.
Require Import boolp reals.

(*
 OUTLINE:
 1. section taylor expansion of the exponential map
 2. sections twist_definition/twist_properties
 3. section exponential_coordinates_rigid_using_taylor
 4. Module Rad (radian)
 5. section exponential_coordinates_rigid
 6. Module TwistComputationExample
 7. section screw definition
 8. section screw_motion
 9. section screw_coordinates_of_a_twist_continued
 10. wip: section etwist_alt, section screw_motion_utwist.
 11. Section screw_axis (Chasles' theorem, computation of a point on the axis)
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Lemma mulmx_tr_uvect (R : rcfType) (w : 'rV[R]_3) :
  norm w = 1 -> (w^T *m w) ^+ 2 = w^T *m w.
Proof.
move=> w1; rewrite expr2 -mulmxE -mulmxA (mulmxA w) dotmulP dotmulvv w1 expr1n.
by rewrite mul1mx.
Qed.

Section taylor_exponential.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Variable n : nat.
Implicit Type M : 'M[R]_n.+1.

Lemma expr_mulmulV M i (g : 'M[R]_n.+1) : g \in unitmx ->
  (g * M * g^-1)^+i = g * M ^+i * g^-1.
Proof.
move=> Hg; elim: i => [|i ih]; first by rewrite 2!expr0 mulr1 divrr.
rewrite exprS ih -!mulrA exprS -mulrA; congr (_ * (_ * _)).
by rewrite mulrA mulVr // mul1r.
Qed.

Definition ecoef M i := i`!%:R^-1 *: M ^+ i.

Lemma ecoefE M i : ecoef M i = i`!%:R^-1 *: M ^+ i.
Proof. by []. Qed.

Lemma ecoefM0 M : ecoef M 0 = 1.
Proof. by rewrite ecoefE expr0 fact0 invr1 scale1r. Qed.

Lemma ecoef0k k : ecoef 0 k = (k == O)%:R.
Proof.
rewrite ecoefE expr0n.
case: k => [|k]; first by rewrite fact0 invr1 scale1r.
by rewrite scaler0.
Qed.

Lemma ecoefS M i : ecoef M i.+1 = i.+1%:R^-1 *: M * ecoef M i.
Proof.
rewrite /ecoef -scalerAr -scalerAl -exprS scalerA; congr (_ *: _).
by rewrite factS natrM invrM // unitfE pnatr_eq0 // -lt0n fact_gt0.
Qed.

Lemma ecoef1 M : ecoef M 1 = M.
Proof. by rewrite ecoefS ecoefM0 mulr1 invr1 scale1r. Qed.

Lemma tr_ecoef M k : (ecoef M k)^T = ecoef M^T k.
Proof.
elim: k => [|k ih]; first by rewrite 2!ecoefM0 trmx1.
rewrite ecoefS -mulmxE -scalemxAl linearZ /= trmx_mul ih ecoefS.
rewrite -mulmxE -scalemxAl; congr (_ *: _).
by rewrite /ecoef -scalemxAr -scalemxAl !mulmxE -exprSr -exprS.
Qed.

Lemma ecoef_mulmulV M (g : 'M[R]_n.+1) i : g \in unitmx ->
  ecoef (g * M * g^-1) i = g * ecoef M i * g^-1.
Proof. move=> Hg; by rewrite /ecoef expr_mulmulV // -scalerAr scalerAl. Qed.

Definition emx M k := \sum_(i < k) ecoef M i.

Lemma emxM0 M : emx M 0 = 0.
Proof. by rewrite /emx big_ord0. Qed.

Lemma emxS M k : emx M k.+1 = emx M k + ecoef M k.
Proof. by rewrite /emx big_ord_recr. Qed.

Lemma emx0k k : emx 0 k = (k != O)%:R.
Proof.
elim: k => [|k ih]; first by rewrite emxM0 eqxx.
by rewrite emxS ih /= ecoef0k -natrD addn_negb.
Qed.

Lemma eSmx M k : emx M k.+1 = ecoef M 0 + \sum_(i < k) ecoef M i.+1.
Proof. by rewrite /emx big_ord_recl. Qed.

Lemma emx1 M : emx M 1 = 1.
Proof. by rewrite emxS emxM0 add0r ecoefM0. Qed.

Lemma emx2 M : emx M 2 = 1 + M.
Proof. by rewrite emxS emx1 ecoef1. Qed.

Lemma tr_emx M k : (emx M k)^T = emx M^T k.
Proof.
rewrite /emx.
have H : {morph @trmx R n.+1 n.+1 : x y / x + y >-> x + y}.
  move=> x y; by rewrite linearD.
rewrite (@big_morph _ _ _ 0 _ 0 _ H) ?trmx0 //; apply eq_bigr => i _.
by rewrite tr_ecoef.
Qed.

Lemma emx_mulmulV M k (g : 'M[R]_n.+1) : g \in unitmx ->
  emx (g * M * g^-1) k = g * emx M k * g^-1.
Proof.
move=> Hg; rewrite /emx big_distrr /= big_distrl /=.
apply/eq_bigr => i _; by rewrite ecoef_mulmulV.
Qed.

End taylor_exponential.

Module TwistCoor.
Section twist_coordinates_definition.
Variable R : rcfType.
Let vector := 'rV[R]_3.
Definition t := 'rV[R]_6.
Definition mk (v w : vector) : t := block_mx v w 0 0.
Definition lin (x : t) : vector := @ulsubmx R 1 0 3 3 x. (* linear vel. *)
Definition ang (x : t) : vector := @ursubmx R 1 0 3 3 x. (* angular vel. *)
Lemma lin_of v w : lin (mk v w) = v.
Proof. by rewrite /lin /mk block_mxKul. Qed.
Lemma ang_of v w : ang (mk v w) = w.
Proof. by rewrite /ang /mk block_mxKur. Qed.
End twist_coordinates_definition.
End TwistCoor.

(* forms a matrix in se(3) (i.e., a twist)
   out of a given vector in R^6 (i.e., twist coordinates) *)
Coercion wedge (R : rcfType) (x : TwistCoor.t R) : 'M_4 :=
  block_mx \S(TwistCoor.ang x) 0 (TwistCoor.lin x) 0.
Notation "'\T(' v , w ')'" := (TwistCoor.mk v w)
  (at level 3, w, v at next level, format "'\T(' v ,  w ')'") : ring_scope.
Notation "'\w(' t ')'" := (TwistCoor.ang t) (format "'\w('  t  ')'", at level 3).
Notation "'\v(' t ')'" := (TwistCoor.lin t) (format "'\v('  t  ')'", at level 3).

Definition bilinear (R : ringType) (T : lmodType R) (op : T -> T -> T) :=
  forall y, linear (op^~ y) /\ linear (op y).

Module LieAlgebra.
Section lie_algebra.
Variable R : ringType.
Structure t (T : lmodType R) := mk {
  bra : T -> T -> T ;
  liebilinear : bilinear bra ;
  alternative : forall x, bra x x = 0 ;
  jacobi : jacobi bra
}.
End lie_algebra.
End LieAlgebra.

Notation "lie[ t1 , t2 ]" := (LieAlgebra.bra _ t1 t2) : ring_scope.

Section lie_algebra_properties.
Variables (R : rcfType) (m n : nat).
Variable A : LieAlgebra.t [lmodType R of 'M[R]_(m, n)].

Local Notation "l[ t1 , t2 ]" := (LieAlgebra.bra A t1 t2).

Lemma anticommutativity x y : l[x, y] = - l[y, x].
Proof.
apply/eqP; rewrite -subr_eq0 opprK; apply/eqP.
transitivity l[x + y, x + y]; last by rewrite LieAlgebra.alternative.
apply/esym.
move: (proj1 ((LieAlgebra.liebilinear A) (x + y)) 1 x y); rewrite !scale1r => ->.
move: (proj2 (LieAlgebra.liebilinear A x) 1 x y); rewrite !scale1r => ->.
move: (proj2 (LieAlgebra.liebilinear A y) 1 x y); rewrite !scale1r => ->.
by rewrite !LieAlgebra.alternative !(addr0,add0r).
Qed.

End lie_algebra_properties.

Section lie_square_matrix.
Variables (R : rcfType) (n : nat).

Definition lie_sqmat (t1 t2 : 'M[R]_n.+1) := t1 * t2 - t2 * t1.

Local Notation "l[ t1 , t2 ]" := (lie_sqmat t1 t2).

Lemma lie_sqmat_bilinear : bilinear lie_sqmat.
Proof.
split => [k /= x1 x2 | k /= y1 y2]; rewrite /lie_sqmat.
- rewrite mulrDl -scalerAl scalerDr -!addrA; congr (_ + _).
  rewrite addrCA scalerN -opprD; congr (_ - _); by rewrite scalemxAr -mulmxDr.
- rewrite /lie_sqmat mulrDr -scalerAr scalerBr -!addrA; congr (_ + _).
  rewrite addrCA -opprD; congr (_ - _); by rewrite mulrDl scalemxAl.
Qed.

Lemma lie_sqmat_alternative x : l[x, x] = 0.
Proof. apply/eqP; by rewrite subr_eq0. Qed.

Lemma lie_sqmat_jacobi : jacobi lie_sqmat.
Proof.
move=> x y z; rewrite /lie_sqmat.
rewrite mulrBr (mulrBl z) opprB !addrA addrC !addrA (mulrA x) (addrC _ (x * y * z)) subrr add0r.
rewrite (mulrBl y) opprB addrA (addrC _ (x * z * y)) mulrA !addrA subrr add0r.
rewrite (mulrBr y) !addrA (addrC _ (- (y * (x * z)))) addrC !addrA mulrA subrr add0r.
by rewrite mulrBl opprB mulrA subrK mulrBr addrA mulrA subrK mulrA subrr.
Qed.

End lie_square_matrix.

Canonical lie_algebra_square_matrix (R : rcfType) n : LieAlgebra.t [lmodType R of 'M[R]_n.+1] :=
  LieAlgebra.mk (@lie_sqmat_bilinear R _) (@lie_sqmat_alternative R _) (@lie_sqmat_jacobi R _).

Section lie_euclidean_3.
Variable (R : rcfType).
Let vector := 'rV[R]_3.

Lemma lie_euclidean_3_bilinear : bilinear (@crossmul R).
Proof. split; [exact: crossmulr_linear | exact: crossmul_linear]. Qed.

Definition lie_euclidean_3_alternative := @crossmulvv R.

Definition lie_euclidean_3_jacobi := @jacobi_crossmul R.

End lie_euclidean_3.

(*Canonical lie_euclidean_3 (R : rcfType) :=
  @LieAlgebra.mk R _ _ (@lie_euclidean_3_bilinear R) (@lie_euclidean_3_alternative R) (@lie_euclidean_3_jacobi R).*)

Section twist_properties.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Lemma twistZ (a : R) v w : a *: (\T(v, w) : 'M_4) = \T((a *: v), (a *: w)).
Proof.
by rewrite /wedge !TwistCoor.ang_of !TwistCoor.lin_of (scale_block_mx a \S(w))
  2!scaler0 skew_mxZ.
Qed.

Lemma ang_of_twist0 : \w( 0 ) = 0 :> 'rV[R]_3.
Proof. by rewrite /TwistCoor.ang -(block_mx0 R 1 0 3 3) block_mxKur. Qed.

Lemma ang_of_twistE v w : \w( \T(v, w) ) = w :> 'rV[R]_3.
Proof. by rewrite /TwistCoor.ang /TwistCoor.mk block_mxKur. Qed.

Lemma ang_of_twistZ k (t : TwistCoor.t R) : \w( (k *: t) ) = k *: \w( t ).
Proof.
rewrite /TwistCoor.ang -{1}(@submxK _ 1 0 3 3 t).
by rewrite (@scale_block_mx _ 1 0 3 3) block_mxKur.
Qed.

Lemma lin_of_twist0 : \v( 0 ) = 0 :> 'rV[R]_3.
Proof. by rewrite /TwistCoor.lin -(block_mx0 R 1 0 3 3) block_mxKul. Qed.

Lemma lin_of_twistE v w : \v( \T(v, w) ) = v :> 'rV[R]_3.
Proof. by rewrite /TwistCoor.lin /TwistCoor.mk block_mxKul. Qed.

Lemma lin_of_twistZ k (t : TwistCoor.t R) : \v( (k *: t) ) = k *: \v( t ).
Proof.
rewrite /TwistCoor.lin -{1}(@submxK _ 1 _ 3 _ t).
by rewrite (@scale_block_mx _ 1 _ 3) block_mxKul.
Qed.

Lemma mkE (t : TwistCoor.t R) : \T((\v( t )), (\w( t ))) = t.
Proof.
rewrite /TwistCoor.mk /TwistCoor.ang /TwistCoor.lin -[RHS](@submxK R 1 0 3 3 t).
f_equal; apply/matrixP; by do 2 case.
Qed.

Definition lin_of_twist (M : 'M[R]_4) := @dlsubmx _ 3 1 3 1 M.

Lemma lin_lin_of_twist t : \v( t ) = lin_of_twist (wedge t).
Proof. by rewrite /TwistCoor.lin /lin_of_twist /wedge block_mxKdl. Qed.

Definition ang_of_twist (M : 'M[R]_4) := unskew (@ulsubmx _ 3 1 3 1 M).

Lemma ang_ang_of_twist t : \w( t ) = ang_of_twist (wedge t).
Proof. by rewrite /TwistCoor.ang /ang_of_twist /wedge block_mxKul skew_mxK. Qed.

(* the set of twists *)
Definition se3 := [qualify M : 'M[R]_4 |
  [&& @ulsubmx _ 3 1 3 1 M \is 'so[R]_3,
      @ursubmx _ 3 1 3 1 M == 0 &
      @drsubmx _ 3 1 3 1 M == 0] ].
Fact se3_key : pred_key se3. Proof. by []. Qed.
Canonical se3_keyed := KeyedQualifier se3_key.

(*
TODO?
Lemma se3E (M : 'M[R]_4) : (M \is se3) = (M == \T( \v( vee M ), \w( vee M ))).
Proof.
apply/idP/idP => [|/eqP ->].
  rewrite qualifE => /and3P[].
  rewrite qualifE => /eqP H1 /eqP H2 /eqP H3.
  rewrite -{1}(@submxK _ 3 1 3 1 M) H2 H3.
  rewrite /wedge /=.
  rewrite Twist.ang_of Twist.lin_of.
  rewrite /vee.
  rewrite unskewK //. qualifE; by apply/eqP.
rewrite qualifE.
rewrite /wedge.
rewrite block_mxKul /= block_mxKur /= eqxx /=.
by rewrite block_mxKdr eqxx andbT anti_skew.
Qed.*)

(* [murray] p.56, lem 2.13 (part 1) *)
Lemma conj_SE3_se3 (t : TwistCoor.t R) g : g \is 'SE3[R] ->
  g^-1 * t * g \is se3.
Proof.
move=> Hg; rewrite SE3_inv // /inv_hom /hom /wedge.
rewrite [in X in _ * _ * X \is _](SE3E Hg) /hom -mulmxE.
set r := rot_of_hom g. set p := rot_of_hom g.
rewrite (mulmx_block r^T _ _ _ \S(\w( t ))) !(mulmx0,addr0,mul0mx,mul1mx).
rewrite (mulmx_block (r^T *m \S(\w( t ))) _ _ _ r) !(mulmx0,mul0mx,addr0).
rewrite qualifE; apply/and3P; rewrite ?block_mxKul ?block_mxKur ?block_mxKdr.
split => //; by rewrite conj_so // anti_skew.
Qed.

(* extract the 6-dimensional vector (i.e., the twist coordinates)
   which parameterizes a twist *)
Definition vee (t : 'M[R]_4) : 'rV[R]_6 :=  \T(lin_of_twist t, ang_of_twist t).

Lemma veeK t : t \is se3 -> wedge (vee t) = t.
Proof.
rewrite qualifE antiE => /and3P[/eqP H1 /eqP H2 /eqP H3].
rewrite /wedge /vee ang_of_twistE lin_of_twistE /lin_of_twist.
rewrite -[in RHS](@submxK _ 3 1 3 1 t) H1 H2 H3; f_equal.
rewrite unskewK // antiE; by apply/eqP.
Qed.

Lemma wedgeK t : vee (wedge t) = t.
Proof.
rewrite /vee /wedge /lin_of_twist /ang_of_twist block_mxKdl block_mxKul skew_mxK.
by rewrite mkE.
Qed.

(* TODO: move *)
Lemma skew_mx_crossmul (u v : 'rV[R]_3) : \S(v *v u) = \S(u) *m \S(v) - \S(v) *m \S(u).
Proof.
apply/eqP/mulmxP => w.
rewrite [in LHS]skew_mxE mulmxBr !mulmxA ![in RHS]skew_mxE.
rewrite (crossmulC v w) crossmulvN opprK.
move/eqP: (jacobi_crossmul v u w); rewrite eq_sym -subr_eq eq_sym => /eqP ->.
by rewrite add0r (crossmulC w) opprK.
Qed.

Lemma lie_bracketE (t1 t2 : TwistCoor.t R) :
  let v1 := TwistCoor.lin t1 in
  let v2 := TwistCoor.lin t2 in
  let w1 := TwistCoor.ang t1 in
  let w2 := TwistCoor.ang t2 in
(*  lie[t1, t2] =*)
  (* NB *) LieAlgebra.bra (@lie_algebra_square_matrix R 3) (wedge t1) (wedge t2) =
  block_mx \S( w2 *v w1 ) 0 (w2 *v v1 + v2 *v w1) 0.
Proof.
move=> v1 v2 w1 w2.
(* NB *) rewrite /LieAlgebra.bra /= /lie_sqmat.
rewrite /wedge -/v1 -/v2 -/w1 -/w2.
rewrite -mulmxE.
rewrite (mulmx_block \S(w1) 0 v1 0 \S(w2)).
rewrite (mulmx_block \S(w2) 0 v2 0 \S(w1)).
rewrite !(mul0mx,addr0,mulmx0).
rewrite (opp_block_mx (\S(w2) *m \S(w1))) !oppr0.
rewrite (add_block_mx (\S(w1) *m \S(w2))) !addr0.
by rewrite 2!skew_mxE skew_mx_crossmul (crossmulC w1 v2) opprK.
Qed.

Lemma lie_bracketE' (t1 t2 : TwistCoor.t R) :
  let v1 := TwistCoor.lin t1 in
  let v2 := TwistCoor.lin t2 in
  let w1 := TwistCoor.ang t1 in
  let w2 := TwistCoor.ang t2 in
  (* NB: can't parse *) LieAlgebra.bra (@lie_algebra_square_matrix _ _) t1 t2 =
  \T( w2 *v v1 + v2 *v w1, w2 *v w1).
Proof.
move=> v1 v2 w1 w2.
by rewrite lie_bracketE -/v1 -/v2 -/w1 -/w2 /wedge TwistCoor.lin_of TwistCoor.ang_of.
Qed.

End twist_properties.

Notation "''se3[' R ]" := (se3 R)
  (at level 8, format "''se3[' R ]") : ring_scope.
Notation "lie[ t1 , t2 ]" := (lie_bracket t1 t2).

(* NB: work in progress *)
Section twist_and_adjoint.

Variable R : rcfType.

(* [murray] p.56, lem 2.13 (part 2) *)
Lemma conj_adjoint (t : TwistCoor.t R) g : g \is 'SE3[R] ->
  g^-1 * t * g = wedge (t *m adjoint g).
Proof.
move=> gSE.
(* rhs *)
rewrite /adjoint -{2}(mkE t) (mulmx_block \v(t) _ 0 0 (rot_of_hom g)).
rewrite !(mulmx0,mul0mx,addr0,add0r).
(* lhs *)
rewrite {1}/wedge /= {2}(SE3E gSE) {1}/hom -mulrA -[in LHS]mulmxE.
rewrite (mulmx_block \S( \w( t ) ) 0 ( \v( t ) ) 0 (rot_of_hom g)).
rewrite !(mulmx0,add0r,mul1mx,mul0mx,addr0).

rewrite SE3_inv // {1}/inv_hom {1}/hom.
rewrite (mulmx_block (rot_of_hom g)^T 0 _ 1 (\S( \w( t ) ) *m rot_of_hom g)).
rewrite !(mul0mx,addr0,mulmx0,mul1mx).
set a := _ *m _. set b := _ + _.
set a' := _ + _. set b' := _ *m _.
rewrite /wedge TwistCoor.ang_of TwistCoor.lin_of; f_equal.
- rewrite {}/a {}/b'.
  rewrite mulmxA !mulmxE; apply/eqP/mulmxP => u.
  by rewrite conj_skew_mx ?rot_of_hom_SO // skew_mxE.
- rewrite {}/a' {}/b.
  rewrite addrC; congr (_ + _).
  rewrite -mulmxE -mulmxA mulmxE mulNmx mulrA conj_skew_mx ?rot_of_hom_SO //.
  by rewrite -!mulmxE mulmxA skew_mxE crossmulC opprK.
Qed.

(* NB: wrong *)
Lemma adjointE (x y : TwistCoor.t R) :
  x *m adjoint y = (*NB: can't parse *)vee (LieAlgebra.bra (@lie_algebra_square_matrix _ _) x y).
Proof.
rewrite lie_bracketE' /=.
rewrite /vee -lin_lin_of_twist -ang_ang_of_twist lin_of_twistE ang_of_twistE.
rewrite /adjoint.
rewrite -{1}(mkE x).
rewrite (mulmx_block \v(x) _ _ _ (rot_of_hom y)) !(mulmx0,add0r,mul0mx).
rewrite /TwistCoor.mk; f_equal.
  rewrite -!skew_mxE; congr (_ + _).
  by rewrite /wedge /rot_of_hom block_mxKul.
  rewrite /wedge /trans_of_hom block_mxKdl /rot_of_hom block_mxKul; congr (_ *m _).
  admit.
rewrite -skew_mxE.
by rewrite /wedge /rot_of_hom block_mxKul.
Abort.

End twist_and_adjoint.

Section sample_rigid_transformation.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types v w : vector.

Definition rigid_trans w v := hom 1 (v *v w).

Definition inv_rigid_trans w v := hom 1 (- v *v w).

Lemma Vrigid_trans w v : inv_rigid_trans w v * rigid_trans w v = 1.
Proof.
by rewrite /inv_rigid_trans /rigid_trans homM mulr1 mulmx1 addrC crossmulNv subrr hom10.
Qed.

Lemma rigid_transV w v : rigid_trans w v * inv_rigid_trans w v = 1.
Proof.
by rewrite /inv_rigid_trans /rigid_trans homM mulr1 mulmx1 crossmulNv subrr hom10.
Qed.

Lemma rigid_trans_unitmx w v : rigid_trans w v \in unitmx.
Proof.
by rewrite unitmxE /rigid_trans (det_lblock 1 (_ *v _)) 2!det1 mulr1 unitr1.
Qed.

Lemma inv_rigid_transE w v : (rigid_trans w v)^-1 = inv_rigid_trans w v.
Proof.
rewrite -[LHS]mul1mx -[X in X *m _ = _](Vrigid_trans w v) -mulmxA.
by rewrite mulmxV ?rigid_trans_unitmx // mulmx1.
Qed.

Lemma rigid_trans_unit w v : rigid_trans w v \is a GRing.unit.
Proof.
apply/unitrP; exists (inv_rigid_trans w v); by rewrite Vrigid_trans rigid_transV.
Qed.

End sample_rigid_transformation.

(* exponential coordinates for rbt using taylor expansion of the exponential function *)
(* [murray] proposition 2.8, p. 41-42 *)
Section exponential_coordinates_rigid_using_taylor.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types w v : vector.

Lemma exp_twist0v v n : (\T(v, 0) : 'M_4) ^+ n.+2 = 0.
Proof.
elim: n => [|n ih]; last by rewrite exprS ih mulr0.
rewrite expr2.
rewrite /wedge TwistCoor.ang_of TwistCoor.lin_of skew_mx0 -mulmxE.
set a := 0. set b := 0.
by rewrite (mulmx_block a b v _ a b v _) /a /b !(mulmx0,addr0,mul0mx) block_mx0.
Qed.

(* [murray] eqn 2.32, p.41 *)
Lemma emx_twist0E v k : emx \T(v, 0) k.+2 = hom 1 v.
Proof.
rewrite /emx 2!big_ord_recl big1 ?addr0; last first.
  move=> /= i _; by rewrite ecoefE exp_twist0v scaler0.
rewrite liftE0 eqxx /ecoef factS fact0 expr0 expr1 invr1 2!scale1r.
rewrite /wedge TwistCoor.ang_of TwistCoor.lin_of skew_mx0.
by rewrite -idmxE (@scalar_mx_block _ 3 1 1) (add_block_mx 1 0 0 1 0 _ v) !(addr0,add0r).
Qed.

Lemma p41eq234 w v : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in
  g^-1 *m \T(v, w) *m g = \T(h *: w, w).
Proof.
move=> w1 g h.
rewrite inv_rigid_transE /inv_rigid_trans /rigid_trans.
rewrite /wedge !TwistCoor.ang_of !TwistCoor.lin_of.
rewrite (mulmx_block 1 0 (- _ *v _) 1 \S( w )) !(mulmx0,addr0,mul0mx,mul1mx).
rewrite skew_mxE crossmulNv crossmulvN.
rewrite double_crossmul dotmulvv w1 expr1n scale1r opprB subrK.
by rewrite (mulmx_block \S( w ) 0 _ 0 1 0) !(mulmx0,addr0,mul0mx,mul1mx,mulmx1).
Qed.

Lemma p42eq235 w v a k :
  let g := rigid_trans w v in
  let e' := g^-1 *m \T(v, w) *m g in
  emx (a *: (\T(v, w) : 'M_4) ) k = g * emx (a *: e') k * g^-1.
Proof.
move=> g e'.
rewrite -emx_mulmulV ?rigid_trans_unitmx //; congr (emx _ _).
rewrite /e' mulmxE -/g -(mulrA g^-1) -scalerAr -scalerAl; congr (_ *: _).
rewrite !mulrA divrr ?rigid_trans_unit // mul1r -mulrA.
by rewrite divrr ?mulr1 // rigid_trans_unit.
Qed.

Lemma p42eq2 w v : norm w = 1 ->
  let g := rigid_trans w v in
  let e' := g^-1 *m \T(v, w) *m g in
  forall k, e' ^+ k.+2 = block_mx (\S( w ) ^+ k.+2) 0 0 0.
Proof.
move=> w1 g e' k.
rewrite /e' (p41eq234 _ w1).
set h := w *d v.
rewrite /wedge TwistCoor.ang_of TwistCoor.lin_of.
elim: k => [|k ih].
  rewrite (@expr2 _ (block_mx \S( w ) _ _ _)) -mulmxE (mulmx_block \S( w ) _ _ _ \S( w )).
  by rewrite !(mulmx0,addr0,mul0mx) mulmxE -expr2 skew_mxE /= crossmulvZ crossmulvv scaler0.
rewrite exprS ih -mulmxE (mulmx_block \S( w ) _ _ _ (\S( w ) ^+ k.+2)).
rewrite !(mulmx0,addr0,mul0mx) mulmxE -exprS; congr (block_mx (\S( w ) ^+ k.+3) 0 _ 0).
by rewrite exprS mulmxA skew_mxE /= crossmulvZ crossmulvv scaler0 mul0mx.
Qed.

Lemma emx2_twist w v a : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in
  emx (a *: (\T(v, w) : 'M_4) ) 2 = g *m hom (emx (a *: \S( w)) 2) (h *: (a *: w)) *m g^-1.
Proof.
move=> w1 g h.
rewrite {1}/emx 2!big_ord_recl big_ord0 addr0 liftE0 eqxx /ecoef factS fact0 invr1 2!scale1r.
rewrite expr0 expr1.
rewrite (_ : 1 = @block_mx _ 3 _ 3 _ 1 0 0 1); last first.
  by rewrite -idmxE (@scalar_mx_block _ 3 1 1).
rewrite twistZ /=.
rewrite /wedge TwistCoor.ang_of TwistCoor.lin_of (add_block_mx 1 0 0 1 \S( a *: w )) !(addr0,add0r).
rewrite {1}/g /rigid_trans mulmxE homM mul1r.
rewrite inv_rigid_transE /inv_rigid_trans homM mulr1 mulmx1 emx2.
rewrite -skew_mxZ.
congr (block_mx (1 + \S( a *: w )) 0 _ 1).
rewrite mulmxDr mulmx1 crossmulNv -addrA addrC addrA subrK skew_mxE.
rewrite scalerA (mulrC h) -scalerA /= crossmulZv -scalerDr; congr (_ *: _).
by rewrite double_crossmul dotmulvv w1 expr1n scale1r -/h addrCA subrr addr0.
Qed.

Lemma p42eq3 w v a : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in 
  let e' := g^-1 *m \T(v, w) *m g in
  forall k, emx (a *: e') k.+2 = hom (emx (a *: \S( w )) k.+2) (h *: (a *: w)).
Proof.
move=> w1 g h e'; rewrite /e'.
elim => [|k ih].
  rewrite -{2}(invrK g) scalemxAl scalemxAr.
  rewrite emx_mulmulV ?unitrV ?rigid_trans_unit //.
  rewrite emx2_twist // !mulmxE !mulrA mulVr ?rigid_trans_unit // mul1r.
  by rewrite -!mulrA divrr ?unitrV ?rigid_trans_unit // mulr1.
rewrite emxS ih /ecoef exprZn p42eq2 //.
rewrite (scale_block_mx (a ^+ k.+2) (\S(w) ^+ k.+2)) !scaler0.
rewrite -exprZn -skew_mxZ.
rewrite (scale_block_mx ((k.+2)`!%:R^-1) (\S( (a *: w) ) ^+ k.+2)) !scaler0.
by rewrite (add_block_mx (emx \S( a *: w ) k.+2)) !(addr0) -emxS.
Qed.

Definition hom_twist t a e : 'M[R]_4 :=
  let (v, w) := (\v( t ), \w( t )) in
  if w == 0 then
    hom 1 (a *: v)
  else
    hom e ((norm w)^-2 *: ((w *v v) *m (1 - e) + (a *: v) *m (w^T *m w))).

(* [murray] eqn 2.36, p.42 *)
Definition emx_twist a t k : 'M_4 :=
  hom_twist t a (emx \S( a *: \w( t ) ) k).

(* [murray] eqn 2.36, p.42 *)
Lemma emx_twistE (t : TwistCoor.t R) a k :
  emx (a *: (t : 'M_4)) k.+2 = emx_twist a t k.+2.
Proof.
set v := lin_of_twist t.
set w := ang_of_twist t.
rewrite (_ : t = \T(v, w)); last first.
  rewrite {}/v {}/w.
  rewrite -[in LHS](mkE t).
  f_equal.
  by rewrite lin_lin_of_twist.
  by rewrite ang_ang_of_twist.
(*  by case: t => v w; rewrite ang_of_twistE lin_of_twistE.*)
case/boolP : (w == 0) => [/eqP ->|w0].
  rewrite twistZ /= scaler0 emx_twist0E.
  by rewrite /emx_twist /hom_twist ang_of_twistE eqxx lin_of_twistE.
set w' : 'rV_3 := a *: w.
rewrite -(norm_scale_normalize w) (_ : v = (norm w) *: ((norm w)^-1 *: v)); last first.
  by rewrite scalerA divrr ?scale1r // unitfE norm_eq0.
rewrite -(twistZ (norm w) ((norm w)^-1 *: v) (normalize w)).
rewrite scalerA p42eq235 p42eq3; last by rewrite norm_normalize.
rewrite -mulmxE.
rewrite {1}/rigid_trans mulmxE homM mul1r.
rewrite inv_rigid_transE /inv_rigid_trans homM mulr1 mulmx1.
rewrite -scalerA -skew_mxZ norm_scale_normalize.
rewrite -scalerA norm_scale_normalize.

rewrite /emx_twist /hom_twist.

rewrite ang_of_twistE (negbTE w0) skew_mxZ; congr hom.

(*rewrite ang_of_twistZ ang_of_twistE norm_scale_normalize (negbTE w0).
rewrite skew_mxZ; congr hom.*)

rewrite crossmulZv crossmulvZ scalerA.
rewrite dotmulZv dotmulvZ !mulrA -[in X in _ + X + _]scalerA.
rewrite crossmulvZ crossmulNv [in X in _ + _ + X = _]scalerN crossmulZv [in X in _ + _ + X]scalerA.
rewrite -scalemxAl -scalerDr -scalerBr; congr (_ *: _).
  by rewrite -invrM ?unitfE ?norm_eq0.
rewrite -/w' /= [in X in _ = X + _]mulmxBr mulmx1.
rewrite -[in RHS]addrA [in RHS]addrC; congr (_ + _ + _).
- rewrite lin_of_twistE crossmulC mulNmx.
  by rewrite scalerA divrr ?unitfE ?norm_eq0 ?scale1r.
- rewrite lin_of_twistE.
  rewrite (scalerA (norm w)) divrr ?scale1r ?unitfE ?norm_eq0 //.
  rewrite -scalemxAl.
  rewrite mulmxA.
  rewrite dotmulP mul_scalar_mx dotmulC.
  by rewrite scalerA mulrC -scalerA.
- rewrite crossmulC opprK; congr (_ *v _).
  by rewrite lin_of_twistE scalerA divrr ?scale1r ?lin_of_twistE // unitfE norm_eq0.
Qed.

(* [murray] proposition 2.8, p. 41 *)
Lemma emx_twist_SE3 v w a k :
  emx \S(a *: w) k.+2 \is 'SO[R]_3 ->
  emx (a *: (\T(v, w) : 'M_4)) k.+2 \is 'SE3[R].
Proof.
move=> emx_SO; rewrite emx_twistE.
rewrite /emx_twist /hom_twist ang_of_twistE.
case: ifPn => [_|w0]; by rewrite hom_is_SE // rpred1.
Qed.

End exponential_coordinates_rigid_using_taylor.

Module Rad.
Section radian.
Variable R : realType.
Axiom f : angle R -> R.
Axiom f0 : forall a, (f a == 0) = (a == 0).
Axiom pi_gt1 : f pi > 1.
Definition f_codom := [pred x | 0 <= x < f pi *+ 2].
Axiom in_codom : forall x, f x \in f_codom.
Axiom angle_of : R -> angle R.
Axiom fK : cancel f angle_of.
Axiom angle_ofK : {in f_codom, cancel angle_of f}.
End radian.
End Rad.
Notation rad := Rad.f.
Notation rad_in := Rad.in_codom.
Notation rad_eq0 := Rad.f0.
Notation rad_pi_gt1 := Rad.pi_gt1.

Section RadTheory.

Variable R : realType.

Lemma rad0 : rad 0 = 0 :> R.
Proof. by apply/eqP; rewrite rad_eq0. Qed.

Lemma rad_ge0 (x : angle R) : rad x >= 0.
Proof. by have /andP [] := rad_in x. Qed.

Lemma rad_lt_pi (x : angle R) : rad x < rad pi *+ 2.
Proof. by have /andP [] := rad_in x. Qed.

Lemma rad_2pi_gt1 : 1 < rad pi *+ 2 :> R.
Proof.
rewrite (@ltr_le_trans _ (rad pi *+ 1)) ?rad_pi_gt1 //.
by rewrite -subr_ge0 -mulrnBr // rad_ge0.
Qed.

End RadTheory.

Hint Resolve rad_ge0 rad_lt_pi rad_pi_gt1.


Section exponential_coordinates_rigid.

Variable R : realType.

(* NB: same definition as exp_twist but using exp_mat instead of the taylor expansion of
   the exponential *)
(* [springer] eqn 1.27, p. 17, closed expression for the exponential of a twist *)
Definition etwist a (t : TwistCoor.t R) :=
  hom_twist t (rad a) (`e^(a, \w( t ))).

Local Notation "'`e$(' a ',' t ')'" := (etwist a t) (format "'`e$(' a ','  t ')'").

Lemma etwistv0 (a : angle R) : `e$(a, \T(0, 0)) = hom 1 0.
Proof. by rewrite /etwist ang_of_twistE /hom_twist ang_of_twistE eqxx lin_of_twistE scaler0. Qed.

Lemma etwist_is_SE (t : TwistCoor.t R) a : norm \w( t ) = 1 -> `e$(a, t) \in 'SE3[R].
Proof. 
move=> w1.
by rewrite /etwist /hom_twist (negbTE (norm1_neq0 w1)) hom_is_SE // eskew_is_SO.
(*case: t w1 => w v.
rewrite ang_of_twistE => w1.
by rewrite (negbTE (norm1_neq0 w1)) hom_is_SE // eskew_is_SO.*)
Qed.

Definition etwist_is_onto_SE_mat (a : angle R) w :=
  (rad a * norm w ^+ 2)%:A
    + ((1 - cos a) * norm w ^+2) *: \S(w)
      + (rad a - sin a) *: \S(w)^+2.

Definition etwist_is_onto_SE_mat_inv (a : angle R) w :=
  (rad a)^-1%:M
   - 2%:R^-1 *: \S(w)
     + ((rad a)^-1 - 2%:R^-1 * cot (half_angle a)) *: \S(w) ^+ 2.

Lemma etwist_is_onto_SE_matP a w (a0 : a != 0) (w1 : norm w = 1) :
  etwist_is_onto_SE_mat_inv a w * etwist_is_onto_SE_mat a w = 1.
Proof.
rewrite /etwist_is_onto_SE_mat /etwist_is_onto_SE_mat_inv.
set ra := rad a.
rewrite w1 expr1n !mulr1.
rewrite !mulrDl.
rewrite 6!mulrDr.
rewrite {1}scalemx1 -{1}mulmxE -scalar_mxM mulVr; last by rewrite unitfE rad_eq0.
rewrite -[RHS]addr0 -!addrA; congr (_ + _); rewrite !addrA.

rewrite -!mulmxE.
rewrite !mul_scalar_mx scalemx1 !mul_mx_scalar.
rewrite -!scalemxAl -!scalemxAr.
rewrite 2!mulNmx.
rewrite (scalerN (1 - cos a) (_ *m _)).
rewrite (scalerN (ra - sin a) (_ *m _)).
rewrite -!scalemxAl mulmxE -expr2 -exprSr -exprS -exprD.
rewrite skew_mx3 skew_mx4.
rewrite w1 expr1n 2!scaleN1r.
rewrite !(scalerN _ \S(w)) !(scalerN _ (\S(w) ^+ 2)).

rewrite (scalerN (ra - sin a)) opprK.
rewrite (scalerBl ra (sin a) (_ *: _)).
rewrite -!addrA.
rewrite (addrCA (ra *: - _)).
rewrite !addrA.
rewrite (scalerN ra) subrK.

rewrite (scalerBl (ra^-1) _ (- (_ *: \S(w) ^+ 2))).
rewrite (scalerN (ra^-1)).
rewrite (addrC (- (_))) !addrA addrC.
rewrite -!addrA.
rewrite addrCA.
rewrite !addrA subrK.

rewrite (scalerBl (ra^-1) _ (- (_ *: \S(w)))).
rewrite addrAC.
rewrite (addrC (ra^-1 *: - _)) addrA addrC.
rewrite scalerN !addrA.
rewrite (addrC (- _)) subrr add0r.

rewrite (scalerA ra).
rewrite mulrBr divrr; last by rewrite unitfE rad_eq0.
rewrite scalerBl scale1r.

rewrite (scalerN (2%:R^-1 * _)) opprK.
rewrite (scalerA (2%:R^-1 * _)).
rewrite mulrBr scalerBl !addrA.
rewrite mulrCA (mulrC ra) mulrA.
rewrite subrK.

case/boolP : (sin a == 0) => [/eqP| sa0].
  case/sin0_inv => [/eqP|api]; first by rewrite (negbTE a0).
  rewrite api cospi sinpi scale0r subr0 mulr0 scale0r subr0.
  rewrite half_anglepi.
  rewrite cot_pihalf mulr0 scale0r subr0 opprK (_ : 1 + 1 = 2%:R) // scalerA.
  by rewrite divrr ?unitfE ?pnatr_eq0 // scale1r addrC subrr.
rewrite {1}cot_half_angle' -!mulrA mulVr ?mulr1; last first.
  by rewrite unitfE.
rewrite cot_half_angle.
rewrite (scalerN (2%:R^-1 * _)) opprK.
rewrite (scalerA (2%:R^-1 * _)).
rewrite -!mulrA mulVr ?mulr1; last first.
  rewrite unitfE subr_eq0.
  by apply: contra a0 => /eqP/esym/cos1_angle0 ->.
rewrite (addrC (- _)) addrC !addrA.
rewrite scalerA mulrC subrr add0r.

rewrite (mulrC 2%:R^-1).
rewrite -scalerA.
rewrite scalerBl scale1r opprB.
rewrite scalerDl scale1r opprD !addrA addrC !addrA.
rewrite (addrC (- (cos a *: _))) subrr add0r.
rewrite addrAC.
rewrite -scaleNr -scalerDl.
rewrite -opprD -mulr2n -mulr_natl divrr; last first.
  by rewrite unitfE pnatr_eq0.
by rewrite scaleN1r addrC subrr.
Qed.

Lemma etwist_is_onto_SE (f : 'M[R]_4) : f \is 'SE3[R] ->
  exists t a, f = `e$(a, t).
Proof.
set p := trans_of_hom f.
case/boolP: (rot_of_hom f == 1) => rotf fSE.
case/boolP : (Rad.angle_of (norm p) == 0) => p0.
    exists \T(p, 0), (Rad.angle_of 1).
    rewrite /etwist /hom_twist ang_of_twistE eqxx lin_of_twistE.
    rewrite Rad.angle_ofK; last by rewrite inE ler01 rad_2pi_gt1.
    by rewrite scale1r (SE3E fSE) (eqP rotf).
  exists \T((rad (Rad.angle_of (norm p)))^-1 *: p, 0),
         (Rad.angle_of (norm p)).
  rewrite /etwist /hom_twist ang_of_twistE eqxx /= lin_of_twistE.
  rewrite scalerA divrr; last by rewrite unitfE rad_eq0.
  by rewrite scale1r (SE3E fSE) (eqP rotf).
case: (eskew_is_onto_SO (rot_of_hom_SO fSE)) => a fexp_skew.
set w := normalize (vaxis_euler _) in fexp_skew.
have a0 : a != 0.
  apply: contra rotf => /eqP.
  rewrite fexp_skew => ->; by rewrite emx30M.
set A : 'M_3 := \S(w) *m (1 - rot_of_hom f) + rad a *: (w^T *m w).
suff [v Hv] : { v | p = (norm w)^-2 *: (v *m A) }.
  exists \T(v, w), a.
  rewrite (SE3E fSE) /etwist /hom_twist ang_of_twistE.
  have /negbTE -> : w != 0 by rewrite normalize_eq0 vaxis_euler_neq0 // rot_of_hom_SO.
  rewrite fexp_skew -/p Hv; congr (hom _ (_ *: _)).
  by rewrite lin_of_twistE /A mulmxDr mulmxA skew_mxE -scalemxAr -scalemxAl fexp_skew.
have HA : A = etwist_is_onto_SE_mat a w.
  (* TODO: isolate as a lemma? *)
  rewrite /A /etwist_is_onto_SE_mat.
  rewrite fexp_skew /emx3.
  rewrite mulmxBr mulmx1 -(addrA 1) mulmxDr mulmx1 -!addrA opprD !addrA subrr add0r.
  rewrite mulmxDr.
  rewrite -scalemxAr mulmxE -expr2 opprD.
  rewrite [in X in _ = _ + X]scalerBl.
  rewrite ![in RHS]addrA [in RHS]addrC.
  rewrite -addrA; congr (_ + _).
  rewrite -scalerAr.
  rewrite -exprS skew_mx3.
  rewrite skew_mx2.
  rewrite scalerBr.
  rewrite -![in RHS]addrA [in RHS]addrC ![in RHS]addrA.
  rewrite !scalemx1 scalar_mxM.
  rewrite mul_scalar_mx subrK.
  by rewrite scaleNr scalerN opprK scalerA.
suff : { A' : 'M_3 |  A' * A = 1 }.
  case => A' AA'.
  exists ((norm w) ^+2 *: p *m A').
  rewrite -mulmxA mulmxE AA' mulmx1 scalerA.
  rewrite mulrC divrr ?scale1r // unitfE expf_eq0 /= norm_eq0.
  apply: contra rotf; rewrite fexp_skew => /eqP ->.
  by rewrite skew_mx0 emx3a0.
(* NB: corresponds to [murray], exercise 9, p.75 *)
(* NB: formula for the inverse matrix in
   [Introduction to Robotics: Mechanics, Planning, and Control,
    F.C. Park, K. Lynch, Mar. 14 2012] *)
exists (etwist_is_onto_SE_mat_inv a w); rewrite HA.
apply: (etwist_is_onto_SE_matP a0 _).
by rewrite norm_normalize // vaxis_euler_neq0 // rot_of_hom_SO.
Qed.

Lemma image_skew_mx (w : 'rV[R]_3) (w0 : w != 0) : (\S(w) == w^C)%MS.
Proof.
have rank_w : \rank (w)%MS = 1%N by rewrite rank_rV w0.
have rank_wC : \rank (w^C)%MS = 2%N by rewrite mxrank_compl rank_w.
have rank_kskew : \rank (kermx \S(w)) = 1%N by rewrite -[RHS]rank_w (eqmx_rank (kernel_skew_mx w0)).
have rank_skew : \rank \S(w) = 2%N.
  move: rank_kskew; rewrite mxrank_ker => /eqP.
  rewrite -(eqn_add2r (\rank \S(w))) subnK; last by rewrite rank_leq_row.
  rewrite add1n => /eqP[] <-; by apply/eqP.
move: (kernel_skew_mx w0) => H.
Abort.

End exponential_coordinates_rigid.

Notation "'`e$(' a ',' t ')'" := (etwist a t) (format "'`e$(' a ','  t ')'").

(* [murray] example 2.6 *)
Module TwistComputationExample.
Section example.
Variable R : realType.
Let vector := 'rV[R]_3.
Variables a1 a2 : R.
Variable a : angle R.
Hypothesis a0 : a != 0.

Definition P20 := row3 (a1 + a2 * cos a) (a2 * sin a) 0.

Definition w : vector := 'e_2%:R.

Let A_inv := etwist_is_onto_SE_mat_inv a w.

Definition v := ((norm w)^+2 *: P20) *m A_inv.

Lemma vP : v = row3 ((a1 + a2) * sin a / (2%:R * (1 - cos a))) (- (a1 - a2) / 2%:R) 0 :> vector.
Proof.
rewrite /v normeE expr1n scale1r /P20.
rewrite /A_inv /etwist_is_onto_SE_mat_inv.
rewrite mulmxDr mulmxBr.
rewrite mul_mx_scalar row3Z mulr0.
rewrite -scalemxAr scalemxAl row3Z mulr0 skew_mxE crossmulE !mxE /=. Simp.r. rewrite /=.
rewrite -scaleN1r row3Z !mulN1r opprK oppr0 row3D addr0.
rewrite -scalemxAr scalemxAl expr2 -mulmxE mulmxA -scalemxAl.
rewrite (skew_mxE (row3 _ _ _)) crossmulE !mxE /=. Simp.r.
rewrite -scalemxAl skew_mxE crossmulE !mxE /=. Simp.r.
rewrite row3Z mulr0 row3D addr0.
case/boolP : (a == pi) => [/eqP ->|api].
  rewrite cot_half_angle sinpi cospi !(mulr0,addr0,subr0,oppr0,add0r,mul0r,mulrN1).
  rewrite mulrN subrr.
  by rewrite mulrC.
congr row3; last first.
  rewrite mulrN mulrBl opprB -!addrA addrC !addrA -mulrA subrK.
  rewrite cot_half_angle' -!mulrA (mulrCA _ a2) mulVr ?mulr1; last first.
    by rewrite unitfE sin_eq0 negb_or a0 api.
  rewrite addrC -mulrBr opprD mulrDl mul1r -!addrA (addrCA _ (- a1)) (mulrC _ a2) subrr addr0.
  by rewrite -mulNr opprB mulrC.
rewrite mulrN mulrBl opprB -!addrA addrC !addrA -mulrA subrK.
rewrite -(mulrA _ (cot _ )) -mulrDr.
rewrite invrM; last 2 first.
  by rewrite unitfE pnatr_eq0.
  rewrite unitfE subr_eq0; apply: contra a0.
  by move/eqP/esym/cos1_angle0/eqP.
rewrite ![in RHS]mulrA [in RHS]mulrC; congr (_ * _).
rewrite -[in RHS]mulrA -cot_half_angle.
rewrite mulrDr addrCA [in RHS]mulrDl (mulrC _ a1); congr (_ + _).
rewrite mulrCA -mulrDr; congr (_ * _).
apply/eqP.
rewrite eq_sym -subr_eq.
rewrite -{1}(mulr1 (cot (half_angle a))) -mulrBr.
rewrite cot_half_angle -mulrA mulVr ?mulr1 //.
  rewrite unitfE subr_eq0; apply: contra a0.
  by move/eqP/esym/cos1_angle0/eqP.
Qed.

End example.
End TwistComputationExample.

Module Screw.
Section screw_definition.
Variable R : rcfType.
Record t := mk {
  l : Line.t R (* axis *) ;
  a : angle R (* magnitude *) ;
  h : R (* pitch *) }.
End screw_definition.
End Screw.

Section screw_motion.

Variable R : realType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* rotation by an amount a about the axis w follows by a translation ha parallel to w *)
Definition screw_motion (s : Screw.t R) (p : point) :=
  let: (l, a, h) := (Screw.l s, Screw.a s, Screw.h s) in
  let (p0, w) := (\pt( l ), \vec( l )) in
  p0 + (p - p0) *m `e^(a, w) + (h * rad a) *: w.

(* the rbt given by a screw *)
Definition hom_screw_motion s : 'M[R]__ :=
  let l := Screw.l s in let a := Screw.a s in let h := Screw.h s in
  let q := \pt( l ) in let w := \vec( l ) in
  hom (`e^(a, w)) (q *m (1 - `e^(a, w)) + (h * rad a) *: w).

Lemma hom_screwa0 s : Screw.a s = 0 -> hom_screw_motion s = hom 1 0.
Proof.
move=> a0.
rewrite /hom_screw_motion a0 emx30M subrr mulmx0 add0r.
rewrite (_ : rad 0 = 0) ?mulr0 ?scale0r //; by apply/eqP; rewrite rad_eq0.
Qed.

Lemma hom_screww0 s : \vec( Screw.l s ) = 0 -> hom_screw_motion s = hom 1 0.
Proof. move=> w0; by rewrite /hom_screw_motion w0 skew_mx0 emx3a0 subrr mulmx0 add0r scaler0. Qed.

Lemma hom_screwE s (p : point) (w1 : norm \vec( Screw.l s) = 1) :
  let l := Screw.l s in let a := Screw.a s in let h := Screw.h s in
  let q := \pt( l ) in let w := \vec( l ) in
  SE.ap_point (SE.mk (q *m (1 - `e^(a, w)) + (h * rad a) *: w)
                     (eskew_is_SO a w1)) p = screw_motion s p.
Proof.
move=> l a h q w.
rewrite SE.ap_pointE mul_mx_row add_row_mx mulmx0 add0r to_hpointK.
rewrite addrA /hom_screw_motion /=; apply/rowP => i.
rewrite mxE [in RHS]mxE; congr (_ + _).
rewrite mulmxBr mulmx1 addrCA mxE [in RHS]mxE; congr (_ + _).
by rewrite mulmxBl.
Qed.

Lemma hom_screw_motion_etwist s :
  let: (l, a, h) := (Screw.l s, Screw.a s, Screw.h s) in
  let (q, w) := (\pt( l ), \vec( l )) in
  let v := - w *v q + h *: w in
  hom_screw_motion s = `e$(a, \T(v, w)) :> 'M_4.
Proof.
rewrite /=.
set l := Screw.l s.
set a := Screw.a s.
set h := Screw.h s.
set q := \pt( l ).
set w := \vec( l ).
set v := _ + _.
rewrite /etwist /hom_twist.
case: ifPn => [/eqP|]; rewrite ang_of_twistE => w0.
  by rewrite hom_screww0 // /v lin_of_twistE w0 crossmulNv crossmul0v oppr0 scaler0 addr0 scaler0.
rewrite /hom_screw_motion.
rewrite -/l -/a -/h -/q -/w.
congr hom.
rewrite {1}/v.
rewrite lin_of_twistE.
rewrite [w *v _]linearD /=.
rewrite crossmulvZ crossmulvv scaler0 addr0.
rewrite crossmulNv crossmulvN.
rewrite double_crossmul dotmulvv.
rewrite [in X in _ = _ *: (X + _)]mulNmx.
rewrite [in X in _ = _ *: (X + _)]mulmxBl.
rewrite opprB -addrA.
rewrite scalerDr -scalemxAl scalerA [in X in _ = X + _]mulrC divrr ?scale1r; last first.
  by rewrite unitfE expf_eq0 /= norm_eq0.
congr (_ + _).
rewrite -[in X in _ = _ *: (_ + X)]scalemxAl.
rewrite mulmxDl.
rewrite -[in X in _ = _ *: (_ + X)]scalemxAl.
rewrite (mulmxA w) dotmulP dotmulvv mul_scalar_mx scalerA.
rewrite [in X in _ = _ *: (_ + X)]scalerDr addrA addrC.
rewrite scalerDr.
rewrite 2!scalerA.
rewrite [in X in _ = X + _]mulrA.
rewrite [in X in _ = X + _]mulrC.
rewrite -2!(mulrA (rad a)) -(mulrA h) divrr ?mulr1; last by rewrite unitfE expf_eq0 /= norm_eq0.
rewrite mulrC -[LHS]addr0.
congr (_ + _).
rewrite mulmxBr mulmx1.
rewrite -rodrigues_genP /rodrigues_gen.
rewrite crossmulvZ crossmulvv 2!scaler0 addr0.
rewrite dotmulZv dotmulvv.
rewrite !scalerA mulrAC mulrA.
rewrite subrK.
rewrite subrr oppr0 add0r.
rewrite crossmulC mulNmx scalerN.
by rewrite crossmulC opprK -skew_mxE -mulmxA (mulmxA \S( w )) skew_mxT mul0mx mulmx0 scaler0 oppr0 scaler0.
Qed.

End screw_motion.

Section screw_coordinates_of_a_twist.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* [murray] 2.43, p.47 *)
Definition axis (t : TwistCoor.t R) : Line.t R :=
  let w := \w( t ) in let v := \v( t ) in
  if w == 0 then
    Line.mk 0 v
  else
    Line.mk ((norm w)^-2 *: (w *v v)) w.

Lemma point_axis_nolin w : w != 0 -> \pt( axis \T(0, w) ) = 0.
Proof.
move=> w0; rewrite /axis ang_of_twistE (negbTE w0) /=.
by rewrite lin_of_twistE /= crossmulv0 scaler0.
Qed.

(* [murray] 2.42, p.47 *)
Definition pitch (t : TwistCoor.t R) : R :=
  let w := \w( t ) in let v := \v( t ) in
  (norm w)^-2 *: v *d w. 

Lemma pitch_nolin (w : 'rV[R]_3) : pitch \T(0, w) = 0.
Proof. by rewrite /pitch ang_of_twistE lin_of_twistE scaler0 dotmul0v. Qed.

(* twist of a revolute joint *)
Definition rjoint_twist (w : vector) (q : point) := \T(- w *v q, w).

(* twist of a prismatic joint *)
Definition pjoint_twist (v : vector) := \T(v, 0).

Lemma pitch_perp (w u : 'rV[R]_3) : norm w = 1 -> pitch (rjoint_twist w u) = 0.
Proof.
move=> w1; rewrite /pitch ang_of_twistE lin_of_twistE w1 expr1n invr1 scale1r.
by rewrite {1}crossmulC crossmulvN opprK -dot_crossmulC crossmulvv dotmulv0.
Qed.

(* [murray] 2.44, p.48 *)
Definition magnitude (t : TwistCoor.t R) : R :=
  let w := \w( t ) in let v := \v( t ) in
  if w == 0 then norm v else norm w.

Lemma magnitudeZ (t : TwistCoor.t R) a : 0 < a ->
  magnitude ((a *: t) : 'M__) = a * magnitude t.
Proof.
move=> a_gt0.
rewrite /magnitude.
case/boolP : (a == 0) => [/eqP ->|a0].
  by rewrite scale0r mul0r ang_of_twist0 eqxx lin_of_twist0 norm0.
rewrite ang_of_twistZ scaler_eq0 (negbTE a0) /=.
case: ifPn => M0.
  by rewrite lin_of_twistZ normZ gtr0_norm.
by rewrite normZ gtr0_norm.
Qed.

(* unit twist: [murray] p.49 (p.48 also) *)
Definition utwist (t : TwistCoor.t R) := (magnitude t == 1).

Lemma utwistE (t : TwistCoor.t R) : utwist t =
  (norm \w( t ) == 1) || ((norm \w( t ) == 0) && (norm \v( t ) == 1)).
Proof.
apply/idP/idP.
- rewrite /utwist /magnitude.
  case: ifPn => [/eqP -> ->|w0 ->]; by rewrite norm_eq0 ?eqxx /= ?orbT.
- case/orP => [w1|/andP[w0 v1]].
    rewrite /utwist /magnitude; case: ifPn => [w0| //].
    by rewrite (eqP w0) norm0 eq_sym (negbTE (@oner_neq0 _)) in w1.
  by rewrite /utwist /magnitude -{1}norm_eq0 w0.
Qed.

(* [murray] p. 48
   if we choose [a unit twist t], then a twist ta has magnitude a *)
Lemma magn_of_utwistZ a (t : TwistCoor.t R) : 0 < a -> utwist t ->
  magnitude (a *: t ) = a.
Proof. move=> a0 Ht; by rewrite magnitudeZ // (eqP Ht) mulr1. Qed.

End screw_coordinates_of_a_twist.

Section screw_coordinates_of_a_twist_continued.

Variable R : realType.

Definition ScrewTwist (t : TwistCoor.t R) :=
  Screw.mk (axis t) (Rad.angle_of (pitch t)) (magnitude t).

End screw_coordinates_of_a_twist_continued.

Section screw_motion_utwist.

Variable R : realType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* [murray] proposition 2.10, p.48 *)
(* TODO: not yet right *)
Lemma hom_screw_motion_eutwist (s : Screw.t R) :
  let a := Screw.a s in
  exists t' : TwistCoor.t R, (*utwist t' /\*)
  hom_screw_motion s = `e$(a, \T( \v( t'), \w( t' ))).
Proof.
move=> a.
set l := Screw.l s.
set h := Screw.h s.
set w := \vec( l ).
set q := \pt( l ).
set v := - w *v q + h *: w.
case/boolP : (w == 0) => [/eqP|]w0.
  exists \T(v, 0).
  rewrite ang_of_twistE lin_of_twistE /v w0 crossmulNv crossmul0v oppr0 scaler0 addr0 etwistv0.
  by rewrite hom_screww0.
exists \T(v, w).
by rewrite lin_of_twistE ang_of_twistE hom_screw_motion_etwist.
Qed.

End screw_motion_utwist.

(* wip *)
Section etwist_alt.

Variable R : realType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

Lemma etwistE a (v w : 'rV[R]_3) :
  `e$(a , \T(v, w)) =
  hom (`e^(a, w)) (if w == 0 then (rad a) *: v else
                  (rad a * pitch \T(v, w)) *:  w +
                    \pt( axis \T(v, w) ) *m (1 - `e^(a, w))).
Proof.
rewrite /etwist /hom_twist ang_of_twistE; case: ifPn => [/eqP ->|w0].
  by rewrite lin_of_twistE skew_mx0 emx3a0.
congr hom.
rewrite lin_of_twistE.
rewrite -scalemxAl mulmxA dotmulP scalemxAl scalerDr -scalemxAl.
rewrite (scalerA _ (rad a)) (mulrC _ (rad a)).
rewrite -(scalerA (rad a) (norm w ^+ 2)^-1).
rewrite mul_scalar_mx (scalerA _ (v *d w) w) -(dotmulZv v _ w).
rewrite (_ : _ *d _ = pitch \T(v, w)); last by rewrite /pitch lin_of_twistE ang_of_twistE.
rewrite addrC.
rewrite scalerA.
rewrite /axis ang_of_twistE (negbTE w0) /=.
by rewrite lin_of_twistE -scalemxAl.
Qed.

Lemma etwist_Rz a (w : 'rV[R]_3) : w != 0 ->
  `e$(a, \T(0, w)) = hom `e^(a, w) 0.
Proof.
move=> w0; rewrite etwistE (negbTE w0) pitch_nolin mulr0.
by rewrite  scale0r add0r point_axis_nolin // mul0mx.
Qed.

End etwist_alt.

Section Chasles.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Variable f : 'DIso_3[R].
Let Q : 'M[R]_3 := ortho_of_iso f.
Let w := normalize (Aa.vaxis Q).
Let a := Aa.angle Q.
Hypothesis w0 : axial_vec Q != 0.
Hypothesis sina0 : sin a != 0.
Let api : a != pi.
Proof. apply: contra sina0 => /eqP ->; by rewrite sinpi. Qed.
Let vaxis0 : Aa.vaxis Q != 0.
Proof. 
by rewrite /Aa.vaxis (negbTE api) scaler_eq0 negb_or w0 andbT div1r invr_eq0 mulrn_eq0.
Qed.
Let w1 : norm w = 1. Proof. by rewrite norm_normalize. Qed.

(* [angeles] theorem 3.2.1, p.97: 
   the displacements of all the points of the body have the same projection onto e *)

Definition d0 := displacement f 0 *d w.

Lemma displacement_proj p : displacement f p *d w = d0.
Proof.
rewrite /dotmul; congr (fun_of_matrix _ 0 0).
rewrite (displacement_iso f 0 p) [in RHS]mulmxDl -[LHS](addr0); congr (_ + _).
rewrite -mulmxA (mulmxBl Q) mul1mx.
suff -> : Q *m w^T = w^T by rewrite subrr mulmx0.
move: (isRot_axis (angle_axis_isRot w0 (ortho_of_diso_is_SO f))).
rewrite -/w => Hw; rewrite -{1}Hw.
rewrite trmx_mul mulmxA mulmxE.
move: (ortho_of_iso_is_O f); rewrite orthogonalE => /eqP ->; by rewrite mul1mx.
Qed.

Definition axialdisp p := axialcomp (displacement f p) w.

Lemma axialdispE p : axialdisp p = d0 *: ((norm w)^-2 *: w).
Proof. 
rewrite /axialdisp /axialcomp dotmulC dotmulvZ displacement_proj mulrC -scalerA.
by rewrite (scalerA (norm w)^-1) -expr2 exprVn.
Qed.

Definition normdisp p := normalcomp (displacement f p) w.

Lemma decomp_displacement p :
  norm (displacement f p) ^+ 2 = norm (d0 *: (norm w ^- 2 *: w)) ^+2 + norm (normdisp p) ^+ 2.
Proof.
rewrite (decomp (displacement f p) w) normD -dotmul_cos axialnormal // mul0rn addr0.
by rewrite -/(normdisp p) -/(axialdisp p) axialdispE.
Qed.

Lemma MozziChasles_helper p : norm (displacement f p) = d0 -> normdisp p = 0.
Proof.
move=> Hp.
have := lerr (norm (d0 *: w) ^+ 2).
rewrite {1}normZ w1 mulr1 sqr_normr -{1}Hp decomp_displacement -ler_sub_addl.
rewrite w1 expr1n invr1 scale1r.
by rewrite subrr ler_eqVlt ltrNge sqr_ge0 orbF sqrf_eq0 norm_eq0 => /eqP.
Qed.

(* [angeles] theorem 3.2.2, p.97 *)
Lemma MozziChasles p : norm (displacement f p) = d0 ->
  colinear (displacement f p) w.
Proof.
move=> H.
by rewrite -(normalcomp_colinear _ (norm1_neq0 w1)) -/(normdisp p) MozziChasles_helper.
Qed.

End Chasles.

Section screw_axis_point_helper.

Variables (R : rcfType) (a : angle R).

Definition Ncos2 := (1 - cos a) *+ 2.

Definition N2cos := 1 - cos a *+ 2.

Lemma unitNcos2 (a0 : a != 0) : Ncos2 \is a GRing.unit.
Proof.
rewrite unitfE /Ncos2 mulrn_eq0 negb_or /= subr_eq0 eq_sym.
apply/eqP => /cos1_angle0; by apply/eqP.
Qed.

Lemma Ncos2V (a0 : a != 0) : (Ncos2^-1)%:M *m Ncos2%:M = 1 :> 'M_3.
Proof. by rewrite -scalar_mxM mulVr // unitNcos2. Qed.

Lemma N2cosNcos2 (a0 : a != 0) :
  N2cos - Ncos2^-1 * N2cos - N2cos / Ncos2 * N2cos = 0.
Proof.
rewrite (mulrC N2cos) -mulrA -{1}(mulKr (unitNcos2 a0) N2cos) -2!mulrBr.
apply/eqP; rewrite mulf_eq0 invr_eq0.
move: (unitNcos2 a0); rewrite unitfE => /negPf -> /=.
rewrite -{2}(mul1r N2cos) -2!mulrBl mulf_eq0 -addrA -opprB opprK subr_eq0.
by rewrite /Ncos2 {1}/N2cos mulrnBl addrAC eqxx.
Qed.

End screw_axis_point_helper.

Section screw_axis_point_def.

Variable R : rcfType.
Let point := 'rV[R]_3.
Variable f : 'DIso_3[R].
Let Q : 'M[R]_3 := ortho_of_iso f.
Let a := Aa.angle Q.

Definition screw_axis_point (p : point) : point :=
  1 / Ncos2 a *: (p *m Q - f p) *m (Q - 1)^T.

End screw_axis_point_def.

Section screw_axis_point.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Variable f : 'DIso_3[R].
Let Q : 'M[R]_3 := ortho_of_iso f.
Hypothesis w0 : axial_vec Q != 0.
Let w : 'rV[R]_3 := normalize (Aa.vaxis Q).
Let a := Aa.angle Q.
Hypothesis sina0 : sin a != 0.
Let a0 : a != 0.
Proof. apply: contra sina0 => /eqP ->; by rewrite sin0. Qed.
Let api : a != pi.
Proof. apply: contra sina0 => /eqP ->; by rewrite sinpi. Qed.
Let Htmp0 : Aa.vaxis Q != 0.
Proof.
rewrite /Aa.vaxis.
rewrite (negbTE api).
by rewrite scaler_eq0 negb_or w0 andbT div1r invr_eq0 mulrn_eq0 //=.
Qed.
Let w1 : norm w = 1. 
Proof. rewrite norm_normalize //. Qed.

Lemma wTwQN1 : (w^T *m w) *m (Q - 1)^T = 0.
Proof.
move: (isRot_exp_eskew' w1 (angle_axis_isRot w0 (ortho_of_diso_is_SO f))).
rewrite -/Q => ->; rewrite linearD /=.
rewrite [in X in _ *m (_ + X)]linearN /= trmx1.
rewrite mulmxBr mulmx1 /eskew'.
rewrite -addrA linearD /= mulmxDr trmx_mul trmxK.
rewrite mulmxE -expr2 (mulmx_tr_uvect w1) //.
rewrite addrC addrA (addrC (- _)) subrr add0r.
rewrite linearD /= [w]lock 2!linearZ /= tr_skew scalerN -lock.
rewrite mulrDr -scalerAr linearD /= trmx1 linearN /= trmx_mul trmxK mulrBr.
rewrite mulr1 -expr2 (mulmx_tr_uvect w1) // subrr scaler0 add0r.
by rewrite mulrN -scalerAr -mulmxE -mulmxA skew_mxE crossmulvv mulmx0 scaler0 oppr0.
Qed.

Lemma QN1wTw : (Q - 1)^T *m (w^T *m w) = 0.
Proof.
move: (isRot_exp_eskew' w1 (angle_axis_isRot w0 (ortho_of_diso_is_SO f))).
rewrite -/Q => ->; rewrite linearD /=.
rewrite mulmxDl [in X in _ + X = _]linearN /= trmx1 mulNmx mul1mx.
rewrite linearD /= [w]lock linearZ /= tr_skew scalerN mulmxDl -lock.
rewrite mulNmx.
rewrite -scalemxAl !mulmxA skew_mxT mul0mx scaler0 subr0.
rewrite linearD /= trmx_mul trmxK.
rewrite -mulmxA mulmxDl mulmxE -expr2 (mulmx_tr_uvect w1) //.
rewrite addrC addrA (addrC (- _)) subrr add0r.
rewrite linearZ /= -mulmxE -scalemxAl.
rewrite linearD /= trmx1 linearN /= trmx_mul trmxK mulmxBl.
rewrite mul1mx mulmxE -expr2 (mulmx_tr_uvect w1) //.
by rewrite subrr scaler0.
Qed.

Definition screw_axis_point_mat :=
  let A := row_mx (Q - 1) w^T in A *m A^T.

Definition screw_axis_point_mat_inv : 'M_3 :=
  (Ncos2 a)^-1 *: 1 + (N2cos a) / (Ncos2 a)*: w^T *m w.

Lemma screw_axis_point_matE : let A := row_mx (Q - 1) w^T in
  A *m A^T = (Ncos2 a) *: 1 - (N2cos a) *: w^T *m w.
Proof.
move=>A.
rewrite /A tr_row_mx mul_row_col trmxK linearD /= linearN /= trmx1.
rewrite mulmxBr mulmx1 opprB mulmxBl mul1mx.
move: (ortho_of_iso_is_O f); rewrite -/Q orthogonalE mulmxE => /eqP ->.
rewrite addrA (addrC (1 - _)) addrA.
rewrite (_ : 1 + 1 = 2%:R) //.
rewrite /Ncos2 mulrnBl scalerBl -2!addrA -[in RHS]addrA; congr (_ + _).
  rewrite scalemx1.
  by apply/matrix3P/and9P; split; apply/eqP; rewrite !mxE ?eqxx /= ?mulr1n // ?mulr0n // addr0.
rewrite addrA.
move: (isRot_exp_eskew' w1 (angle_axis_isRot w0 (ortho_of_diso_is_SO f))).
rewrite -/Q -/a => HQ.
rewrite {1}HQ.
rewrite /eskew'.
rewrite -(addrA (w^T *m w)).
rewrite [w]lock linearD /= trmx_mul trmxK opprD addrC 2!addrA subrr add0r.
rewrite linearD /= [w]lock 2!linearZ /= 2!linearD /= trmx1 -!lock.
move: (isRot_exp_eskew' w1 (angle_axis_isRot w0 (ortho_of_diso_is_SO f))).
rewrite -/Q -/a => ->.
rewrite opprD !addrA addrC !addrA tr_skew.
rewrite (scalerN (sin a) \S( w )) opprK.
rewrite (addrC (- (sin a *: _))) subrK.
rewrite linearN /= trmx_mul trmxK opprD addrA addrAC -scaleNr -scalerDl.
rewrite -mulr2n scalerBr scalemx1 scalemx1 -addrA; congr (_ + _).
  apply/matrix3P/and9P; split; apply/eqP; by rewrite !mxE ?eqxx ?mulr1n ?mulr0n // ?oppr0 // mulNrn.
rewrite -scalemxAl /N2cos [in RHS]scalerBl scale1r opprB; congr (_ + _).
by rewrite mulNrn scaleNr opprK.
Qed.

Lemma screw_axis_point_Vmat :
  screw_axis_point_mat_inv * screw_axis_point_mat = 1.
Proof.
rewrite /screw_axis_point_mat /screw_axis_point_mat_inv screw_axis_point_matE !scalemx1 -!mulmxE.
rewrite mulmxBr mulmxDl Ncos2V // -[RHS]addr0 -addrA; congr (_ + _).
rewrite mul_mx_scalar -{1}scalemxAl {1}(mulrC (N2cos a)) scalerA mulrA mulrV ?unitNcos2 // mul1r.
rewrite mulmxDl.
rewrite opprD addrA mul_scalar_mx -[in X in X - _ = 0]scalemxAl scalerA.
rewrite -scalerBl.
rewrite -3![in X in _ - X = 0]scalemxAl.
rewrite -[in X in _ - X = 0]scalemxAr.
rewrite [in X in _ - X = 0]scalerA.
rewrite mulmxE -expr2 (mulmx_tr_uvect w1) // -scalerBl.
by apply/eqP; rewrite scaler_eq0 (N2cosNcos2 a0) eqxx.
Qed.

Lemma screw_axis_point_matV :
  screw_axis_point_mat * screw_axis_point_mat_inv = 1.
Proof.
rewrite /screw_axis_point_mat /screw_axis_point_mat_inv screw_axis_point_matE !scalemx1 -!mulmxE.
rewrite mulmxBl mulmxDr {1}mulmxE (scalar_mx_comm ((Ncos2 a)^-1)) -{1}mulmxE Ncos2V //.
rewrite -[RHS]addr0 -addrA; congr (_ + _).
rewrite mul_scalar_mx -{1}scalemxAl scalerA mulrC -mulrA mulVr ?unitNcos2 // mulr1.
rewrite mulmxDr.
rewrite opprD addrA mul_mx_scalar -[in X in X - _ = 0]scalemxAl scalerA.
rewrite -scalerBl.
rewrite -3![in X in _ - X = 0]scalemxAl.
rewrite -[in X in _ - X = 0]scalemxAr.
rewrite [in X in _ - X = 0]scalerA.
rewrite mulmxE -expr2 (mulmx_tr_uvect w1) // -scalerBl.
by apply/eqP; rewrite scaler_eq0 (mulrC (N2cos a)) N2cosNcos2 // eqxx.
Qed.

Lemma screw_axis_point_mat_unit :
  screw_axis_point_mat \is a GRing.unit.
Proof.
apply/unitrP; exists screw_axis_point_mat_inv.
by rewrite screw_axis_point_Vmat // screw_axis_point_matV.
Qed.

Lemma screw_axis_point_mat_invE :
  let A := row_mx (Q - 1) w^T in
  (A *m A^T)^-1 = screw_axis_point_mat_inv.
Proof.
move=> A.
by rewrite -[LHS]mul1r -screw_axis_point_Vmat // mulrK // screw_axis_point_mat_unit.
Qed.

Lemma screw_axis_point_invariant (p q : point) :
  screw_axis_point f p = screw_axis_point f q.
Proof.
rewrite /screw_axis_point -!scalemxAl -/Q; congr (_ *: _); apply/eqP.
rewrite -subr_eq0 -mulmxBl opprB -addrA (addrA (- f p)) addrCA -mulmxBl.
by rewrite -img_vec_iso addrCA !addrA subrr add0r subrr mul0mx.
Qed.

(* [angeles] Sect. 3.2.1 (the screw of a rigid-body motion) *)
Lemma screw_axis_pointE p0 q :
  p0 *d w = 0 (* p0 is the closed point to the origin *) ->
  norm (displacement f p0) = d0 f ->
  p0 = screw_axis_point f q.
Proof.
move=> p0e0 fp0e0.
have _(*?*) : relative_displacement f (f p0) p0 = 0.
  rewrite /relative_displacement -/(displacement f p0).
  move: (MozziChasles w0 sina0 fp0e0).
  rewrite -(normalcomp_colinear _ (norm1_neq0 w1)) // => /eqP H1.
  rewrite (decomp (displacement f p0) w) H1 addr0.
  rewrite /axialcomp -scalemxAl mulmxBr mulmx1.
  move: (angle_axis_isRot w0 (ortho_of_diso_is_SO f)); rewrite -/Q -/a -/w.
  rewrite normalizeI // => /isRot_axis ->; by rewrite subrr scaler0.
have step2 : displacement f q + relative_displacement f p0 q = displacement f q *m (w^T *m w).
  transitivity (displacement f p0 *m w^T *m w).
    rewrite -(displacement_iso f p0 q) {1}(decomp (displacement f p0) w).
    move/(MozziChasles w0 sina0) : fp0e0.
    rewrite -normalcomp_colinear; last by rewrite normalize_eq0.
    move/eqP => ->.
    by rewrite addr0 axialcompE w1 expr1n invr1 scale1r.
  by rewrite dotmulP mulmxA dotmulP 2!(displacement_proj w0).
have {step2}step2 : p0 *m (Q - 1) = q *m (Q - 1) - displacement f q *m (1 - w^T *m w).
  rewrite [in X in _ = _ - X]mulmxBr mulmx1 -{}step2.
  rewrite (opprD (displacement f q)) opprK addrCA addrA subrr add0r.
  by rewrite /relative_displacement -/Q mulmxBl addrCA subrr addr0.
set A := row_mx (Q - 1) w^T.
set b : 'rV[R]_4 := row_mx (q *m (Q - 1) - displacement f q *m (1 - w^T *m w)) 0.
have step3 : b *m A^T = (q *m (Q - 1) - displacement f q) *m (Q - 1)^T.
  rewrite /A tr_row_mx trmxK.
  rewrite /b (mul_row_col (q *m (Q - 1) - _)) mul0mx addr0.
  rewrite (mulmxBr (displacement f q)) mulmx1 opprB addrA addrAC.
  rewrite mulmxDl -mulmxA.
  rewrite wTwQN1.
  by rewrite mulmx0 addr0.
have {step2} : p0 *m A = b.
  rewrite /A mul_mx_row /b {}step2; congr row_mx.
  by rewrite dotmulP p0e0 (mx11_scalar 0) mxE.
move/(congr1 (fun x => x *m A^T)).
move/(congr1 (fun x => x *m screw_axis_point_mat_inv)).
rewrite /screw_axis_point.
rewrite -2!mulmxA.
rewrite -screw_axis_point_mat_invE // mulmxV; last by rewrite screw_axis_point_mat_unit.
rewrite mulmx1 screw_axis_point_mat_invE //.
rewrite step3.
rewrite mulmxBr mulmx1 /displacement opprB addrA subrK.
rewrite /screw_axis_point_mat_inv mulmxDr.
rewrite -[in X in _ = _ + X -> _]mulmxA.
rewrite -[in X in _ = _ + X -> _]scalemxAl.
rewrite -[in X in _ = _ + X -> _]scalemxAr.
rewrite QN1wTw scaler0 mulmx0 addr0.
by rewrite scalemx1 mul_mx_scalar div1r scalemxAl => ?.
Qed.

Lemma screw_axis_pointE1 q : let p0 := screw_axis_point f q in
  p0 *d w = 0.
Proof.
apply/eqP; rewrite /screw_axis_point -scalemxAl dotmulZv mulf_eq0.
apply/orP; right; rewrite -/Q /dotmul -mulmxA -trmx_mul mulmxBr mulmx1.
have -> : w *m Q = w.
  by rewrite /w /normalize -scalemxAl Aa.vaxis_ortho_of_iso // ortho_of_diso_is_SO.
by rewrite subrr trmx0 mulmx0 mxE.
Qed.

Lemma screw_axis_pointE2 q : let p0 := screw_axis_point f q in
  colinear (displacement f p0) w.
Proof.
red.
set p0 := screw_axis_point f q.
Abort.

End screw_axis_point.
