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

Require Import aux angle euclidean3 skew robot.

(*
 OUTLINE:
 1. sections twist, taylor expansion of the exponential map, 
     exponential coordinates for rbt using taylor expansion, 
     exponential coordinates for rbt using exponential coordinates for rotation (def. only)
 2. section screw, equivalence screw motion <-> exponential coordinates for rbt
 3. section chasles
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
move=> w1; rewrite expr2 -mulmxE -mulmxA (mulmxA w) (mx11_scalar (w *m _)).
by rewrite -/(w *d w) dotmulvv w1 expr1n mul1mx.
Qed.

Module Twist.
Section Twist.
Variable R : rcfType.
Let vector := 'rV[R]_3.
Record t := mk {
  lin : vector ; (* linear vel. *)
  ang : vector (* angular vel. *) }.
End Twist.
End Twist.

Coercion Twistmx (R : rcfType) (x : Twist.t R) : 'M_4 := block_mx \S(Twist.ang x) 0 (Twist.lin x) 0.
Notation "'\T(' v , w ')'" := (Twist.mk v w)
  (at level 3, w, v at next level, format "'\T(' v ,  w ')'") : ring_scope.

Section twists.

Variable R : rcfType.

Lemma twistZ (a : R) v w : a *: (\T(v, w) : 'M_4) = \T((a *: v), (a *: w)).
Proof. by rewrite /Twistmx /= (scale_block_mx a \S(w)) skew_mxZ 2!scaler0. Qed.

Definition lie_bracket (t1 t2 : Twist.t R) := t1 *m t2 - t2 *m t1.

Local Notation "[ t1 , t2 ]" := (lie_bracket t1 t2).

Lemma lie_bracketE t1 t2 :
  let: \T(v1, w1) := t1 in
  let: \T(v2, w2) := t2 in
  [ t1 , t2 ] = block_mx \S( w1 *v w2 ) 0 (w1 *v w2 - w2 *v w1) 0.
Proof.
Abort.

Definition ang_of_twist (M : 'M[R]_4) := unskew (@ulsubmx _ 3 1 3 1 M).

Lemma ang_of_twist0 : ang_of_twist 0 = 0.
Proof. by rewrite /ang_of_twist -(@block_mx0 _ 3 1 3 1) block_mxKul unskew0. Qed.

Lemma ang_of_twistE (v w : 'rV[R]_3) : ang_of_twist \T(v, w) = w.
Proof. by rewrite /ang_of_twist block_mxKul /= skew_mxK. Qed.

Definition lin_of_twist (M : 'M[R]_4) := @dlsubmx _ 3 1 3 1 M.

Lemma lin_of_twist0 : lin_of_twist 0 = 0.
Proof. by rewrite /lin_of_twist -(@block_mx0 _ 3 1 3 1) block_mxKdl. Qed.

Lemma lin_of_twistE (v w : 'rV[R]_3) : lin_of_twist \T(v, w) = v.
Proof. by rewrite /lin_of_twist block_mxKdl /=. Qed.

Definition se3 := [qualify M : 'M[R]_4 |
  [&& @ulsubmx _ 3 1 3 1 M \is 'so[R]_3,
      @ursubmx _ 3 1 3 1 M == 0 &
      @drsubmx _ 3 1 3 1 M == 0] ].
Fact se3_key : pred_key se3. Proof. by []. Qed.
Canonical se3_keyed := KeyedQualifier se3_key.

Lemma se3E (M : 'M[R]_4) :
  (M \is se3) = (M == \T(@dlsubmx _ 3 1 3 1 M, unskew (@ulsubmx _ 3 1 3 1 M))).
Proof.
apply/idP/idP => [|/eqP ->].
  rewrite qualifE => /and3P[].
  rewrite qualifE => /eqP H1 /eqP H2 /eqP H3.
  rewrite -{1}(@submxK _ 3 1 3 1 M) H2 H3 /Twistmx /=.
  rewrite unskewK // qualifE; by apply/eqP.
rewrite qualifE /Twistmx block_mxKul /= block_mxKur /= eqxx /=.
by rewrite block_mxKdr eqxx andbT anti_skew.
Qed.

Lemma ang_of_twistZ k (M : 'M[R]_4) : ang_of_twist (k *: M) = k *: ang_of_twist M.
Proof.
rewrite /ang_of_twist -{1}(@submxK _ 3 1 3 1 M).
by rewrite (scale_block_mx k (@ulsubmx _ 3 1 3 1 M)) block_mxKul unskew_mxZ.
Qed.

Lemma lin_of_twistZ k (M : 'M[R]_4) : lin_of_twist (k *: M) = k *: lin_of_twist M.
Proof.
rewrite /lin_of_twist -{1}(@submxK _ 3 1 3 1 M).
by rewrite (scale_block_mx k (@ulsubmx _ 3 1 3 1 M)) block_mxKdl.
Qed.

End twists.

Notation "''se3[' R ]" := (se3 R)
  (at level 8, format "''se3[' R ]") : ring_scope.

Section sample_rigid_transformation.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types v w : vector.

Definition rigid_trans w v := hom 1 (w *v v).

Definition inv_rigid_trans w v := hom 1 (- w *v v).

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
by rewrite unitmxE /rigid_trans (det_lblock 1 (w *v v)) 2!det1 mulr1 unitr1.
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

Definition expt M i := i`!%:R^-1 *: M ^+ i.

Lemma exptE M i : expt M i = i`!%:R^-1 *: M ^+ i.
Proof. by []. Qed.

Lemma exptM0 M : expt M 0 = 1.
Proof. by rewrite exptE expr0 fact0 invr1 scale1r. Qed.

Lemma expt0k k : expt 0 k = (k == O)%:R.
Proof.
rewrite exptE expr0n.
case: k => [|k]; first by rewrite fact0 invr1 scale1r.
by rewrite scaler0.
Qed.

Lemma exptS M i : expt M i.+1 = i.+1%:R^-1 *: M * expt M i.
Proof.
rewrite /expt -scalerAr -scalerAl -exprS scalerA; congr (_ *: _).
by rewrite factS natrM invrM // unitfE pnatr_eq0 // -lt0n fact_gt0.
Qed.

Lemma expt1 M : expt M 1 = M.
Proof. by rewrite exptS exptM0 mulr1 invr1 scale1r. Qed.

Lemma expt_mulmulV M (g : 'M[R]_n.+1) i : g \in unitmx ->
  expt (g * M * g^-1) i = g * expt M i * g^-1.
Proof. move=> Hg; by rewrite /expt expr_mulmulV // -scalerAr scalerAl. Qed.

Definition expmx M k := \sum_(i < k) expt M i.

Lemma expmxM0 M : expmx M 0 = 0.
Proof. by rewrite /expmx big_ord0. Qed.

Lemma expmxS M k : expmx M k.+1 = expmx M k + expt M k.
Proof. by rewrite /expmx big_ord_recr. Qed.

Lemma expmx0k k : expmx 0 k = (k != O)%:R.
Proof.
elim: k => [|k ih]; first by rewrite expmxM0 eqxx.
by rewrite expmxS ih /= expt0k -natrD addn_negb.
Qed.

Lemma expSmx M k : expmx M k.+1 = expt M 0 + \sum_(i < k) expt M i.+1.
Proof. by rewrite /expmx big_ord_recl. Qed.

Lemma expmx1 M : expmx M 1 = 1.
Proof. by rewrite expmxS expmxM0 add0r exptM0. Qed.

Lemma expmx2 M : expmx M 2 = 1 + M.
Proof. by rewrite expmxS expmx1 expt1. Qed.

Lemma expmx_mulmulV M k (g : 'M[R]_n.+1) : g \in unitmx ->
  expmx (g * M * g^-1) k = g * expmx M k * g^-1.
Proof.
move=> Hg; rewrite /expmx big_distrr /= big_distrl /=.
apply/eq_bigr => i _; by rewrite expt_mulmulV.
Qed.

End taylor_exponential.

(* exponential coordinates for rbt using taylor expansion of the exponential function *)
(* [murray] proposition 2.8, p. 41-42 *)
Section exponential_coordinates_rigid_using_taylor.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types w v : vector.

Lemma exp_twist0v v n : (\T(v, 0) : 'M_4) ^+ n.+2 = 0.
Proof.
elim: n => [|n ih]; last by rewrite exprS ih mulr0.
rewrite expr2 /Twistmx skew_mx0 -mulmxE.
set a := 0. set b := 0.
by rewrite (mulmx_block a b v _ a b v _) /a /b !(mulmx0,addr0,mul0mx) block_mx0.
Qed.

(* [murray] eqn 2.32, p.41 *)
Lemma expmx_twist0E v k : expmx \T(v, 0) k.+2 = hom 1 v.
Proof.
rewrite /expmx 2!big_ord_recl big1 ?addr0; last first.
  move=> /= i _; by rewrite exptE exp_twist0v scaler0.
rewrite liftE0 eqxx /expt factS fact0 expr0 expr1 invr1 2!scale1r /Twistmx skew_mx0.
by rewrite -idmxE (@scalar_mx_block _ 3 1 1) (add_block_mx 1 0 0 1 0 _ v) !(addr0,add0r).
Qed.

Lemma p41eq234 w v : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in
  g^-1 *m \T(v, w) *m g = \T(h *: w, w).
Proof.
move=> w1 g h.
rewrite inv_rigid_transE /inv_rigid_trans /rigid_trans /Twistmx.
rewrite (mulmx_block 1 0 (- w *v v) 1 \S( w )) !(mulmx0,addr0,mul0mx,mul1mx).
rewrite skew_mxE 2!crossmulNv (crossmulC _ w) opprK.
rewrite double_crossmul dotmulvv w1 expr1n scale1r subrK.
by rewrite (mulmx_block \S( w ) 0 _ 0 1 0) !(mulmx0,addr0,mul0mx,mul1mx,mulmx1).
Qed.

Lemma p42eq235 w v a k :
  let g := rigid_trans w v in
  let e' := g^-1 *m \T(v, w) *m g in
  expmx (a *: (\T(v, w) : 'M__) ) k = g * expmx (a *: e') k * g^-1.
Proof.
move=> g e'.
rewrite -expmx_mulmulV ?rigid_trans_unitmx //; congr (expmx _ _).
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
elim: k => [|k ih].
  rewrite (@expr2 _ (block_mx \S( w ) _ _ _)) -mulmxE (mulmx_block \S( w ) _ _ _ \S( w )).
  by rewrite !(mulmx0,addr0,mul0mx) mulmxE -expr2 skew_mxE crossmulZv crossmulvv scaler0.
rewrite exprS ih -mulmxE (mulmx_block \S( w ) _ _ _ (\S( w ) ^+ k.+2)).
rewrite !(mulmx0,addr0,mul0mx) mulmxE -exprS; congr (block_mx (\S( w ) ^+ k.+3) 0 _ 0).
by rewrite exprS mulmxA skew_mxE crossmulZv crossmulvv scaler0 mul0mx.
Qed.

Lemma expmx2_twist w v a : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in
  expmx (a *: (\T(v, w) : 'M__) ) 2 = g *m hom (expmx (a *: \S( w)) 2) (h *: (a *: w)) *m g^-1.
Proof.
move=> w1 g h.
rewrite {1}/expmx 2!big_ord_recl big_ord0 addr0 liftE0 eqxx /expt factS fact0 invr1 2!scale1r.
rewrite expr0 expr1 /Twistmx.
rewrite (_ : 1 = @block_mx _ 3 _ 3 _ 1 0 0 1); last first.
  by rewrite -idmxE (@scalar_mx_block _ 3 1 1).
rewrite twistZ /= (add_block_mx 1 0 0 1 \S( a *: w )) !(addr0,add0r).
rewrite {1}/g /rigid_trans mulmxE homM mul1r.
rewrite inv_rigid_transE /inv_rigid_trans homM mulr1 mulmx1 expmx2.
rewrite -skew_mxZ.
congr (block_mx (1 + \S( a *: w )) 0 _ 1).
rewrite mulmxDr mulmx1 crossmulNv -addrA addrC addrA subrK skew_mxE.
rewrite scalerA (mulrC h) -scalerA crossmulvZ -scalerDr; congr (_ *: _).
by rewrite crossmulC double_crossmul dotmulvv w1 expr1n scale1r -/h opprB addrCA subrr addr0.
Qed.

Lemma p42eq3 w v a : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in 
  let e' := g^-1 *m \T(v, w) *m g in
  forall k, expmx (a *: e') k.+2 = hom (expmx (a *: \S( w )) k.+2) (h *: (a *: w)).
Proof.
move=> w1 g h e'; rewrite /e'.
elim => [|k ih].
  rewrite -{2}(invrK g) scalemxAl scalemxAr.
  rewrite expmx_mulmulV ?unitrV ?rigid_trans_unit //.
  rewrite expmx2_twist // !mulmxE !mulrA mulVr ?rigid_trans_unit // mul1r.
  by rewrite -!mulrA divrr ?unitrV ?rigid_trans_unit // mulr1.
rewrite expmxS ih /expt exprZn p42eq2 //.
rewrite (scale_block_mx (a ^+ k.+2) (\S(w) ^+ k.+2)) !scaler0.
rewrite -exprZn -skew_mxZ.
rewrite (scale_block_mx ((k.+2)`!%:R^-1) (\S( (a *: w) ) ^+ k.+2)) !scaler0.
by rewrite (add_block_mx (expmx \S( a *: w ) k.+2)) !(addr0) -expmxS.
Qed.

Definition hom_twist t a e : 'M[R]_4 :=
  let: \T(v, w) := t in
  if w == 0 then
    hom 1 (a *: v)
  else
    hom e ((norm w)^-2 *: ((v *v w) *m (1 - e) + (a *: v) *m (w^T *m w))).

(* [murray] eqn 2.36, p.42 *)
Definition expmx_twist a t k : 'M_4 :=
  let: \T(_, w) := t in
  hom_twist t a (expmx \S( a *: w ) k).

(* [murray] eqn 2.36, p.42 *)
Lemma expmx_twistE v w a k :
  expmx (a *: (\T(v, w) : 'M_4)) k.+2 =
  expmx_twist a \T(v, w) k.+2.
Proof.
case/boolP : (w == 0) => [/eqP ->|w0].
  by rewrite twistZ /= scaler0 expmx_twist0E eqxx.
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
rewrite [in RHS]scalerA divrr ?scale1r; last by rewrite unitfE norm_eq0.

rewrite /expmx_twist /hom_twist.
rewrite (negbTE w0).
rewrite skew_mxZ; congr hom.

rewrite crossmulZv crossmulvZ scalerA.
rewrite dotmulZv dotmulvZ !mulrA -[in X in _ + X + _]scalerA.
rewrite crossmulvZ crossmulNv [in X in _ + _ + X = _]scalerN crossmulZv [in X in _ + _ + X]scalerA.
rewrite -scalemxAl -scalerDr -scalerBr; congr (_ *: _).
  by rewrite -invrM ?unitfE ?norm_eq0.
rewrite -/w' /= [in X in _ = X + _]mulmxBr mulmx1.
rewrite -[in RHS]addrA [in RHS]addrC; congr (_ + _ + _).
- by rewrite crossmulC mulNmx.
- rewrite -scalemxAl mulmxA.
  rewrite (mx11_scalar (v *m _ ^T)) -/(v *d w) mul_scalar_mx dotmulC.
  by rewrite scalerA mulrC -scalerA -/w'.
- by rewrite crossmulC opprK.
Qed.

(* [murray] proposition 2.8, p. 41 *)
Lemma expmx_twist_SE3 v w a k :
  expmx \S(a *: w) k.+2 \is 'SO[R]_3 ->
  expmx (a *: (\T(v, w) : 'M__)) k.+2 \is 'SE3[R].
Proof.
move=> expmx_SO; rewrite expmx_twistE.
rewrite /expmx_twist /hom_twist.
case: ifPn => [_|w0]; by rewrite hom_is_SE // rpred1.
Qed.

End exponential_coordinates_rigid_using_taylor.

Module AngleR.
Section angler.
Variable R : rcfType.

(* fonction de conversion proportionnelle positive non-nulle *)
Variable conv : angle R -> R.
Hypothesis conv_pos : forall a, 0 <= conv a.
Hypothesis conv0 : conv 0 = 0.
Hypotheses convpi : 0 < conv pi.
Hypothesis conv_propor : forall k a, conv (a *+ k) = conv a *+ k.

(* modulo *)
Variable representative : R -> R.
Hypothesis representative_codomain :  forall r, 0 <= representative r < (conv pi) *+ 2.
Definition representativeP r := 
  [pred k | ((0 <= r) ==> (r == representative r + (conv pi) *+ 2 *+ k)) && 
            ((r < 0) ==> (r == representative r + (conv pi) *+ 2 *- k))].
Axiom exists_representativeP : forall r, { k | representativeP r k }.

Definition f : angle R -> R := representative \o conv.

Lemma f2pi : f (pi *+ 2) = 0%:R.
Proof.
rewrite /f /= conv_propor.
case: (exists_representativeP (conv pi *+ 2)) => k /=.
rewrite ltrNge mulrn_wge0 // implyTb implyFb andbT.
case: k.
  rewrite mulr0n addr0 => abs.
  move: (representative_codomain ((conv pi) *+ 2)).
  by rewrite -(eqP abs) ltrr andbF.
case=> [|k]; last first.
  rewrite (mulrS _ k.+1) addrCA addrC -subr_eq subrr eq_sym addr_eq0 => abs.
  move: (representative_codomain ((conv pi) *+ 2)).
  rewrite lerNgt (eqP abs) -lerNgt mulrS => /andP[].
  by rewrite oppr_ge0 lerNgt addrC ltr_paddl // ?pmulrn_rgt0 // mulrn_wge0 // mulrn_wge0 // ltrW.
by rewrite mulr1n -subr_eq subrr => /eqP.
Qed.
End angler.
End AngleR.

Section exponential_coordinates_rigid.

Variable R : rcfType.

Axiom radian : angle R -> R.
Axiom angle_of_radian : R -> angle R.
Axiom angle_of_radianK : cancel angle_of_radian radian.
Axiom radianK : cancel radian angle_of_radian.
Axiom radian0 : forall a, (radian a == 0) = (a == 0).

(* NB: same definition as exp_twist but using exp_mat instead of the taylor expansion of
   the exponential *)
(* [springer] eqn 1.27, p. 17, closed expression for the exponential of a twist *)
Definition exp_twist a (t : Twist.t R) :=
  let w := ang_of_twist t in
  hom_twist t (radian a) (`e^(a, \S( w ))).

Lemma exp_twist_is_SE (t : Twist.t R) a :
  norm (ang_of_twist t) = 1 -> exp_twist a t \in 'SE3[R].
Proof. 
move=> w1.
rewrite /exp_twist /hom_twist.
case: t w1 => w v.
rewrite ang_of_twistE => w1.
rewrite (negbTE (norm1_neq0 w1)).
apply hom_is_SE.
by rewrite exp_skew_is_SO.
Qed.

Lemma exp_twist_is_onto_SE (f : 'M[R]_4) : f \is 'SE3[R] ->
  exists (t : Twist.t R) (a : R), f = exp_twist (angle_of_radian a) t.
Proof.
case/boolP: (rot_of_hom f == 1) => rotf fSE.
  set p := trans_of_hom f.
  exists \T(normalize p, 0), (norm p).
  rewrite /exp_twist /hom_twist ang_of_twistE eqxx /=.
  rewrite angle_of_radianK norm_scale_normalize.
  by rewrite (SE3E fSE) (eqP rotf).
case: (exp_skew_is_onto_SO (rot_of_hom_SO fSE)) => a [w [w1 fexp_skew]].
have a0 : a != 0.
  apply: contra rotf => /eqP.
  rewrite fexp_skew => ->; by rewrite exp_mat0v.
set A := \S(w) *m (1 - rot_of_hom f) + radian a *: (w^T *m w).
suff [v Hv] : exists v, trans_of_hom f = (norm w)^-2 *: (v *m A).
  exists (\T(v, w)), (radian a).
  rewrite (SE3E fSE) /exp_twist /hom_twist.
  rewrite ang_of_twistE.
  have /negbTE -> : w != 0.
    apply: contra rotf; rewrite fexp_skew => /eqP ->.
    by rewrite skew_mx0 exp_mata0.
  rewrite radianK fexp_skew Hv; congr hom.
  congr (_ *: _).
  rewrite /A mulmxDr mulmxA skew_mxE -scalemxAr -scalemxAl.
  by rewrite fexp_skew.
have HA : A = (radian a * norm w ^+ 2)%:A + ((1 - cos a) * norm w ^+2) *: \S(w) + (radian a - sin a) *: \S(w)^+2.
  rewrite /A.
  rewrite fexp_skew /exp_mat.
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
suff : exists A' : 'M_3 , A' * A = 1.
  case => A' AA'.
  exists ((norm w) ^+2 *: (trans_of_hom f) *m A').
  rewrite -mulmxA mulmxE AA' mulmx1 scalerA.
  rewrite mulrC divrr ?scale1r // unitfE expf_eq0 /= norm_eq0.
  apply: contra rotf; rewrite fexp_skew => /eqP ->.
  by rewrite skew_mx0 exp_mata0.
(* NB: corresponds to [murray], exercise 9, p.75 *)
(* NB: formula for the inverse matrix in
   [Introduction to Robotics: Mechanics, Planning, and Control,
    F.C. Park, K. Lynch, Mar. 14 2012]
 *)
set AT := (radian a)^-1%:M - 2%:R^-1 *: \S(w) +
          ((radian a)^-1 - 2%:R^-1 * cot (half_angle a)) *: \S(w) ^+ 2.
exists AT.
rewrite /AT HA.
set ra := radian a.
rewrite w1 expr1n !mulr1.
rewrite !mulrDl.
rewrite 6!mulrDr.
rewrite {1}scalemx1 -{1}mulmxE -scalar_mxM mulVr; last by rewrite unitfE radian0.
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
rewrite mulrBr divrr; last by rewrite unitfE radian0.
rewrite scalerBl scale1r.

rewrite (scalerN (2%:R^-1 * _)) opprK.
rewrite (scalerA (2%:R^-1 * _)).
rewrite mulrBr scalerBl !addrA.
rewrite mulrCA (mulrC ra) mulrA.
rewrite subrK.

rewrite {1}cot_half_angle' -!mulrA mulVr ?mulr1; last first.
  rewrite unitfE.
  admit.
rewrite cot_half_angle.
rewrite (scalerN (2%:R^-1 * _)) opprK.
rewrite (scalerA (2%:R^-1 * _)).
rewrite -!mulrA mulVr ?mulr1; last first.
  rewrite unitfE subr_eq0.
  admit.
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
Abort.

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

(* screws: a geometric description of twists *)

Module Screw.
Section Screw.
Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Record t := mk {
  p : point ; (* axis point *)
  w : vector ; (* axis vector *)
  a : angle R ; (* magnitude *)
  h : R (* pitch *) }.
End Screw.
End Screw.

Section screw_motion.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* rotation by an amount a about the axis w follows by a translation ha parallel to w *)
Definition screw q w a h (p : point) :=
  q + (p - q) *m `e^(a, \S( w )) + (h * radian a) *: w.

(* the rbt given by a screw *)
Definition hom_screw q w a h : 'M[R]__ :=
  hom (`e^(a, \S(w))) (q *m (1 - `e^(a, \S( w ))) + (h * radian a) *: w).

Lemma hom_screwa0 q w h : hom_screw q w 0 h = hom 1 0.
Proof.
rewrite /hom_screw exp_mat0v subrr mulmx0 add0r.
rewrite (_ : radian 0 = 0) ?mulr0 ?scale0r //; by apply/eqP; rewrite radian0.
Qed.

Lemma hom_screww0 q a h : hom_screw q 0 a h = hom 1 0.
Proof. by rewrite /hom_screw skew_mx0 exp_mata0 scaler0 addr0 subrr mulmx0. Qed.

Lemma hom_screwE q w a h (p : point) (w1 : norm w = 1) :
  SE.ap_point (SE.mk (q *m (1 - `e^(a, \S( w ))) + (h * radian a) *: w)
                     (exp_skew_is_SO a w1)) p = screw q w a h p.
Proof.
rewrite SE.ap_pointE mul_mx_row add_row_mx mulmx0 add0r to_hpointK.
rewrite addrA /hom_screw /=; apply/rowP => i.
rewrite mxE [in RHS]mxE; congr (_ + _).
rewrite mulmxBr mulmx1 addrCA mxE [in RHS]mxE; congr (_ + _).
by rewrite mulmxBl.
Qed.

Definition rodrigues_gen (v : 'rV[R]_3) a w :=
  v - (1 - cos a) *: (norm w ^+ 2 *: v) + (1 - cos a) * (v *d w) *: w + sin a *: (v *v w).

Lemma rodrigues_genP u a w : rodrigues_gen u a w = u *m `e^(a, \S( w )).
Proof.
rewrite /rodrigues_gen.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE.
rewrite [in X in _ = _ + _ + X]crossmulC scalerN.
rewrite double_crossmul dotmulvv.
rewrite [in X in _ = _ + _ + X]dotmulC scalerBr opprB.
rewrite [in RHS]scalerA [in RHS](addrC (_ *: w)) [in RHS]addrA; congr (_ + _).
rewrite addrAC; congr (_ + _).
Qed.

(* [murray] p. 47
  in fact, if we choose v = - w x q + h w, then \xi = (v, w) generates the screw motion
  in equation 2.40
*)
Lemma hom_screw_exp_twist s :
  let: Screw.mk q w a h := s in
  let v := w *v q + h *: w in
  hom_screw q w a h = exp_twist a \T(v, w) :> 'M_4.
Proof.
case: s => p w a h v.
(*case/boolP : (radian a == 0) => [|a0].
  rewrite radian0 => /eqP ->.
  rewrite /exp_twist /hom_screw /hom_twist.
  rewrite (_ : radian 0 = 0); last by apply/eqP; rewrite radian0.
  rewrite !exp_mat0v subrr mulr0 scale0r mulmx0 addr0 scale0r mulmx0 mul0mx.
  rewrite addr0 scaler0; by case: ifPn.*)
rewrite /exp_twist /hom_twist. (*/hom_screw unskewK block_mxKul /= ?anti_skew //.*)
case: ifPn => [/eqP|] w0.
  by rewrite w0 hom_screww0 /v w0 crossmul0v add0r 2!scaler0.
rewrite /hom_screw.
rewrite ang_of_twistE.
congr hom.
rewrite {1}/v.
rewrite crossmulC.
rewrite [w *v _]linearD /=.
rewrite crossmulvZ crossmulvv scaler0 addr0.
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
rewrite (mulmxA w) (mx11_scalar (w *m w^T)) -/(w *d w) dotmulvv mul_scalar_mx scalerA.
rewrite [in X in _ = _ *: (_ + X)]scalerDr addrA addrC.
rewrite scalerDr.
rewrite 2!scalerA.
rewrite [in X in _ = X + _]mulrA.
rewrite [in X in _ = X + _]mulrC.
rewrite 2!mulrA divrr ?mul1r; last by rewrite unitfE expf_eq0 /= norm_eq0.
rewrite mulrC -[LHS]addr0.
congr (_ + _).
rewrite mulmxBr mulmx1.
rewrite -rodrigues_genP /rodrigues_gen.
rewrite crossmulZv crossmulvv 2!scaler0 addr0.
rewrite dotmulZv dotmulvv.
rewrite !scalerA mulrAC mulrA.
rewrite subrK.
rewrite subrr oppr0 add0r.
rewrite crossmulC mulNmx scalerN.
by rewrite -skew_mxE -mulmxA (mulmxA \S( w )) skew_mxT mul0mx mulmx0 scaler0 oppr0 scaler0.
Qed.

End screw_motion.

Section screw_coordinates_of_a_twist.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Variable t : 'M[R]_4. (* NB: supposed to be a twist *)
Let w := ang_of_twist t.
Let v := lin_of_twist t.

Definition axis_point : point := (* [murray] 2.43, p.47 *)
  if w == 0 then 0 else (norm w)^-2 *: (w *v v).

Definition axis : vector := if w == 0 then v else w. (* [murray] 2.43, p.47 *)

Definition pitch : R := (norm w)^-2 *: v *d w. (* [murray] 2.42, p.47 *)

Definition magnitude : R := if w == 0 then norm v else norm w. (* [murray] 2.44, p.48 *)

Definition ScrewTwist := Screw.mk
  axis_point axis (angle_of_radian pitch) magnitude.

End screw_coordinates_of_a_twist.

Lemma magnitudeZ (R : rcfType) (M : 'M[R]_4 (* NB: supposed to be a twist *)) a : 0 < a ->
  magnitude (a *: M) = a * magnitude M.
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

Section screw_motion_utwist.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* unit twist: [murray] p.49 (p.48 also) *)
Definition utwist (t : 'M[R]_4) := (magnitude t == 1).
(* (norm (ang_of_twist t) == 1) ||
  ((norm (ang_of_twist t) == 0) && (norm (lin_of_twist t) == 1)) *)

(* a unit twist has magnitude M = 1 [murray p.49] *)
(*Lemma magn_of_utwist t : utwist t -> magnitude t = 1.
Proof.
rewrite /magnitude; case/orP => [/eqP w1|/andP[w0 /eqP v1]].
  by rewrite (negbTE (norm1_neq0 w1)) w1.
by rewrite -norm_eq0 w0.
Qed.*)

(* [murray] p. 48
   if we choose [a unit twist t], then a twist ta has magnitude a *)
Lemma magn_of_utwistZ a (t : Twist.t R) : 0 < a -> utwist t ->
  magnitude (a *: (t : 'M_4) ) = a.
Proof. move=> a0 Ht; by rewrite magnitudeZ // (eqP Ht) mulr1. Qed.

(* [murray] proposition 2.10, p.48 *)
(* TODO: not yet right *)
Lemma hom_screw_exp_utwist (t : Twist.t R) (t0 : (t : 'M_4) != 0) :
  let q := axis_point t in
  let w := axis t in
  let a := magnitude t in
  let h := pitch t in
  exists t' : Twist.t R, (* TODO: utwist t' /\*)
  (if ang_of_twist t == 0 then
    hom 1 (a *: w)
  else
    hom_screw q w (angle_of_radian a) h) = exp_twist (angle_of_radian a) t'.
Proof.
move=> q w a h.
case/boolP : (ang_of_twist t == 0) => [/eqP|] w0.
  exists \T(w, 0).
  rewrite /exp_twist ang_of_twistE skew_mx0 exp_mata0 angle_of_radianK.
  by rewrite /hom_twist eqxx.
set v := w *v q + h *: w.
exists \T(v, w).
by rewrite (hom_screw_exp_twist (Screw.mk q w (angle_of_radian a) h)).
Qed.

End screw_motion_utwist.

Section chasles.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Variable f : 'DIso_3[R].
Let Q : 'M[R]_3 := ortho_of_iso f.
Let T : vector := trans_of_iso f.
Variable e : vector.
Hypothesis ne : norm e = 1.
Variable phi : angle R.
Hypothesis Maxis : is_around_axis e phi (mx_lin1 Q).

(* [angeles] theorem 3.2.1, p.97: 
   the displacements of all the points of the body have the same projection onto e *)

Lemma thm321 (a p : point) : displacement f a *d e = displacement f p *d e.
Proof.
rewrite /dotmul; congr (fun_of_matrix _ 0 0).
rewrite (displacement_iso f p a) [in RHS]mulmxDl -[LHS](addr0); congr (_ + _).
rewrite -mulmxA (mulmxBl Q) mul1mx.
suff -> : Q *m e^T = e^T by rewrite subrr mulmx0.
rewrite -{1}(is_around_axis_axis Maxis) trmx_mul mulmxA mulmxE.
move: (ortho_of_iso_is_O f); rewrite -/Q orthogonalE => /eqP ->; by rewrite mul1mx.
Qed.

Definition d0 := displacement f 0 *d e.

Lemma d0_is_a_lb_of_a_displacement p : d0 ^+ 2 <= norm (displacement f p) ^+ 2.
Proof.
rewrite /d0 (thm321 0 p).
move: (Frame.pframe (norm1_neq0 ne)) => F.
have -> : norm (displacement f p) =
          norm (displacement f p *m (col_mx3 (normalize e) (Frame.j e) (Frame.k e))^T).
  rewrite orth_preserves_norm // orthogonalV rotation_sub //; exact: (pframe_is_rot F).
rewrite col_mx3_mul sqr_norm !mxE /= -[X in X <= _]addr0 -addrA ler_add //.
  rewrite normalizeI //; by case: e.
by rewrite addr_ge0 // sqr_ge0.
Qed.

Definition parpart (p : point) := axialcomp (displacement f p) e.

Lemma parpartP p : parpart p = d0 *: (e : 'rV[R]_3).
Proof. by rewrite /parpart /axialcomp dotmulC (thm321 _ 0). Qed.

Definition perppart (p : point) := normalcomp (displacement f p) e.

(* [angeles] theorem 3.2.2, p.97 *)
(* d0 is the minimal norm of a displacement, all such points are along a line parallel
   to e *)
Lemma MozziChasles p :
  norm (displacement f p) = d0 -> colinear (displacement f p) e.
Proof.
move=> H.
have Hp : forall p : point,
    norm (displacement f p) ^+ 2 = norm (d0 *: (e : 'rV[R]_3)) ^+2 + norm (perppart p) ^+ 2.
  move=> p'.
  rewrite (decomp (displacement f p') e) normD -dotmul_cos.
  rewrite axialnormal // ?neq // mul0rn addr0 sqr_sqrtr; last first.
    by rewrite addr_ge0 // ?sqr_ge0.
  by rewrite /perppart -/(parpart p') parpartP.
move: {Hp}(Hp p) => Hp.
rewrite -normalcomp_colinear ?ne // -norm_eq0.
suff : norm (displacement f p) ^+2 <= norm (d0 *: (e : 'rV[R]_3)) ^+ 2.
  by rewrite Hp addrC -ler_subr_addr subrr exprn_even_le0 //= norm_eq0.
rewrite 2!expr2.
by rewrite ler_pmul // ?norm_ge0 // H normZ ne mulr1 ler_norm.
Qed.

Definition pitch_new := d0 / radian phi.

Definition screw_axis_point (a : point) :=
  let a':= f a in
  1 / ((1 - cos phi) *+ 2) *: (a *m Q - a') *m (Q - 1)^T.

(* [angeles] Sect. 3.2.1 (the screw of a rigid-body motion) *)
Lemma screw_axis_pointE p0 (* a point on the screw axis *) a :
  phi != 0 ->
  p0 *d e = 0 (* p0 is the closed point to the origin *) ->
  normalcomp (displacement f p0) e = 0 ->
  p0 = screw_axis_point a.
Proof.
move=> phi0 p0e0 fp0e0.
have step1 : displacement f p0 *m (Q - 1) = 0.
  have : colinear (displacement f p0) e.
    rewrite (decomp (displacement f p0) e).
    rewrite -/(parpart p0).
    rewrite parpartP.
    by rewrite fp0e0 addr0 colinearZv colinear_refl orbC.
  rewrite -normalcomp_colinear // => /eqP H1.
  rewrite (decomp (displacement f p0) e) H1 addr0.
  rewrite /axialcomp -scalemxAl mulmxBr mulmx1.
  by case: Maxis => /= -> _ _; rewrite subrr scaler0.
move: (displacement_iso f p0 a) => step2.
have {step2}step3 : displacement f a + relative_displacement f p0 a = displacement f a *m (e^T *m e).
  transitivity (displacement f p0 *m e^T *m e).
    rewrite -step2.
    rewrite {1}(decomp (displacement f p0) e) fp0e0 addr0.
    by rewrite axialcompE.
  rewrite (mx11_scalar (displacement f p0 *m e^T)) -/(dotmul _ _) (thm321 p0 a).
  by rewrite mulmxA (mx11_scalar (displacement f a *m e^T)) -/(dotmul _ _).
have step4 : p0 *m (Q - 1) = a *m (Q - 1) - displacement f a *m (1 - e^T *m e).
  rewrite [in X in _ = _ - X]mulmxBr mulmx1 -{}step3.
  rewrite (opprD (displacement f a)) opprK addrCA addrA subrr add0r.
  by rewrite /relative_displacement -/Q mulmxBl addrCA subrr addr0.
set A := row_mx (Q - 1) e^T.
set b : 'rV[R]_4 := row_mx (a *m (Q - 1) - displacement f a *m (1 - e^T *m e)) 0.
have step5 : p0 *m A = b.
  rewrite /A mul_mx_row /b {}step4; congr row_mx.
  rewrite (mx11_scalar (_ *m _)) -/(dotmul p0 e) p0e0.
  by apply/rowP => i; rewrite (ord1 i) !mxE eqxx mulr1n.
move/(congr1 (fun x => x *m A^T)) in step5.
move: (is_around_axis_exp_skew'_new ne Maxis) => step6.
set x := (1 - cos phi) *+ 2.
have Hx : x \is a GRing.unit.
  rewrite unitfE /x mulrn_eq0 negb_or /= subr_eq0 eq_sym.
  by apply/eqP => /cos1_angle0; apply/eqP.
have Hx1 : (x^-1)%:M *m x%:M = 1 :> 'M_3.
  by rewrite -scalar_mxM mulVr // mul_mx_scalar.
set y := (1 - cos phi *+ 2).
have step7 : A *m A^T = x *: 1 - y *: e^T *m e.
  rewrite /A tr_row_mx mul_row_col trmxK linearD /= linearN /= trmx1.
  rewrite mulmxBr mulmx1 opprB mulmxBl mul1mx.
  move: (ortho_of_iso_is_O f); rewrite -/Q orthogonalE mulmxE => /eqP ->.
  rewrite addrA (addrC (1 - _)) addrA.
  rewrite (_ : 1 + 1 = 2%:R) //.
  rewrite /x mulrnBl scalerBl -2!addrA -[in RHS]addrA; congr (_ + _).
    rewrite scalemx1.
    by apply/matrix3P; rewrite !mxE ?eqxx /= ?mulr1n // ?mulr0n // addr0.
  rewrite addrA.
  rewrite {1}step6 /exp_skew' cosN sinN scaleNr.
  rewrite -(addrA (e^T *m e)).
  rewrite linearD /= trmx_mul trmxK opprD addrC 2!addrA subrr add0r.
  rewrite linearD /= linearZ /= linearN /= opprB linearZ /= linearD /= trmx1.
  rewrite step6 opprD sinN scaleNr opprK !addrA addrC !addrA tr_skew.
  rewrite (scalerN (sin phi) \S( e )) subrr add0r cosN.
  rewrite linearN /= trmx_mul trmxK opprD addrA addrAC -scaleNr -scalerDl.
  rewrite -mulr2n scalerBr scalemx1 scalemx1 -addrA; congr (_ + _).
    apply/matrix3P; by rewrite !mxE ?eqxx ?mulr1n ?mulr0n // ?oppr0 // mulNrn.
  rewrite -scalemxAl /y [in RHS]scalerBl scale1r opprB; congr (_ + _).
  by rewrite mulNrn scaleNr opprK.
set AATinv : 'M_3 := x^-1 *: 1 + y / x *: e^T *m e.
have Htmp : y - x^-1 * y - y / x * y = 0.
  rewrite (mulrC y) -mulrA -{1}(mulKr Hx y) -2!mulrBr; apply/eqP.
  rewrite mulf_eq0 invr_eq0.
  move: Hx; rewrite unitfE => /negPf -> /=.
  rewrite -{2}(mul1r y) -2!mulrBl mulf_eq0.
  rewrite -addrA -opprB opprK subr_eq0.
  by rewrite /x {1}/y mulrnBl addrAC eqxx.
have AATinv_1 : AATinv * (A *m A^T) = 1.
  rewrite /AATinv step7 -/x -/y !scalemx1 -!mulmxE.
  rewrite mulmxBr mulmxDl Hx1 -[RHS]addr0 -addrA; congr (_ + _).
  rewrite mul_mx_scalar -{1}scalemxAl {1}(mulrC y) scalerA mulrA mulrV // mul1r.
  rewrite mulmxDl.
  rewrite opprD addrA mul_scalar_mx -[in X in X - _ = 0]scalemxAl scalerA.
  rewrite -scalerBl.
  rewrite -3![in X in _ - X = 0]scalemxAl.
  rewrite -[in X in _ - X = 0]scalemxAr.
  rewrite [in X in _ - X = 0]scalerA.
  rewrite mulmxE -expr2 mulmx_tr_uvect // -scalerBl.
  by apply/eqP; rewrite scaler_eq0 Htmp eqxx.
have AATinv_2 : (A *m A^T) * AATinv = 1.
  rewrite /AATinv step7 -/x -/y !scalemx1 -!mulmxE.
  rewrite mulmxBl mulmxDr {1}mulmxE (scalar_mx_comm (x^-1)) -{1}mulmxE Hx1.
  rewrite -[RHS]addr0 -addrA; congr (_ + _).
  rewrite mul_scalar_mx -{1}scalemxAl scalerA mulrC -mulrA mulVr // mulr1.
  rewrite mulmxDr.
  rewrite opprD addrA mul_mx_scalar -[in X in X - _ = 0]scalemxAl scalerA.
  rewrite -scalerBl.
  rewrite -3![in X in _ - X = 0]scalemxAl.
  rewrite -[in X in _ - X = 0]scalemxAr.
  rewrite [in X in _ - X = 0]scalerA.
  rewrite mulmxE -expr2 mulmx_tr_uvect // -scalerBl.
  by apply/eqP; rewrite scaler_eq0 (mulrC y) Htmp eqxx.
have H3 : A *m A^T \is a GRing.unit.
  by apply/unitrP; exists AATinv; rewrite AATinv_1 AATinv_2.
have step8 : (A *m A^T)^-1 = AATinv by rewrite -[LHS]mul1r -AATinv_1 mulrK // unitmxE.
have Htmp2 : (Q - 1)^T *m (e^T *m e) = 0.
  rewrite (is_around_axis_exp_skew'_new ne Maxis).
  rewrite linearD /=.
  rewrite mulmxDl.
  rewrite [in X in _ + X = _]linearN /= trmx1 mulNmx mul1mx.
  rewrite linearD /=.
  rewrite cosN sinN scaleNr.
  rewrite linearN /=.
  rewrite linearZ /=.
  rewrite tr_skew.
  rewrite scalerN.
  rewrite opprK.
  rewrite mulmxDl.
  rewrite -scalemxAl !mulmxA skew_mxT mul0mx scaler0 addr0.
  rewrite linearD /= trmx_mul trmxK.
  rewrite -mulmxA mulmxDl mulmxE -expr2 mulmx_tr_uvect //.
  rewrite addrC addrA (addrC (- _)) subrr add0r.
  rewrite linearZ /= -mulmxE -scalemxAl.
  rewrite linearD /= trmx1 linearN /= trmx_mul trmxK mulmxBl.
  rewrite mul1mx mulmxE -expr2 mulmx_tr_uvect //.
  by rewrite subrr scaler0.
have step9 : b *m A^T = (a *m (Q - 1) - displacement f a) *m (Q - 1)^T.
  rewrite /A tr_row_mx trmxK.
  rewrite /b (mul_row_col (a *m (Q - 1) - _)) mul0mx addr0.
  rewrite (mulmxBr (displacement f a)) mulmx1 opprB addrA addrAC.
  rewrite mulmxDl -mulmxA.
  have Htmp3 : (e^T *m e) *m (Q - 1)^T = 0.
    rewrite (is_around_axis_exp_skew'_new ne Maxis).
    rewrite linearD /=.
    rewrite [in X in _ *m (_ + X)]linearN /= trmx1.
    rewrite mulmxBr mulmx1 /exp_skew' cosN sinN scaleNr.
    rewrite -addrA.
    rewrite linearD /=.
    rewrite mulmxDr.
    rewrite trmx_mul trmxK.
    rewrite mulmxE -expr2 mulmx_tr_uvect //.
    rewrite addrC addrA (addrC (- _)) subrr add0r.
    rewrite linearD /=.
    rewrite linearN /= 2!linearZ /= tr_skew scalerN opprK.
    rewrite mulrDr.
    rewrite -scalerAr.
    rewrite linearD /= trmx1 linearN /= trmx_mul trmxK mulrBr.
    rewrite mulr1 -expr2 mulmx_tr_uvect // subrr scaler0 add0r.
    by rewrite -scalerAr -mulmxE -mulmxA skew_mxE crossmulvv mulmx0 scaler0.
  by rewrite Htmp3 mulmx0 addr0.
rewrite /screw_axis_point -/x.
move/(congr1 (fun x => x *m AATinv)) : step5.
rewrite -2!mulmxA -step8 mulmxV // mulmx1.
rewrite step9 step8.
rewrite mulmxBr mulmx1 /displacement opprB addrA subrK.
rewrite /AATinv.
rewrite mulmxDr.
rewrite -[in X in _ = _ + X -> _]mulmxA.
rewrite -[in X in _ = _ + X -> _]scalemxAl.
rewrite -[in X in _ = _ + X -> _]scalemxAr.
rewrite Htmp2.
rewrite scaler0 mulmx0 addr0.
by rewrite scalemx1 mul_mx_scalar div1r scalemxAl.
Qed.

End chasles.
