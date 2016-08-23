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

Local Notation "'\w(' t ')'" := (ang_of_twist t) (format "'\w('  t  ')'", at level 3).

Lemma ang_of_twist0 : \w( 0 ) = 0.
Proof. by rewrite /ang_of_twist -(@block_mx0 _ 3 1 3 1) block_mxKul unskew0. Qed.

Lemma ang_of_twistE (v w : 'rV[R]_3) : \w( \T(v, w) ) = w.
Proof. by rewrite /ang_of_twist block_mxKul /= skew_mxK. Qed.

Definition lin_of_twist (M : 'M[R]_4) := @dlsubmx _ 3 1 3 1 M.

Local Notation "'\v(' t ')'" := (lin_of_twist t) (format "'\v('  t  ')'", at level 3).

Lemma lin_of_twist0 : \v( 0 ) = 0.
Proof. by rewrite /lin_of_twist -(@block_mx0 _ 3 1 3 1) block_mxKdl. Qed.

Lemma lin_of_twistE (v w : 'rV[R]_3) : \v( \T(v, w) ) = v.
Proof. by rewrite /lin_of_twist block_mxKdl /=. Qed.

Definition se3 := [qualify M : 'M[R]_4 |
  [&& @ulsubmx _ 3 1 3 1 M \is 'so[R]_3,
      @ursubmx _ 3 1 3 1 M == 0 &
      @drsubmx _ 3 1 3 1 M == 0] ].
Fact se3_key : pred_key se3. Proof. by []. Qed.
Canonical se3_keyed := KeyedQualifier se3_key.

Lemma se3E (M : 'M[R]_4) :
  (M \is se3) = (M == \T( \v( M ), \w( M ))).
Proof.
apply/idP/idP => [|/eqP ->].
  rewrite qualifE => /and3P[].
  rewrite qualifE => /eqP H1 /eqP H2 /eqP H3.
  rewrite -{1}(@submxK _ 3 1 3 1 M) H2 H3 /Twistmx /=.
  rewrite unskewK // qualifE; by apply/eqP.
rewrite qualifE /Twistmx block_mxKul /= block_mxKur /= eqxx /=.
by rewrite block_mxKdr eqxx andbT anti_skew.
Qed.

Lemma ang_of_twistZ k (M : 'M[R]_4) : \w( (k *: M) ) = k *: \w( M ).
Proof.
rewrite /ang_of_twist -{1}(@submxK _ 3 1 3 1 M).
by rewrite (scale_block_mx k (@ulsubmx _ 3 1 3 1 M)) block_mxKul unskew_mxZ.
Qed.

Lemma lin_of_twistZ k (M : 'M[R]_4) : \v( (k *: M) ) = k *: \v( M ).
Proof.
rewrite /lin_of_twist -{1}(@submxK _ 3 1 3 1 M).
by rewrite (scale_block_mx k (@ulsubmx _ 3 1 3 1 M)) block_mxKdl.
Qed.

End twists.

Notation "''se3[' R ]" := (se3 R)
  (at level 8, format "''se3[' R ]") : ring_scope.
Notation "'\w(' t ')'" := (ang_of_twist t) (format "'\w('  t  ')'", at level 3).
Notation "'\v(' t ')'" := (lin_of_twist t) (format "'\v('  t  ')'", at level 3).

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
Lemma emx_twist0E v k : emx \T(v, 0) k.+2 = hom 1 v.
Proof.
rewrite /emx 2!big_ord_recl big1 ?addr0; last first.
  move=> /= i _; by rewrite ecoefE exp_twist0v scaler0.
rewrite liftE0 eqxx /ecoef factS fact0 expr0 expr1 invr1 2!scale1r /Twistmx skew_mx0.
by rewrite -idmxE (@scalar_mx_block _ 3 1 1) (add_block_mx 1 0 0 1 0 _ v) !(addr0,add0r).
Qed.

Lemma p41eq234 w v : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in
  g^-1 *m \T(v, w) *m g = \T(h *: w, w).
Proof.
move=> w1 g h.
rewrite inv_rigid_transE /inv_rigid_trans /rigid_trans /Twistmx.
rewrite (mulmx_block 1 0 (- _ *v _) 1 \S( w )) !(mulmx0,addr0,mul0mx,mul1mx).
rewrite skew_mxE crossmulNv crossmulvN.
rewrite double_crossmul dotmulvv w1 expr1n scale1r opprB subrK.
by rewrite (mulmx_block \S( w ) 0 _ 0 1 0) !(mulmx0,addr0,mul0mx,mul1mx,mulmx1).
Qed.

Lemma p42eq235 w v a k :
  let g := rigid_trans w v in
  let e' := g^-1 *m \T(v, w) *m g in
  emx (a *: (\T(v, w) : 'M__) ) k = g * emx (a *: e') k * g^-1.
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
  emx (a *: (\T(v, w) : 'M__) ) 2 = g *m hom (emx (a *: \S( w)) 2) (h *: (a *: w)) *m g^-1.
Proof.
move=> w1 g h.
rewrite {1}/emx 2!big_ord_recl big_ord0 addr0 liftE0 eqxx /ecoef factS fact0 invr1 2!scale1r.
rewrite expr0 expr1 /Twistmx.
rewrite (_ : 1 = @block_mx _ 3 _ 3 _ 1 0 0 1); last first.
  by rewrite -idmxE (@scalar_mx_block _ 3 1 1).
rewrite twistZ /= (add_block_mx 1 0 0 1 \S( a *: w )) !(addr0,add0r).
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
Lemma emx_twistE (t : Twist.t R) a k :
  emx (a *: (t : 'M__)) k.+2 = emx_twist a t k.+2.
Proof.
set v := lin_of_twist t.
set w := ang_of_twist t.
rewrite (_ : t = \T(v, w)); last first.
  rewrite {}/v {}/w.
  by case: t => v w; rewrite ang_of_twistE lin_of_twistE.
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
rewrite ang_of_twistZ ang_of_twistE norm_scale_normalize (negbTE w0).
rewrite skew_mxZ; congr hom.
(*rewrite [in RHS]scalerA divrr ?scale1r; last by rewrite unitfE norm_eq0.

rewrite /emx_twist /hom_twist.
rewrite ang_of_twistE (negbTE w0).
rewrite skew_mxZ; congr hom.*)

rewrite crossmulZv crossmulvZ scalerA.
rewrite dotmulZv dotmulvZ !mulrA -[in X in _ + X + _]scalerA.
rewrite crossmulvZ crossmulNv [in X in _ + _ + X = _]scalerN crossmulZv [in X in _ + _ + X]scalerA.
rewrite -scalemxAl -scalerDr -scalerBr; congr (_ *: _).
  by rewrite -invrM ?unitfE ?norm_eq0.
rewrite -/w' /= [in X in _ = X + _]mulmxBr mulmx1.
rewrite -[in RHS]addrA [in RHS]addrC; congr (_ + _ + _).
- rewrite lin_of_twistZ lin_of_twistE crossmulC mulNmx.
  by rewrite scalerA divrr ?unitfE ?norm_eq0 ?scale1r.
- rewrite lin_of_twistZ lin_of_twistE.
  rewrite (scalerA (norm w)) divrr ?scale1r ?unitfE ?norm_eq0 //.
  rewrite -scalemxAl.
  rewrite mulmxA.
  rewrite (mx11_scalar (v *m _ ^T)) -/(v *d w) mul_scalar_mx dotmulC.
  by rewrite scalerA mulrC -scalerA.
- rewrite crossmulC opprK; congr (_ *v _).
  by rewrite -twistZ scalerA divrr ?scale1r ?lin_of_twistE // unitfE norm_eq0.
Qed.

(* [murray] proposition 2.8, p. 41 *)
Lemma emx_twist_SE3 v w a k :
  emx \S(a *: w) k.+2 \is 'SO[R]_3 ->
  emx (a *: (\T(v, w) : 'M__)) k.+2 \is 'SE3[R].
Proof.
move=> emx_SO; rewrite emx_twistE.
rewrite /emx_twist /hom_twist ang_of_twistE.
case: ifPn => [_|w0]; by rewrite hom_is_SE // rpred1.
Qed.

End exponential_coordinates_rigid_using_taylor.

(*Module AngleR.
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
End AngleR.*)

Section rodrigues_gen.

Variable R : rcfType.

(* NB: technical generalization of Rodrigues' formula*)
Definition rodrigues_gen (v : 'rV[R]_3) a w :=
  v - (1 - cos a) *: (norm w ^+ 2 *: v) + (1 - cos a) * (v *d w) *: w + sin a *: (w *v v).

Lemma rodrigues_genP u a w : rodrigues_gen u a w = u *m `e^(a, w).
Proof.
rewrite /rodrigues_gen.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE -!addrA; congr (_ + _).
rewrite !addrA.
rewrite [in X in _ = _ + X]crossmulC scalerN.
rewrite [in X in _ = _ - X]crossmulC.
rewrite double_crossmul dotmulvv.
rewrite scalerN opprK.
rewrite scalerBr [in RHS]addrA [in RHS]addrC -!addrA; congr (_ + (_ + _)).
by rewrite dotmulC scalerA. 
Qed.

End rodrigues_gen.

Require Import boolp reals.

Section exponential_coordinates_rigid.

Variable R : rcfType (* NB: realType not yet compatible with angle, defined using rcfType *).

Axiom R2pi : R.
Axiom R2pi_gt1 : 1 < R2pi.
Axiom radian : angle R -> R.
Definition radian_codom := [pred x | 0 <= x < R2pi].
Axiom radian_codomP : forall x, radian x \in radian_codom.
(*Axiom Repr : R -> nat * angle R.*)
(*Axiom ReprE : forall x, x = R2pi *+ (Repr x).1 + radian (Repr x).2.*)
Axiom angle_of_radian : R -> angle R (* NB: in other words: (Repr x).2 *).
Axiom radianK : cancel radian angle_of_radian.
Axiom angle_of_radianK : forall x, x \in radian_codom -> radian (angle_of_radian x) = x.
Axiom radian0 : forall a, (radian a == 0) = (a == 0).

(* NB: same definition as exp_twist but using exp_mat instead of the taylor expansion of
   the exponential *)
(* [springer] eqn 1.27, p. 17, closed expression for the exponential of a twist *)
Definition etwist a (t : Twist.t R) :=
  hom_twist t (radian a) (`e^(a, \w( t ))).

Local Notation "'`e$(' a ',' t ')'" := (etwist a t) (format "'`e$(' a ','  t ')'").

Lemma etwistv0 (a : angle R) : `e$(a, \T(0, 0)) = hom 1 0.
Proof. by rewrite /etwist ang_of_twistE /hom_twist ang_of_twistE eqxx lin_of_twistE scaler0. Qed.

Lemma etwist_is_SE (t : Twist.t R) a :
  norm \w( t ) = 1 -> `e$(a, t) \in 'SE3[R].
Proof. 
move=> w1.
rewrite /etwist /hom_twist.
case: t w1 => w v.
rewrite ang_of_twistE => w1.
by rewrite (negbTE (norm1_neq0 w1)) hom_is_SE // eskew_is_SO.
Qed.

Definition etwist_is_onto_SE_mat a w :=
  (radian a * norm w ^+ 2)%:A
    + ((1 - cos a) * norm w ^+2) *: \S(w)
      + (radian a - sin a) *: \S(w)^+2.

Definition etwist_is_onto_SE_mat_inv a w :=
  (radian a)^-1%:M
   - 2%:R^-1 *: \S(w)
     + ((radian a)^-1 - 2%:R^-1 * cot (half_angle a)) *: \S(w) ^+ 2.

Lemma etwist_is_onto_SE_matP a w (a0 : a != 0) (w1 : norm w = 1) :
  etwist_is_onto_SE_mat_inv a w * etwist_is_onto_SE_mat a w = 1.
Proof.
rewrite /etwist_is_onto_SE_mat /etwist_is_onto_SE_mat_inv.
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
  exists t a, f = `e$(angle_of_radian a, t).
Proof.
set p := trans_of_hom f.
case/boolP: (rot_of_hom f == 1) => rotf fSE.
case/boolP : (angle_of_radian (norm p) == 0) => p0.
    exists \T(p, 0), 1.
    rewrite /etwist /hom_twist ang_of_twistE eqxx lin_of_twistE.
    rewrite angle_of_radianK; last by rewrite inE R2pi_gt1 ler01.
    by rewrite scale1r (SE3E fSE) (eqP rotf).
  exists \T((radian (angle_of_radian (norm p)))^-1 *: p, 0), 
         (radian (angle_of_radian (norm p))).
  rewrite /etwist /hom_twist ang_of_twistE eqxx /= lin_of_twistE.
  rewrite angle_of_radianK; last by  apply radian_codomP.
  rewrite scalerA divrr; last by rewrite unitfE radian0.
  by rewrite scale1r (SE3E fSE) (eqP rotf).
case: (eskew_is_onto_SO (rot_of_hom_SO fSE)) => a [w [w1 fexp_skew]].
have a0 : a != 0.
  apply: contra rotf => /eqP.
  rewrite fexp_skew => ->; by rewrite emx30M.
set A : 'M_3 := \S(w) *m (1 - rot_of_hom f) + radian a *: (w^T *m w).
suff [v Hv] : exists v, p = (norm w)^-2 *: (v *m A).
  exists \T(v, w), (radian a).
  rewrite (SE3E fSE) /etwist /hom_twist ang_of_twistE.
  have /negbTE -> : w != 0.
    apply: contra rotf; rewrite fexp_skew => /eqP ->.
    by rewrite skew_mx0 emx3a0.
  rewrite radianK fexp_skew -/p Hv; congr (hom _ (_ *: _)).
  rewrite lin_of_twistE.
  by rewrite /A mulmxDr mulmxA skew_mxE -scalemxAr -scalemxAl fexp_skew.
have HA : A = etwist_is_onto_SE_mat a w.
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
suff : exists A' : 'M_3 , A' * A = 1.
  case => A' AA'.
  exists ((norm w) ^+2 *: p *m A').
  rewrite -mulmxA mulmxE AA' mulmx1 scalerA.
  rewrite mulrC divrr ?scale1r // unitfE expf_eq0 /= norm_eq0.
  apply: contra rotf; rewrite fexp_skew => /eqP ->.
  by rewrite skew_mx0 emx3a0.
(* NB: corresponds to [murray], exercise 9, p.75 *)
(* NB: formula for the inverse matrix in
   [Introduction to Robotics: Mechanics, Planning, and Control,
    F.C. Park, K. Lynch, Mar. 14 2012]
 *)
exists (etwist_is_onto_SE_mat_inv a w).
rewrite HA.
exact: (etwist_is_onto_SE_matP a0 w1).
Qed.

(* NB: pitch est redefini plus bas *)
Definition pitch_tmp (w v : 'rV[R]_3) : R := (norm w)^-2 *: v *d w. 

Lemma etwistE a v w : norm w = 1 ->
  `e$(a , \T(v, w)) = 
  hom (`e^(a, w)) (if w == 0 then (radian a) *: v else 
                  (radian a * pitch_tmp w v / radian (pi *+ 2)) *:  w).
Proof.
move=> w1.
rewrite /etwist /hom_twist ang_of_twistE; case: ifPn => [/eqP ->|w0].
  rewrite lin_of_twistE; congr hom.
  by rewrite skew_mx0 emx3a0.
congr hom.
rewrite /pitch_tmp dotmulZv mulrCA -mulrA -scalerA; congr (_ *: _).
rewrite lin_of_twistE mulmxA -scalemxAl (_ : v *m w^T = (v *d w)%:M); last first.
  by rewrite /dotmul -mx11_scalar.
rewrite (_ : _ *m _ = 0) ?add0r; last first.
  rewrite mulmxBr mulmx1 -rodrigues_genP /rodrigues_gen.
  admit.
Admitted.

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

Module Example.
Section example.
Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Variables l1 l2 : R.
Variable a : angle R.
Hypothesis a0 : a != 0.

Definition TAB := row3 (- l2 * sin a) (l1 + l2 * cos a) 0.

Definition w : vector := 'e_2%:R.

Let A_inv := etwist_is_onto_SE_mat_inv a w.

Definition v := ((norm w)^+2 *: TAB) *m A_inv.

Lemma vP : v = row3 ((l1 - l2) / 2%:R) ((l1 + l2) * sin a / (2%:R * (1 - cos a))) 0 :> vector. 
Proof.
rewrite /v normeE expr1n scale1r /TAB.
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
  by rewrite mulrC addrC.
congr row3.
  rewrite mulrCA mulrBl -(mulrA 2%:R^-1 _ (sin a)) cot_half_angle'.
  rewrite -(mulrA (1 + cos a)) mulVr ?mulr1; last first.
    rewrite unitfE; apply: contra a0 => /eqP/sin0_inv[-> //|/eqP].
    by rewrite (negbTE api).
  rewrite mulrDr addrCA !addrA mulrCA mulrA subrr add0r.
  rewrite mulrN.
  rewrite 3!mulrDr mulr1 opprD.
  rewrite addrCA mulrCA addrK.
  by rewrite mulrC -mulrN -mulrDr addrC mulrC.
rewrite cot_half_angle.
rewrite -mulf_div.
rewrite -cot_half_angle.
rewrite mulrDl {1}opprD addrCA !addrA.
rewrite -opprD {1}mulrN (addrC (- _)) subrr add0r.
rewrite mulrN mulNr opprK.
rewrite mulrDr -[in RHS]mulrA addrCA.
rewrite mulrDl [in RHS]mulrCA [in RHS](mulrC l1) (mulrA _ _ l1); congr (_ + _).
rewrite -!mulrA -mulrDr [in RHS]mulrCA; congr (_ * _).
rewrite mulrCA -mulrDr; congr (_ * _).
rewrite cot_half_angle.
rewrite mulrAC -{1}(mulr1 (sin a)) -{1}(@divrr _ (1 - cos a)); last first.
  by rewrite unitfE subr_eq0; apply: contra a0 => /eqP/esym/cos1_angle0 ->.
rewrite mulrA -mulrDl; congr (_ / _).
by rewrite mulrBr mulr1 subrK.
Qed.

End example.
End Example.

(* screws: a geometric description of twists *)

Module Screw.
Section Screw.
Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Record t := mk {
  l : line R (* axis *) ;
  a : angle R (* magnitude *) ;
  h : R (* pitch *) }.
End Screw.
End Screw.

Section screw_motion.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* rotation by an amount a about the axis w follows by a translation ha parallel to w *)
Definition screw_motion (s : Screw.t R) (p : point) :=
  let: (l, a, h) := (Screw.l s, Screw.a s, Screw.h s) in
  let (p0, w) := (line_point l, line_vector l) in
  p0 + (p - p0) *m `e^(a, w) + (h * radian a) *: w.

(* the rbt given by a screw *)
Definition hom_screw_motion s : 'M[R]__ :=
  let l := Screw.l s in let a := Screw.a s in let h := Screw.h s in
  let q := line_point l in let w := line_vector l in
  hom (`e^(a, w)) (q *m (1 - `e^(a, w)) + (h * radian a) *: w).

Lemma hom_screwa0 s : Screw.a s = 0 -> hom_screw_motion s = hom 1 0.
Proof.
move=> a0.
rewrite /hom_screw_motion a0 emx30M subrr mulmx0 add0r.
rewrite (_ : radian 0 = 0) ?mulr0 ?scale0r //; by apply/eqP; rewrite radian0.
Qed.

Lemma hom_screww0 s : line_vector (Screw.l s) = 0 -> hom_screw_motion s = hom 1 0.
Proof. move=> w0; by rewrite /hom_screw_motion w0 skew_mx0 emx3a0 subrr mulmx0 add0r scaler0. Qed.

Lemma hom_screwE s (p : point) (w1 : norm (line_vector (Screw.l s)) = 1) :
  let l := Screw.l s in let a := Screw.a s in let h := Screw.h s in
  let q := line_point l in let w := line_vector l in
  SE.ap_point (SE.mk (q *m (1 - `e^(a, w)) + (h * radian a) *: w)
                     (eskew_is_SO a w1)) p = screw_motion s p.
Proof.
move=> l a h q w.
rewrite SE.ap_pointE mul_mx_row add_row_mx mulmx0 add0r to_hpointK.
rewrite addrA /hom_screw_motion /=; apply/rowP => i.
rewrite mxE [in RHS]mxE; congr (_ + _).
rewrite mulmxBr mulmx1 addrCA mxE [in RHS]mxE; congr (_ + _).
by rewrite mulmxBl.
Qed.

(* [murray] p. 47
  in fact, if we choose v = - w x q + h w, then \xi = (v, w) generates the screw motion
  in equation 2.40
*)

Lemma hom_screw_motion_etwist s :
  let: (l, a, h) := (Screw.l s, Screw.a s, Screw.h s) in
  let (q, w) := (line_point l, line_vector l) in
  let v := - w *v q + h *: w in
  hom_screw_motion s = `e$(a, \T(v, w)) :> 'M_4.
Proof.
rewrite /=.
set l := Screw.l s.
set a := Screw.a s.
set h := Screw.h s.
set q := line_point l.
set w := line_vector l.
set v := _ + _.
(*case/boolP : (radian a == 0) => [|a0].
  rewrite radian0 => /eqP ->.
  rewrite /etwist /hom_screw /hom_twist.
  rewrite (_ : radian 0 = 0); last by apply/eqP; rewrite radian0.
  rewrite !exp_mat0v subrr mulr0 scale0r mulmx0 addr0 scale0r mulmx0 mul0mx.
  rewrite addr0 scaler0; by case: ifPn.*)
rewrite /etwist /hom_twist. (*/hom_screw unskewK block_mxKul /= ?anti_skew //.*)
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
Definition axis (t : 'M[R]_4) : line R :=
  let w := \w( t ) in let v := \v( t ) in
  if w == 0 then
    mkDline 0 v
  else
    mkDline ((norm w)^-2 *: (w *v v)) w.

(* [murray] 2.42, p.47 *)
Definition pitch (t : 'M[R]_4) : R := 
  let w := \w( t ) in let v := \v( t ) in
  (norm w)^-2 *: v *d w. 

(* [murray] 2.44, p.48 *)
Definition magnitude (t : 'M[R]_4) : R := 
  let w := \w( t ) in let v := \v( t ) in
  if w == 0 then norm v else norm w. 

Lemma magnitudeZ (t : 'M[R]_4) a : 0 < a ->
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
Definition utwist (t : 'M[R]_4) := (magnitude t == 1).

Lemma utwistE (t : 'M[R]_4) : utwist t = 
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
Lemma magn_of_utwistZ a (t : Twist.t R) : 0 < a -> utwist t ->
  magnitude (a *: (t : 'M_4) ) = a.
Proof. move=> a0 Ht; by rewrite magnitudeZ // (eqP Ht) mulr1. Qed.

Definition ScrewTwist t := Screw.mk (axis t) (angle_of_radian (pitch t)) (magnitude t).

End screw_coordinates_of_a_twist.

Section screw_motion_utwist.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* [murray] proposition 2.10, p.48 *)
(* TODO: not yet right *)
Lemma hom_screw_motion_eutwist (s : Screw.t R) :
  let a := Screw.a s in
  exists t' : Twist.t R, (*utwist t' /\*)
  hom_screw_motion s = `e$(a, (\T( \v( t'), \w( t' )))).
Proof.
move=> a.
set l := Screw.l s.
set h := Screw.h s.
set w := line_vector l.
set q := line_point l.
set v := - w *v q + h *: w.
case/boolP : (w == 0) => [/eqP|]w0.
  exists \T(v, 0).
  rewrite ang_of_twistE lin_of_twistE /v w0 crossmulNv crossmul0v oppr0 scaler0 addr0 etwistv0.
  by rewrite hom_screww0.
exists \T(v, w).
by rewrite lin_of_twistE ang_of_twistE hom_screw_motion_etwist.
Qed.

End screw_motion_utwist.

Section screw_axis.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Variable f : 'DIso_3[R].
Let Q : 'M[R]_3 := ortho_of_iso f.
Let T : vector := trans_of_iso f.
Variable w : vector.
Hypothesis w1 : norm w = 1.
Variable a : angle R.
Hypothesis Qaxis : is_around_axis w a (mx_lin1 Q).

(* [angeles] theorem 3.2.1, p.97: 
   the displacements of all the points of the body have the same projection onto e *)

Lemma displacement_proj (q p : point) : displacement f q *d w = displacement f p *d w.
Proof.
rewrite /dotmul; congr (fun_of_matrix _ 0 0).
rewrite (displacement_iso f p q) [in RHS]mulmxDl -[LHS](addr0); congr (_ + _).
rewrite -mulmxA (mulmxBl Q) mul1mx.
suff -> : Q *m w^T = w^T by rewrite subrr mulmx0.
rewrite -{1}(is_around_axis_axis Qaxis) trmx_mul mulmxA mulmxE.
move: (ortho_of_iso_is_O f); rewrite -/Q orthogonalE => /eqP ->; by rewrite mul1mx.
Qed.

Definition d0 := displacement f 0 *d w.

Lemma d0_is_a_lb_of_a_displacement p : d0 ^+ 2 <= norm (displacement f p) ^+ 2.
Proof.
rewrite /d0 (displacement_proj 0 p).
set F := Base.frame (norm1_neq0 w1).
have -> : norm (displacement f p) =
          norm (displacement f p *m (col_mx3 (normalize w) (Base.j w) (Base.k w))^T).
rewrite orth_preserves_norm // orthogonalV rotation_sub //.
  exact: (frame_is_rot F).
rewrite col_mx3_mul sqr_norm !mxE /= -[X in X <= _]addr0 -addrA ler_add //.
  by rewrite normalizeI.
by rewrite addr_ge0 // sqr_ge0.
Qed.

Definition parpart (p : point) := axialcomp (displacement f p) w.

Lemma parpartP p : parpart p = d0 *: (w : 'rV[R]_3).
Proof. by rewrite /parpart /axialcomp dotmulC (displacement_proj _ 0). Qed.

Definition perppart (p : point) := normalcomp (displacement f p) w.

(* [angeles] theorem 3.2.2, p.97 *)
(* d0 is the minimal norm of a displacement, all such points are along a line parallel
   to e *)
Lemma MozziChasles p :
  norm (displacement f p) = d0 -> colinear (displacement f p) w.
Proof.
move=> H.
have Hp : forall p : point,
    norm (displacement f p) ^+ 2 = norm (d0 *: (w : 'rV[R]_3)) ^+2 + norm (perppart p) ^+ 2.
  move=> p'.
  rewrite (decomp (displacement f p') w) normD -dotmul_cos.
  rewrite axialnormal // ?neq // mul0rn addr0 sqr_sqrtr; last first.
    by rewrite addr_ge0 // ?sqr_ge0.
  by rewrite /perppart -/(parpart p') parpartP.
move: {Hp}(Hp p) => Hp.
rewrite -normalcomp_colinear ?ne // -norm_eq0.
suff : norm (displacement f p) ^+2 <= norm (d0 *: (w : 'rV[R]_3)) ^+ 2.
  by rewrite Hp addrC -ler_subr_addr subrr exprn_even_le0 //= norm_eq0.
rewrite 2!expr2.
by rewrite ler_pmul // ?norm_ge0 // H normZ w1 mulr1 ler_norm.
Qed.

Definition pitch_new := d0 / radian a.

Lemma wTwQN1 : (w^T *m w) *m (Q - 1)^T = 0.
Proof.
rewrite (is_around_axis_exp_skew'_new w1 Qaxis) linearD /=.
rewrite [in X in _ *m (_ + X)]linearN /= trmx1.
rewrite mulmxBr mulmx1 /exp_skew'.
rewrite -addrA linearD /= mulmxDr trmx_mul trmxK.
rewrite mulmxE -expr2 mulmx_tr_uvect //.
rewrite addrC addrA (addrC (- _)) subrr add0r.
rewrite linearD /= 2!linearZ /= tr_skew scalerN.
rewrite mulrDr -scalerAr linearD /= trmx1 linearN /= trmx_mul trmxK mulrBr.
rewrite mulr1 -expr2 mulmx_tr_uvect // subrr scaler0 add0r.
by rewrite mulrN -scalerAr -mulmxE -mulmxA skew_mxE crossmulvv mulmx0 scaler0 oppr0.
Qed.

Lemma QN1wTw : (Q - 1)^T *m (w^T *m w) = 0.
Proof.
rewrite (is_around_axis_exp_skew'_new w1 Qaxis) linearD /=.
rewrite mulmxDl [in X in _ + X = _]linearN /= trmx1 mulNmx mul1mx.
rewrite linearD /=.
rewrite linearZ /= tr_skew scalerN mulmxDl.
rewrite mulNmx.
rewrite -scalemxAl !mulmxA skew_mxT mul0mx scaler0 subr0.
rewrite linearD /= trmx_mul trmxK.
rewrite -mulmxA mulmxDl mulmxE -expr2 mulmx_tr_uvect //.
rewrite addrC addrA (addrC (- _)) subrr add0r.
rewrite linearZ /= -mulmxE -scalemxAl.
rewrite linearD /= trmx1 linearN /= trmx_mul trmxK mulmxBl.
rewrite mul1mx mulmxE -expr2 mulmx_tr_uvect //.
by rewrite subrr scaler0.
Qed.

Definition Ncos2 := (1 - cos a) *+ 2.
Definition N2cos := 1 - cos a *+ 2.

Lemma unitNcos2 (a0 : a != 0) : Ncos2 \is a GRing.unit.
Proof.
rewrite unitfE /Ncos2 mulrn_eq0 negb_or /= subr_eq0 eq_sym.
apply/eqP => /cos1_angle0; by apply/eqP.
Qed.

Lemma N2cosNcos2 (a0 : a != 0) : N2cos - Ncos2^-1 * N2cos - N2cos / Ncos2 * N2cos = 0.
Proof.
rewrite (mulrC N2cos) -mulrA -{1}(mulKr (unitNcos2 a0) N2cos) -2!mulrBr; apply/eqP.
rewrite mulf_eq0 invr_eq0.
move: (unitNcos2 a0); rewrite unitfE => /negPf -> /=.
rewrite -{2}(mul1r N2cos) -2!mulrBl mulf_eq0.
rewrite -addrA -opprB opprK subr_eq0.
by rewrite /Ncos2 {1}/N2cos mulrnBl addrAC eqxx.
Qed.

Lemma Ncos2V (a0 : a != 0) : (Ncos2^-1)%:M *m Ncos2%:M = 1 :> 'M_3.
Proof. by rewrite -scalar_mxM mulVr // unitNcos2. Qed.

Definition screw_axis_point (x : point) : point :=
  1 / Ncos2 *: (x *m Q - f x) *m (Q - 1)^T.

Definition screw_axis_point_mat :=
  let A := row_mx (Q - 1) w^T in A *m A^T.

Definition screw_axis_point_mat_inv : 'M_3 :=
  Ncos2^-1 *: 1 + N2cos / Ncos2 *: w^T *m w.

Lemma screw_axis_point_matE : let A := row_mx (Q - 1) w^T in
  A *m A^T = Ncos2 *: 1 - N2cos *: w^T *m w.
Proof.
move=>A.
rewrite /A tr_row_mx mul_row_col trmxK linearD /= linearN /= trmx1.
rewrite mulmxBr mulmx1 opprB mulmxBl mul1mx.
move: (ortho_of_iso_is_O f); rewrite -/Q orthogonalE mulmxE => /eqP ->.
rewrite addrA (addrC (1 - _)) addrA.
rewrite (_ : 1 + 1 = 2%:R) //.
rewrite /Ncos2 mulrnBl scalerBl -2!addrA -[in RHS]addrA; congr (_ + _).
  rewrite scalemx1.
  by apply/matrix3P; rewrite !mxE ?eqxx /= ?mulr1n // ?mulr0n // addr0.
rewrite addrA.
rewrite {1}(is_around_axis_exp_skew'_new w1 Qaxis).
rewrite /exp_skew'.
rewrite -(addrA (w^T *m w)).
rewrite linearD /= trmx_mul trmxK opprD addrC 2!addrA subrr add0r.
rewrite linearD /= linearZ /= linearZ /= 2!linearD /= trmx1.
rewrite (is_around_axis_exp_skew'_new w1 Qaxis).
rewrite opprD !addrA addrC !addrA tr_skew.
rewrite (scalerN (sin a) \S( w )) opprK.
rewrite (addrC (- (sin a *: _))) subrK.
rewrite linearN /= trmx_mul trmxK opprD addrA addrAC -scaleNr -scalerDl.
rewrite -mulr2n scalerBr scalemx1 scalemx1 -addrA; congr (_ + _).
  apply/matrix3P; by rewrite !mxE ?eqxx ?mulr1n ?mulr0n // ?oppr0 // mulNrn.
rewrite -scalemxAl /N2cos [in RHS]scalerBl scale1r opprB; congr (_ + _).
by rewrite mulNrn scaleNr opprK.
Qed.

Lemma screw_axis_point_Vmat (a0 : a != 0) :
  screw_axis_point_mat_inv * screw_axis_point_mat = 1.
Proof.
rewrite /screw_axis_point_mat /screw_axis_point_mat_inv screw_axis_point_matE !scalemx1 -!mulmxE.
rewrite mulmxBr mulmxDl Ncos2V // -[RHS]addr0 -addrA; congr (_ + _).
rewrite mul_mx_scalar -{1}scalemxAl {1}(mulrC N2cos) scalerA mulrA mulrV ?unitNcos2 // mul1r.
rewrite mulmxDl.
rewrite opprD addrA mul_scalar_mx -[in X in X - _ = 0]scalemxAl scalerA.
rewrite -scalerBl.
rewrite -3![in X in _ - X = 0]scalemxAl.
rewrite -[in X in _ - X = 0]scalemxAr.
rewrite [in X in _ - X = 0]scalerA.
rewrite mulmxE -expr2 mulmx_tr_uvect // -scalerBl.
by apply/eqP; rewrite scaler_eq0 (N2cosNcos2 a0) eqxx.
Qed.

Lemma screw_axis_point_matV (a0 : a != 0) :
  screw_axis_point_mat * screw_axis_point_mat_inv = 1.
Proof.
rewrite /screw_axis_point_mat /screw_axis_point_mat_inv screw_axis_point_matE !scalemx1 -!mulmxE.
rewrite mulmxBl mulmxDr {1}mulmxE (scalar_mx_comm (Ncos2^-1)) -{1}mulmxE Ncos2V //.
rewrite -[RHS]addr0 -addrA; congr (_ + _).
rewrite mul_scalar_mx -{1}scalemxAl scalerA mulrC -mulrA mulVr ?unitNcos2 // mulr1.
rewrite mulmxDr.
rewrite opprD addrA mul_mx_scalar -[in X in X - _ = 0]scalemxAl scalerA.
rewrite -scalerBl.
rewrite -3![in X in _ - X = 0]scalemxAl.
rewrite -[in X in _ - X = 0]scalemxAr.
rewrite [in X in _ - X = 0]scalerA.
rewrite mulmxE -expr2 mulmx_tr_uvect // -scalerBl.
by apply/eqP; rewrite scaler_eq0 (mulrC N2cos) N2cosNcos2 // eqxx.
Qed.

Lemma screw_axis_point_mat_unit (a0 : a != 0) :
  screw_axis_point_mat \is a GRing.unit.
Proof.
apply/unitrP; exists screw_axis_point_mat_inv.
by rewrite screw_axis_point_Vmat // screw_axis_point_matV.
Qed.

Lemma screw_axis_point_mat_invE (a0 : a != 0) :
  let A := row_mx (Q - 1) w^T in
  (A *m A^T)^-1 = screw_axis_point_mat_inv.
Proof.
move=> A.
by rewrite -[LHS]mul1r -screw_axis_point_Vmat // mulrK // screw_axis_point_mat_unit.
Qed.

(* [angeles] Sect. 3.2.1 (the screw of a rigid-body motion) *)
Lemma screw_axis_pointE p0 (* a point on the screw axis *) q (a0 : a != 0) :
  p0 *d w = 0 (* p0 is the closed point to the origin *) ->
  normalcomp (displacement f p0) w = 0 ->
  p0 = screw_axis_point q.
Proof.
move=> p0e0 fp0e0.
have _(*?*) : displacement f p0 *m (Q - 1) = 0.
  have : colinear (displacement f p0) w.
    rewrite (decomp (displacement f p0) w) -/(parpart p0) parpartP.
    by rewrite fp0e0 addr0 colinearZv colinear_refl orbC.
  rewrite -normalcomp_colinear // => /eqP H1.
  rewrite (decomp (displacement f p0) w) H1 addr0.
  rewrite /axialcomp -scalemxAl mulmxBr mulmx1.
  by case: Qaxis => /= -> _ _; rewrite subrr scaler0.
have step2 : displacement f q + relative_displacement f p0 q = displacement f q *m (w^T *m w).
  transitivity (displacement f p0 *m w^T *m w).
    rewrite -(displacement_iso f p0 q) {1}(decomp (displacement f p0) w).
    by rewrite fp0e0 addr0 axialcompE.
  rewrite (mx11_scalar (displacement f p0 *m w^T)) -/(dotmul _ _) (displacement_proj p0 q).
  by rewrite mulmxA (mx11_scalar (displacement f q *m w^T)) -/(dotmul _ _).
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
  rewrite (mx11_scalar (_ *m _)) -/(dotmul p0 w) p0e0.
  by apply/rowP => i; rewrite (ord1 i) !mxE eqxx mulr1n.
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
by rewrite scalemx1 mul_mx_scalar div1r scalemxAl.
Qed.

End screw_axis.
