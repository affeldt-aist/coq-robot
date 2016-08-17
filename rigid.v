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

Require Import aux angle euclidean3 quaternion skew vec_angle rot frame.

(*
 OUTLINE:
 1. section quaternion.
    correction of rotation using unit quaternions
 2. section central_isometry_n
 3. section central_isometry_3
 4. section isometry_prop.
 5. section tangent_vectors_and_frames
 6. section derivative maps of isometries
     definition of what it means to preserve the cross-product by a transformation
     (sample lemma: preservation of the cross-product by derivative maps)
 7. section homogeneous_points_and_vectors
 8. section SE3_def
 9. section rigid_transformation_is_homogeneous_transformation
     (a direct isometry (i.e., cross-product preserving) can be expressed in homogeneous coordinates)
     (NB: converse in progress (?))
 10. section kinematic_chain
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Module Iso.
Section isometry.
Variables (R : rcfType) (n : nat).
Record t := mk {
  f :> 'rV[R]_n -> 'rV[R]_n ;
  P : {mono f : a b / norm (a - b)} }.
End isometry.
End Iso.

Notation "''Iso[' R ]_ n" := (Iso.t R n)
  (at level 8, n at level 2, format "''Iso[' R ]_ n").
Definition isometry_coercion := Iso.f.
Coercion isometry_coercion : Iso.t >-> Funclass.

Module CIso.
Section central_isometry.
Variable (R : rcfType) (n : nat).
Record t := mk {
  f : 'Iso[R]_n ;
  P : f 0 = 0 }.
End central_isometry.
End CIso.

Notation "''CIso[' R ]_ n" := (CIso.t R n)
  (at level 8, n at level 2, format "''CIso[' R ]_ n").
Definition cisometry_coercion := CIso.f.
Coercion cisometry_coercion : CIso.t >-> Iso.t.

Section central_isometry_n.

Variable (R : rcfType) (n : nat).

Lemma central_isometry_preserves_norm (f : 'CIso[R]_n) : {mono f : x / norm x}.
Proof. by case: f => f f0 p; rewrite -(subr0 (f p)) -f0 Iso.P subr0. Qed.

Lemma central_isometry_preserves_dotmul (f : 'CIso[R]_n) : {mono f : u v / u *d v}.
Proof.
case: f => f f0 a b.
have : norm (f a - f b) = norm (a - b) by rewrite (Iso.P f).
rewrite /norm => /eqP.
rewrite eqr_sqrt ?le0dotmul // !dotmulDl !dotmulDr !dotmulvv !normN.
rewrite !(central_isometry_preserves_norm (CIso.mk f0)) !addrA 2!(addrC _ (norm b ^+ 2)).
move/eqP/addrI.
rewrite -2!addrA => /addrI.
rewrite -(dotmulC (f a)) dotmulvN -(dotmulC a) dotmulvN -2!mulr2n.
move/eqP.
rewrite -mulr_natr -[in X in _ == X -> _]mulr_natr 2!mulNr eqr_opp.
by move/eqP/mulIr => -> //; rewrite unitfE pnatr_eq0.
Qed.

End central_isometry_n.

Section central_isometry_3.

Variable R : rcfType.

Lemma frame_central_iso (f : 'CIso[R]_3) i j k :
  oframe i j k -> oframe (f i) (f j) (f k).
Proof.
case => *; apply mkOFrame; by
  rewrite /= central_isometry_preserves_norm ||
  rewrite /= central_isometry_preserves_dotmul.
Qed.

Lemma central_isometry_is_linear (f : 'CIso[R]_3) : linear f.
Proof.
move=> k /= a b.
have Hp : forall p, f p = p``_0 *: f 'e_0 + p``_1 *: f 'e_1 + p``_2%:R *: f 'e_2%:R.
  move=> p.
  have -> : f p = f p *d f 'e_0 *: f 'e_0 + f p *d f 'e_1 *: f 'e_1 + f p *d f 'e_2%:R *: f 'e_2%:R.
    rewrite -orthogonal_expansion //.
    apply frame_central_iso => //; exact: can_oframe.
  by rewrite 3!central_isometry_preserves_dotmul // 3!coorE.
rewrite Hp (Hp a) (Hp b) !mxE /= !(scalerDl, scalerDr).
rewrite !scalerA -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrC -!addrA.
Qed.

End central_isometry_3.

Section isometry_prop.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Definition lin1_mx' n (f : 'rV[R]_n -> 'rV[R]_n) : linear f ->
  {M : {linear 'rV[R]_n -> 'rV[R]_n} & forall x, f x = M x}.
Proof.
move=> H.
have @g : {linear 'rV[R]_n -> 'rV[R]_n}.
  exists f; exact: (GRing.Linear.class_of_axiom H).
by exists g.
Defined.

Lemma trans_ortho_of_iso (f : 'Iso[R]_3) :
  { trans : 'rV[R]_3 & { rot : 'M[R]_3 |
    (forall x : 'rV[R]_3, f x == x *m rot + trans) /\
    rot \is 'O[R]_3 /\
    trans = f 0 } }.
Proof.
set T := f 0.
set Tm1f := fun x => f x - T.
have Tm1f_is_iso : {mono Tm1f : a b / norm (a - b)}.
  move=> ? ?; by rewrite /Tm1f -addrA opprB 2!addrA subrK (Iso.P f).
have Tm1f0 : Tm1f 0 = 0 by rewrite /Tm1f subrr.
have /= linearTm1f : linear (@CIso.mk _ _ (Iso.mk Tm1f_is_iso) Tm1f0).
  by apply: central_isometry_is_linear.
have orthogonalTm1f : {mono Tm1f : u v / u *d v}.
  move=> ? ?; by rewrite (central_isometry_preserves_dotmul
    (@CIso.mk _ _ (Iso.mk Tm1f_is_iso) Tm1f0)).
exists T.
case: (lin1_mx' linearTm1f) => g Hg.
exists (lin1_mx g); split; last first.
  split; last by done.
  apply orth_preserves_dotmul => u v /=.
  by rewrite 2!mul_rV_lin1 -[in RHS]orthogonalTm1f 2!Hg.
move=> u; by rewrite mul_rV_lin1 -Hg subrK.
Qed.

Definition ortho_of_iso (f : 'Iso[R]_3) : 'M[R]_3 := projT1 (projT2 (trans_ortho_of_iso f)).

Definition trans_of_iso (f : 'Iso[R]_3) : 'rV[R]_3 := projT1 (trans_ortho_of_iso f).

Lemma trans_of_isoE (f : 'Iso[R]_3) : trans_of_iso f = f 0.
Proof.
rewrite /trans_of_iso; by case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
Qed.

Lemma ortho_of_iso_is_O f : ortho_of_iso f \is 'O[R]_3.
Proof.
rewrite /ortho_of_iso; by case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
Qed.

Lemma trans_ortho_of_isoE f u : u *m ortho_of_iso f = f u - trans_of_iso f.
Proof.
rewrite /ortho_of_iso /trans_of_iso.
case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
move: (H1 u) => /eqP ->; by rewrite addrK.
Qed.

Lemma ortho_of_iso_eq (f1 f2 : 'Iso[R]_3) :
  (forall i, Iso.f f1 i = Iso.f f2 i) ->
  ortho_of_iso f1 = ortho_of_iso f2.
Proof.
move=> f12.
apply/eqP/mulmxP => u.
rewrite 2!trans_ortho_of_isoE /= 2!trans_of_isoE /=.
case: f1 f2 f12 => [f1 Hf1] [f2 Hf2] /= f12.
by rewrite !f12.
Qed.

Definition iso_sgn (f : 'Iso[R]_3) : R := \det (ortho_of_iso f).

Lemma img_vec_iso (f : 'Iso[R]_3) (a b : point) :
  f b - f a = (b - a) *m ortho_of_iso f.
Proof.
move/esym/eqP: (trans_ortho_of_isoE f a).
move/esym/eqP: (trans_ortho_of_isoE f b).
rewrite mulmxBl => /eqP <- /eqP <-; by rewrite opprB addrA subrK.
Qed.

Definition displacement (f : 'Iso[R]_3) p := f p - p.

Definition relative_displacement (f : 'Iso[R]_3) (p a : point) := 
  (p - a) *m (ortho_of_iso f - 1).

(* NB: caused only by rotation *)
Lemma displacement_iso (f : 'Iso[R]_3) p a :
  displacement f p = displacement f a + relative_displacement f p a.
Proof.
rewrite /relative_displacement mulmxBr mulmx1 opprB addrA -(addrC a) 2!addrA.
rewrite subrK; congr (_ - _).
apply/eqP; by rewrite addrC -subr_eq img_vec_iso.
Qed.

End isometry_prop.

Module DIso.
Section direct_isometry.
Variable (R : rcfType).
Record t := mk {
  f :> 'Iso[R]_3 ;
  P : iso_sgn f == 1 }.
End direct_isometry.
End DIso.

Notation "''DIso_3[' R ]" := (DIso.t R)
  (at level 8, format "''DIso_3[' R ]").
Definition disometry_coercion := DIso.f.
Coercion disometry_coercion : DIso.t >-> Iso.t.

Section tangent_vectors_and_frames.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.
Implicit Types p : point.

(* tangent vector *)
Record tvec p := TVec {tvec_field :> vector}.
Definition vtvec p (v : tvec p) := let: TVec v := v in v.

Local Notation "p .-vec" := (tvec p) (at level 5).

Definition tframe_i p u1 u2 u3 (f : tframe p u1 u2 u3) : p.-vec := TVec p u1.
Definition tframe_j p u1 u2 u3 (f : tframe p u1 u2 u3) : p.-vec := TVec p u2.
Definition tframe_k p u1 u2 u3 (f : tframe p u1 u2 u3) : p.-vec := TVec p u3.

End tangent_vectors_and_frames.

Coercion vtvec_field_coercion := vtvec.
Notation "p .-vec" := (tvec p) (at level 5).

Section derivative_map.

Variable R : rcfType.
Let vector := 'rV[R]_3.

(* [oneill] theorem 2.1, p. 104 *)
Definition dmap (f : 'Iso[R]_3) p (v : p.-vec) :=
  let C := ortho_of_iso f in
  TVec (f p) (v *m C).

Local Notation "f '`*'" := (@dmap f _) (at level 5, format "f `*").

Lemma dmap0 (f : 'Iso[R]_3) p : f `* (TVec p 0) = TVec (f p) 0.
Proof. by rewrite /dmap /= mul0mx. Qed.

Lemma derivative_map_preserves_length (f : 'Iso[R]_3) p :
  {mono (fun x : p.-vec => f`* x) : u v / norm (vtvec u - vtvec v)}.
Proof.
move=> u v; rewrite /dmap /= -(mulmxBl (vtvec u) (vtvec v) (ortho_of_iso f)).
by rewrite orth_preserves_norm // ortho_of_iso_is_O.
Qed.

Lemma dmap_iso_sgnP p e1 e2 e3 (tf : tframe p e1 e2 e3) (f : 'Iso[R]_3) :
  f`* (TVec p e1) *d (f `* (TVec p e2) *v f`* (TVec p e3)) =
  iso_sgn f * (e1 *d (e2 *v e3)).
Proof.
case: tf => fo.
move: (orthogonal_expansion e1 (can_oframe R)).
set a11 := _ *d 'e_0. set a12 := _ *d 'e_1. set a13 := _ *d 'e_2%:R => He1.
move: (orthogonal_expansion e2 (can_oframe R)).
set a21 := _ *d 'e_0. set a22 := _ *d 'e_1. set a23 := _ *d 'e_2%:R => He2.
move: (orthogonal_expansion e3 (can_oframe R)).
set a31 := _ *d 'e_0. set a32 := _ *d 'e_1. set a33 := _ *d 'e_2%:R => He3.
have e1a : e1 = row3 a11 a12 a13.
  apply/rowP => i; rewrite !mxE /= coorE.
  case: ifPn => [/eqP -> //|]; by rewrite ifnot0 => /orP [] /eqP ->.
have e2a : e2 = row3 a21 a22 a23.
  apply/rowP => i; rewrite !mxE /= coorE.
  case: ifPn => [/eqP -> //|]; by rewrite ifnot0 => /orP [] /eqP ->.
have e3a : e3 = row3 a31 a32 a33.
  apply/rowP => i; rewrite !mxE /= coorE.
  case: ifPn => [/eqP -> //|]; by rewrite ifnot0 => /orP [] /eqP ->.
transitivity (\det ((ortho_of_iso f)^T *m
  (col_mx3 (row3 a11 a12 a13) (row3 a21 a22 a23) (row3 a31 a32 a33))^T)).
  rewrite /= -det_tr trmx_mul trmxK mulmx_col3.
  by rewrite -crossmul_triple -e1a -e2a -e3a trmxK.
rewrite det_mulmx det_tr; congr (_ * _).
rewrite det_tr -crossmul_triple; by congr (_ *d (_ *v _)).
Qed.

Lemma dmap_preserves_crossmul p (u v : p.-vec) (f : 'Iso[R]_3) :
  f`* (TVec p (u *v v)) =
    iso_sgn f *: vtvec (TVec (f p) ((f`* u) *v (f`* v))) :> vector.
Proof.
set tf : tframe _ _ _ _ := tframe_trans (TFrame 0 (can_oframe R)) p.
set u1p := tframe_i tf. set u2p := tframe_j tf. set u3p := tframe_k tf.
move: (orthogonal_expansion u (oframe_of_tframe tf)).
set u1 := _ *d 'e_0. set u2 := _ *d 'e_1. set u3 := _ *d 'e_2%:R => Hu.
move: (orthogonal_expansion v (oframe_of_tframe tf)).
set v1 := _ *d 'e_0. set v2 := _ *d 'e_1. set v3 := _ *d 'e_2%:R => Hv.
set e1 := f`* (TVec p u1p). set e2 := f`* (TVec p u2p). set e3 := f`* (TVec p u3p).
have Ku : f`* u = u1 *: vtvec e1 + u2 *: vtvec e2 + u3 *: vtvec e3 :> vector.
  by rewrite /= Hu 2!mulmxDl !scalemxAl.
have Kv : f`* v = v1 *: vtvec e1 + v2 *: vtvec e2 + v3 *: vtvec e3 :> vector.
  by rewrite /= Hv 2!mulmxDl !scalemxAl.
have f' : oframe e1 e2 e3.
  split => //.
  by rewrite orth_preserves_norm ?ortho_of_iso_is_O // norm_delta_mx.
  by rewrite orth_preserves_norm ?ortho_of_iso_is_O // norm_delta_mx.
  by rewrite orth_preserves_norm ?ortho_of_iso_is_O // norm_delta_mx.
  rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_O //.
  by case: (can_oframe R).
  rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_O //.
  by case: (can_oframe R).
  rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_O //.
  by case: (can_oframe R).
have -> : iso_sgn f = frame_sgn f'.
  rewrite /frame_sgn dmap_iso_sgnP /=.
    by rewrite (jcrossk (can_frame _)) dotmulvv norm_delta_mx expr1n mulr1.
  by apply (TFrame _ (can_oframe R)).
have : vtvec (TVec (f p) ((f`* u) *v (f`* v))) =
         frame_sgn f' *: vtvec (f`* (TVec p (u *v v))) :> vector.
  rewrite /=.
  rewrite (@crossmul_oframe_sgn _ e1 e2 e3 _ (f`* u) u1 u2 u3 (f`* v) v1 v2 v3) //.
  rewrite /=.
  congr (_ *: _).
  have -> : 'e_0 *m ortho_of_iso f = vtvec e1 by done.
  have -> : 'e_1 *m ortho_of_iso f = vtvec e2 by done.
  have -> : 'e_2%:R *m ortho_of_iso f = vtvec e3 by done.
  rewrite Hu Hv.
  do 2 rewrite linearD [in RHS]/=.
  rewrite 2!mulmxDl.
  (* on fait les remplacement veci *v vecj -> veck, veci *v veci -> 0, etc. *)
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite crossmulC scalerN.
  rewrite linearD [in RHS]/=.
  rewrite [in X in _ = - (_ *: X) *m _ + _ + _]linearD.
  rewrite [in RHS]/=.
  rewrite (_ : 'e_0 *v (u1 *: _) = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite (_ : 'e_0 *v (u2 *: _) = u2 *: 'e_2%:R); last first.
    by rewrite linearZ /= -(icrossj (can_frame _)).
  rewrite (_ : 'e_0 *v (u3 *: _) = - u3 *: 'e_1); last first.
    by rewrite linearZ /= (icrossk (can_frame _)) scalerN scaleNr.
  rewrite add0r.
  rewrite mulNmx -[in RHS]scalemxAl [in RHS]mulmxDl.
  rewrite -![in RHS]scalemxAl.
  have -> : 'e_2%:R *m ortho_of_iso f = vtvec e3 by done.
  have -> : 'e_1 *m ortho_of_iso f = vtvec e2 by done.
  rewrite [in RHS]scalerDr.
  rewrite opprD.
  rewrite crossmulC [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite scaleNr scalerN opprK.
  rewrite (_ : _ *v _ = - u1 *: 'e_2%:R); last first.
    by rewrite linearZ /= crossmulC -(icrossj (can_frame _)) scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite addr0.
  rewrite (_ : _ *v _ = u3 *: 'e_0); last by rewrite linearZ /= (jcrossk (can_frame _)).
  rewrite scaleNr opprK mulmxBl.
  rewrite -![in RHS]scalemxAl.
  have -> : 'e_0 *m ortho_of_iso f = vtvec e1 by done.
  have -> : 'e_2%:R *m ortho_of_iso f = vtvec e3 by done.
  rewrite scalerDr scalerN.
  rewrite crossmulC [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite (_ : _ *v _ = u1 *: 'e_1); last first.
    by rewrite linearZ /= crossmulC (icrossk (can_frame _)) opprK.
  rewrite (_ : _ *v _ = - u2 *: 'e_0); last first.
    by rewrite linearZ /= crossmulC (jcrossk (can_frame _)) scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite subr0 scaleNr opprK mulmxDl mulNmx.
  rewrite -![in RHS]scalemxAl.
  have -> : 'e_0 *m ortho_of_iso f = vtvec e1 by done.
  have -> : 'e_1 *m ortho_of_iso f = vtvec e2 by done.
  (* on a une expression uniquement avec des vtvec e1, etc. -> on identifie rhs et lhs *)
  rewrite -![in RHS]addrA [in RHS]addrC -[in RHS]addrA [in RHS]addrCA -[in RHS]addrA [in RHS]addrC.
  rewrite ![in RHS]addrA -[in RHS]addrA.
  congr (_ + _); last first.
    by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u1).
  rewrite scalerDr.
  rewrite -![in RHS]addrA [in RHS]addrCA [in RHS]addrC ![in RHS]addrA -addrA; congr (_ + _).
  by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u2).
  by rewrite scalerN !scalerA -scalerBl -scaleNr opprB mulrC (mulrC u1).
move=> ->; by rewrite scalerA -expr2 /iso_sgn -sqr_normr frame_sgn1 expr1n scale1r.
Qed.

Definition preserves_orientation (f : 'Iso[R]_3) :=
  forall p (u v : p.-vec),
  f`* (TVec p (u *v v)) = TVec (f p) ((f`* u) *v (f`* v))
  :> vector.

Lemma direct_iso_preserves_crossmul (f : 'DIso_3[R]) : preserves_orientation f.
Proof. move=> p u v; by rewrite dmap_preserves_crossmul (eqP (DIso.P f)) scale1r. Qed.

Lemma preserves_crossmul_is_direct_iso p (u v : p.-vec) (f : 'Iso[R]_3) :
  ~~ colinear u v ->
  f`* (TVec p (u *v v)) = TVec (f p) ((f`* u) *v (f`* v)) :> vector ->
  iso_sgn f = 1.
Proof.
move=> uv0.
rewrite dmap_preserves_crossmul /iso_sgn => H.
move: (orthogonal_det (ortho_of_iso_is_O f)).
case: (lerP 0 (\det (ortho_of_iso f))) => K; first by rewrite ger0_norm.
rewrite ltr0_norm // => /eqP.
rewrite eqr_oppLR => /eqP {K}K.
rewrite K scaleN1r /= in H.
move/esym/opp_self : H.
move: (mulmxr_crossmulr (vtvec u) (vtvec v) (ortho_of_iso_is_O f)).
rewrite K scaleN1r => /esym/eqP.
rewrite eqr_oppLR => /eqP -> /eqP.
rewrite oppr_eq0 mul_mx_rowfree_eq0; last first.
  apply/row_freeP.
  exists (ortho_of_iso f)^T.
  apply/eqP; by rewrite -orthogonalE ortho_of_iso_is_O.
move: uv0.
rewrite /colinear; by move/negbTE => ->.
Qed.

End derivative_map.

Notation "f '`*'" := (@dmap _ f _) (at level 5, format "f '`*'").

Section homogeneous_points_and_vectors.

Variable R : rcfType.

Definition hpoint := [qualify u : 'rV[R]_4 | u``_3%:R == 1].
Fact hpoint_key : pred_key hpoint. Proof. by []. Qed.
Canonical hpoint_keyed := KeyedQualifier hpoint_key.

Lemma hpointE p : (p \in hpoint) = (p``_3%:R == 1).
Proof. by []. Qed.

Definition hvector := [qualify u : 'rV[R]_4 | u``_3%:R == 0].
Fact hvector_key : pred_key hvector. Proof. by []. Qed.
Canonical hvector_keyed := KeyedQualifier hvector_key.

Lemma hvectorE p : (p \in hvector) = (p``_3%:R == 0).
Proof. by []. Qed.

Definition from_h (x : 'rV[R]_4) : 'rV[R]_3 := @lsubmx _ 1 3 1 x.

Definition to_hpoint (p : 'rV[R]_3) : 'rV[R]_4 := row_mx p 1.

Definition to_hvector (v : 'rV[R]_3) : 'rV[R]_4 := row_mx v 0.

Lemma to_hpointK p : from_h (to_hpoint p) = p.
Proof. by rewrite /from_h row_mxKl. Qed.

Lemma to_hvectorK v : from_h (to_hvector v) = v.
Proof. by rewrite /from_h row_mxKl. Qed.

Lemma from_hB (a b : 'rV[R]_4) : from_h (a - b) = from_h a - from_h b.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hE (x : 'rV[R]_4) : from_h x = \row_(i < 3) x 0 (inord i).
Proof.
apply/rowP => i; rewrite !mxE; congr (x 0 _).
apply val_inj => /=; by rewrite inordK // (ltn_trans (ltn_ord i)).
Qed.

Lemma rsubmx_coor3 (x : 'rV[R]_4) : @rsubmx _ 1 3 1 x = x``_3%:R%:M.
Proof.
apply/rowP => i; rewrite {i}(ord1 i) !mxE eqxx.
rewrite (_ : (rshift _ _) = 3%:R :> 'I_(3 + 1) ) //; by apply val_inj.
Qed.

Lemma hpoint_from_h p : (p \is hpoint) = (p == row_mx (from_h p) 1).
Proof.
rewrite hpointE -{2}(@hsubmxK _ 1 3 1 p) rsubmx_coor3.
apply/idP/idP => [/eqP -> // | /eqP/(@eq_row_mx _ 1 3 1) [_ /rowP/(_ ord0)]].
by rewrite !mxE eqxx /= => /eqP.
Qed.

Lemma to_hpointP p : to_hpoint p \in hpoint.
Proof. by rewrite hpoint_from_h to_hpointK. Qed.

Lemma hvector_from_h p : (p \is hvector) = (p == row_mx (from_h p) 0).
Proof.
rewrite hvectorE -{2}(@hsubmxK _ 1 3 1 p) rsubmx_coor3.
apply/idP/idP => [/eqP -> //| /eqP/(@eq_row_mx _ 1 3 1) [_ /rowP/(_ ord0)]].
by rewrite (_ : 0%:M = 0) //; apply/rowP => i; rewrite {i}(ord1 i) !mxE eqxx.
by rewrite !mxE eqxx /= => /eqP.
Qed.

Lemma to_hvectorP v : to_hvector v \in hvector.
Proof. by rewrite hvector_from_h to_hvectorK. Qed.

Lemma hpointB p q : p \in hpoint -> q \in hpoint -> p - q \in hvector.
Proof.
rewrite 2!hpoint_from_h hvector_from_h => /eqP Hp /eqP Hq.
by rewrite {1}Hp {1}Hq (opp_row_mx (from_h q)) (add_row_mx (from_h p)) subrr -from_hB.
Qed.

Lemma to_hpointB p q : to_hpoint p - to_hpoint q = to_hvector (p - q).
Proof. by rewrite /to_hpoint (opp_row_mx q) (add_row_mx p) subrr. Qed.

End homogeneous_points_and_vectors.

Notation "''hP[' R ]" := (hpoint R) (at level 8, format "''hP[' R ]").
Notation "''hV[' R ]" := (hvector R) (at level 8, format "''hV[' R ]").

Section SE3_def.

Variable R : rcfType.

Definition hom (r : 'M[R]_3) (t : 'rV[R]_3) : 'M[R]_4 :=
  block_mx r 0 t 1.

Definition rot_of_hom (M : 'M[R]_4) : 'M[R]_3 := @ulsubmx _ 3 1 3 1 M.

Definition SE3 := [qualify M : 'M[R]_4 |
  [&& rot_of_hom M \is 'SO[R]_3,
      @ursubmx _ 3 1 3 1 M == 0 &
      @drsubmx _ 3 1 3 1 M == 1%:M] ].
Fact SE3_key : pred_key SE3. Proof. by []. Qed.
Canonical SE3_keyed := KeyedQualifier SE3_key.

End SE3_def.

Notation "''SE3[' R ]" := (SE3 R)
  (at level 8, format "''SE3[' R ]") : ring_scope.

Section SE3_prop.

Variable R : rcfType.

Lemma rot_of_hom_SO (M : 'M[R]_4) : M \is 'SE3[R] ->
  rot_of_hom M \is 'SO[R]_3.
Proof. by case/and3P. Qed.

Lemma rot_of_hom_hom r t : rot_of_hom (hom r t) = r :> 'M[R]_3.
Proof. by rewrite /rot_of_hom /hom block_mxKul. Qed.

Lemma hom_is_SE r t : r \is 'SO[R]_3 -> hom r t \is 'SE3[R].
Proof.
move=> Hr; apply/and3P; rewrite rot_of_hom_hom Hr; split => //.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

Lemma rot_of_homN (M : 'M[R]_4) : rot_of_hom (- M) = - rot_of_hom M.
Proof. apply/matrixP => i j; by rewrite !mxE. Qed.

Definition trans_of_hom (M : 'M[R]_4) : 'rV[R]_3 := @dlsubmx _ 3 1 3 1 M.

Lemma trans_of_hom_hom r t : trans_of_hom (hom r t) = t.
Proof. by rewrite /trans_of_hom /hom block_mxKdl. Qed.

Lemma SE3E T : T \is 'SE3[R] -> T = hom (rot_of_hom T) (trans_of_hom T).
Proof.
move=> HT.
case/and3P : HT => T1 /eqP T2 /eqP T3.
by rewrite /hom -[in LHS](@submxK _ 3 1 3 1 T) T2 T3 /rot_of_hom /trans_of_hom.
Qed.

Lemma SE31 : 1 \is 'SE3[R].
Proof.
apply/and3P; split.
- rewrite /rot_of_hom (_ : ulsubmx _ = 1) ?rotation1 //.
  apply/matrixP => i j; by rewrite !mxE -val_eqE.
- apply/eqP/matrixP => i j; rewrite !mxE -val_eqE /= {j}(ord1 j) addn0.
  by case: i => -[] // [] // [].
- by apply/eqP/rowP => i; rewrite {i}(ord1 i) !mxE -val_eqE.
Qed.

Lemma det_hom (r : 'M[R]_3) t : \det (hom r t) = \det r.
Proof. by rewrite /hom (det_lblock r) det1 mulr1. Qed.

Lemma SE3_is_unitmx (M : 'M[R]_4) : M \is 'SE3[R] -> M \in unitmx.
Proof.
move=> HM.
by rewrite (SE3E HM) unitmxE /= det_hom rotation_det // ?unitr1 // ?rot_of_hom_SO.
Qed.

Lemma hom10 : hom 1 0 = 1 :> 'M[R]_4.
Proof.
rewrite /hom -[in RHS](@submxK _ 3 1 3 1 1).
congr (@block_mx _ 3 1 3 1); apply/matrixP => i j; rewrite !mxE -val_eqE //.
rewrite {j}(ord1 j) /= addn0; by case: i => -[] // [] // [].
rewrite {i}(ord1 i) /= addn0; by case: j => -[] // [] // [].
Qed.

Lemma homM r r' t t' : hom r t * hom r' t' = hom (r * r') (t *m r' + t') :> 'M[R]_4.
Proof.
rewrite /hom -mulmxE (mulmx_block r _ _ _ r') !(mulmx0,mul0mx,addr0,add0r,mulmx1).
by rewrite mulmxE mul1mx.
Qed.

Definition inv_hom (M : 'M[R]_4) :=
  hom (rot_of_hom M)^T (- trans_of_hom M *m (rot_of_hom M)^T).

Lemma trmx_hom (r : 'M[R]_3) t : (hom r t)^T = block_mx r^T t^T (0 : 'rV_3) 1.
Proof. by rewrite /hom (tr_block_mx r) trmx1 trmx0. Qed.

Lemma homV (T : 'M[R]_4) : T \is 'SE3[R] -> T * inv_hom T = 1.
Proof.
move=> HT.
rewrite (SE3E HT) /= /inv_hom rot_of_hom_hom trans_of_hom_hom.
rewrite homM -rotation_inv ?rot_of_hom_SO // divrr; last first.
  by apply/orthogonal_unit/rotation_sub/rot_of_hom_SO.
by rewrite mulNmx subrr hom10.
Qed.

Lemma Vhom (T : 'M[R]_4) : T \is 'SE3[R] -> inv_hom T * T = 1.
Proof.
move=> HT.
rewrite (SE3E HT) /= /inv_hom rot_of_hom_hom trans_of_hom_hom.
rewrite homM -rotation_inv ?rot_of_hom_SO // mulVr; last first.
  by apply/orthogonal_unit/rotation_sub/rot_of_hom_SO.
rewrite -mulmxA mulVmx ?mulmx1 1?addrC ?subrr ?hom10 // .
by rewrite unitmxE unitfE rotation_det ?oner_eq0 // rot_of_hom_SO.
Qed.

Lemma SE3_inv (M : 'M[R]_4) (HM : M \is 'SE3[R]) : M^-1 = inv_hom M.
Proof.
rewrite -[LHS]mul1mx -[X in X *m _ = _](Vhom HM) -mulmxA.
by rewrite mulmxV ?mulmx1 // SE3_is_unitmx.
Qed.

Lemma SE3_invr_closed : invr_closed 'SE3[R].
Proof.
move=> M HM.
rewrite SE3_inv //.
case/and3P : HM => M1 M2 M3.
apply/and3P; split.
- by rewrite /inv_hom rot_of_hom_hom rotationV.
- by rewrite /inv_hom /hom block_mxKur.
- by rewrite /inv_hom /hom block_mxKdr.
Qed.

Lemma SE3_mulr_closed : mulr_closed 'SE3[R].
Proof.
split; first exact: SE31.
move=> /= A B HA HB.
rewrite (SE3E HA) (SE3E HB) /= homM.
apply/and3P; split.
- rewrite /rot_of_hom /hom block_mxKul.
  case/and3P : HA; rewrite /rot_of_hom => HA _ _.
  case/and3P : HB; rewrite /rot_of_hom => HB _ _.
  by rewrite rpredM.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

Canonical SE3_is_mulr_closed := MulrPred SE3_mulr_closed.

Lemma SE3_divr_closed : divr_closed 'SE3[R].
Proof.
split; first by rewrite SE31.
move=> A B HA HB.
by rewrite rpredM // SE3_invr_closed.
Qed.

Canonical SE3_is_divr_closed := DivrPred SE3_divr_closed.

End SE3_prop.

Module SE.

Section se.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Record t : Type := mk {
  trans : 'rV[R]_3;
  rot : 'M[R]_3 ;
  rotP : rot \in 'SO[R]_3 }.

Coercion mx (T : t) := hom (rot T) (trans T).

Definition hrot (T : t) := hom (rot T) 0.

Definition htrans (T : t) := hom 1 (trans T).

Lemma tE (T : t) : T = hrot T *m htrans T :> 'M[R]_4.
Proof. by rewrite /mx /trans /rot mulmxE homM mulr1 mul0mx add0r. Qed.

Lemma mxSE_in_SE3 (T : t) : mx T \is 'SE3[R].
Proof.
rewrite /mx.
case: T => t r rSO /=; apply/and3P; split.
- by rewrite /rot_of_hom /hom block_mxKul.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

(* NB: not used *)
Definition inv (T : t) := hom (rot T)^T (- trans T *m (rot T)^T).

Lemma invV (T : t) : T *m inv T = 1.
Proof.
rewrite /mx /inv mulmxE homM -rotation_inv; last by case: T.
rewrite divrr; last by apply orthogonal_unit, rotation_sub; case: T.
by rewrite mulNmx subrr hom10.
Qed.

(* NB: not used, does not seem interesting *)
(*Definition inv_trans (T : t R) := hom 1 (- SE.trans T).
Lemma inv_transP (T : t R) : trans T *m inv_trans T = 1.
Proof.
by rewrite /trans /inv_trans mulmxE homM mulr1 trmx1 mulmx1 addrC subrr hom10.
Qed.*)

Definition hom_ap (T : t) x : 'rV[R]_4 := x *m T.

Lemma hom_ap_point (p : 'rV[R]_4) (T : t) : p \is 'hP[R] ->
  hom_ap T p = from_h p *m row_mx (rot T) 0 + row_mx (trans T) 1.
Proof.
rewrite hpoint_from_h => /eqP Hp.
rewrite /hom_ap /= /mx {1}Hp (mul_row_block (from_h p) 1 (rot T)).
by rewrite mulmx0 mulmx1 -add_row_mx mul1mx mul_mx_row mulmx0.
Qed.

Lemma hom_ap_vector (u : 'rV[R]_4) (T : t) : u \is 'hV[R] ->
  hom_ap T u = from_h u *m row_mx (rot T) 0.
Proof.
rewrite hvector_from_h => /eqP Hu.
rewrite /hom_ap /mx /= /hom {1}Hu (mul_row_block (from_h u) 0 (rot T)).
by rewrite mulmx0 mulmx1 -add_row_mx mul0mx mul_mx_row mulmx0 row_mx0 addr0.
Qed.

Lemma hom_apB p q (T : t) : p \is 'hP[R] -> q \is 'hP[R] ->
  hom_ap T p - hom_ap T q = hom_ap T (p - q).
Proof.
move=> Hu Hv.
rewrite hom_ap_point // hom_ap_point // opprD -addrCA -addrA subrr addr0 addrC.
by rewrite hom_ap_vector ?hpointB // from_hB mulmxBl.
Qed.

(* TODO: cannot be total anymore
Lemma linear_ap_hvect (T : t) : linear (ap_hvect T).
Proof. move=> k u v; rewrite 3!ap_hvectE mulmxDl scalemxAl. Qed.
*)

Definition ap_point T p := from_h (hom_ap T (to_hpoint p)).

Lemma ap_pointE u T : ap_point T u = from_h (u *m row_mx (rot T) 0 + row_mx (trans T) 1).
Proof. by rewrite /ap_point hom_ap_point ?to_hpointP // to_hpointK. Qed.

Definition ap_vector T v := from_h (hom_ap T (to_hvector v)).

Lemma ap_vectorE u (T : t) : ap_vector T u = u *m rot T.
Proof.
by rewrite /ap_vector hom_ap_vector ?to_hvectorP // to_hvectorK mul_mx_row mulmx0 to_hvectorK.
Qed.

Lemma ap_pointB u v (T : t) : ap_point T u - ap_point T v = ap_vector T (u - v).
Proof. by rewrite /ap_point -from_hB hom_apB ?to_hpointP // to_hpointB. Qed.

Lemma ap_vector_preserves_norm (T : t) : {mono (ap_vector T) : u / norm u}.
Proof.
move=> ?; rewrite ap_vectorE orth_preserves_norm // rotation_sub //; by case: T.
Qed.

Lemma rodrigues_homogeneous M u (HM : M \in 'SO[R]_3) :
  axis_of_rot M != 0 ->
  sin (angle_of_rot M) != 0 ->
  let a := aangle (angle_axis_of_rot M) in 
  let w := aaxis (angle_axis_of_rot M) in
  rodrigues u a w = ap_point (mk 0 HM) u.
Proof.
move=> axis0 sin0.
transitivity (u *m M); last first.
  (* TODO: lemma? *)
  by rewrite ap_pointE /= (mul_mx_row u) mulmx0 add_row_mx addr0 add0r to_hpointK.
have w1 : norm w = 1 by rewrite /w aaxis_of // norm_normalize.
rewrite rodriguesP //; congr (_ *m _) => {u}.
by rewrite (angle_axis_eskew HM).
Qed.

End se.

End SE.

Coercion hmx_coercion := SE.mx.

Section rigid_transformation_is_homogeneous_transformation.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Lemma direct_iso_is_SE (f : 'DIso_3[R]) :
  exists T : SE.t R, f =1 SE.ap_point T.
Proof.
case: f => /= f r1.
pose r := ortho_of_iso f.
have tf0 := trans_of_isoE f.
set t := trans_of_iso f in tf0.
have Hr : r \is 'SO[R]_3 by rewrite rotationE ortho_of_iso_is_O.
set T := SE.mk t Hr.
exists T => i.
rewrite SE.ap_pointE /=.
move: (trans_ortho_of_isoE f i); rewrite -/r -/t => /eqP.
rewrite eq_sym subr_eq => /eqP ->.
by rewrite mul_mx_row mulmx0 add_row_mx add0r to_hpointK.
Qed.

Lemma SE_preserves_length (T : SE.t R) :
  {mono (SE.ap_point T) : a b / norm (a - b)}.
Proof. move=> m0 m1; by rewrite SE.ap_pointB SE.ap_vector_preserves_norm. Qed.

(*Lemma SE_preserves_length (T : SE.t R) :
  f =1 SE.ap_point T -> {mono f : a b / norm (a - b)}.
Proof. move=> fT m0 m1; by rewrite 2!fT SE.ap_pointB SE.ap_vector_preserves_norm. Qed.*)

Lemma ortho_of_isoE (T : SE.t R) :
  ortho_of_iso (Iso.mk (SE_preserves_length T)) = SE.rot T.
Proof.
suff : forall x : 'rV[R]_3, x *m ortho_of_iso (Iso.mk (SE_preserves_length T)) = x *m SE.rot T.
  move=> Hx;   apply/eqP/mulmxP => u; by rewrite -Hx.
move=> x.
by rewrite trans_ortho_of_isoE /= trans_of_isoE /= SE.ap_pointB subr0 SE.ap_vectorE.
Qed.

Definition preserves_angle (f : point -> point) :=
  forall i j k, vec_angle (j - i) (k - i) =
                vec_angle (f j - f i) (f k - f i).

Lemma SE_preserves_angle (T : SE.t R) : preserves_angle (SE.ap_point T).
Proof.
move=> /= m0 m1 k.
rewrite 2!SE.ap_pointB 2!SE.ap_vectorE orth_preserves_vec_angle //.
by rewrite rotation_sub // SE.rotP.
Qed.

Lemma SE_preserves_orientation (T : SE.t R) :
  preserves_orientation (Iso.mk (SE_preserves_length T)).
Proof.
move=> p u v /=.
rewrite mulmxr_crossmulr ?ortho_of_iso_is_O // ortho_of_isoE.
rewrite rotation_det ?scale1r //; by case: T.
Qed.

End rigid_transformation_is_homogeneous_transformation.

Section plucker.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

(* equation of a line passing through two points p1 p2 *)
Definition line (p1 p2 : point) : pred point :=
  [pred p : point | colinear (p2 - p1) (p - p1)].

Definition coplanar (p1 p2 p3 p4 : point) : bool :=
  (p1 - p3) *d ((p2 - p1) *v (p4 - p3)) == 0.

Definition intersects (p1 p2 p3 p4 : point) :=
  coplanar p1 p2 p3 p3 && ~~ colinear (p2 - p1) (p4 - p3).
  
End plucker.

Local Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Local Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

(* TODO: in progress, [angeles] p.141-142 *)
Section open_chain.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := Tframe R (* NB: positive frame with an origin *).

Record joint := mkJoint {
  joint_axis : vector ;
  norm_joint_axis : norm joint_axis = 1 ;                  
  joint_angle : angle R (*  *) }.

Record link := mkLink {
  link_length : R ; (* a_i = distance Zi <-> Zi.+1 (mutually perpendicular segment) *)
  link_offset : R ; (* *)
  link_twist : angle R (*  *) }.

(* NB: link_offset, joint_angle, link_length, link_twist are called 
   Denavit-Hartenberg parameters *)

(* n + 1 links numberes 0,..., n (at least two links: the manipulator base and the end-effector)
   n + 1 frames numbered F_1, F_2, ..., F_n+1 (F_i attached to link i-1)
   n joints *)

Variable n' : nat.
Let n := n'.+1.

(* Zi is the axis of the ith joint *)
Definition Z_joint_axis (joints : joint ^ n) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := Ordinal (leq_trans (ltn_ord i) (leqnSn _))(* NB: i < n.+1 *) in 
  joint_axis (joints i) == tframek (frames i').

Definition X_Z (frames : frame ^ n.+1) (i : 'I_n.+1) : bool :=
  let predi := Ordinal (leq_ltn_trans (leq_pred _) (ltn_ord i)) (* NB: i-1 < n.+1 *) in 
  let: (o_predi, z_predi) := let f := frames predi in (torig f, tframek f) in
  let: (o_i, x_i, z_i) := let f := frames i in (torig f, tframei f, tframek f) in
  if intersects o_predi z_predi o_i z_i then
    x_i == z_predi *v z_i (* special case *)
  else if colinear z_predi z_i then
    o_predi \in line o_i (o_i + x_i) (* special case *)
  else
    x_i _|_ z_predi, z_i. (* common perpendicular to Zi-1 and Zi *)

Axiom distance_between_lines : point -> vector -> point -> vector -> R.

Definition link_length_prop (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := Ordinal (leq_trans (ltn_ord i) (leqnSn _)) (* i < n.+1 *) in
  let succi := Ordinal (leq_ltn_trans (ltn_ord i) (ltnSn _)) (* i.+1 < n.+1 *) in
  let: (o_i, z_i) := let f := frames i' in (torig f, tframek f) in 
  let: (o_succi, z_succi) := let f := frames succi in (torig f, tframek f) in 
  link_length (links i') = distance_between_lines o_i z_i o_succi z_succi.

(* TODO *)
Axiom intersection : point -> vector -> point -> vector -> point.

Definition link_offset_prop (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=  
  let i' := Ordinal (leq_trans (ltn_ord i) (leqnSn _)) (* i < n.+1 *) in
  let succi := Ordinal (leq_ltn_trans (ltn_ord i) (ltnSn _)) (* i.+1 < n.+1 *) in
  let: (o_succi, x_succi) := let f := frames succi in (torig f, tframei f) in 
  let: (o_i, x_i, z_i) := let f := frames i' in (torig f, tframei f, tframek f) in 
  let: o'_i := intersection o_i z_i o_succi x_succi in
  (norm (o'_i - o_i) == link_offset (links i')) &&
  (`| link_offset (links i') | == distance_between_lines o_i x_i o_succi x_succi).

(* TODO *)
Axiom angle_between_lines : point -> vector -> point -> vector -> vector (*direction*) -> angle R.

Definition link_twist_prop (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=  
  let i' := Ordinal (leq_trans (ltn_ord i) (leqnSn _)) (* i < n.+1 *) in
  let succi := Ordinal (leq_ltn_trans (ltn_ord i) (ltnSn _)) (* i.+1 < n.+1 *) in
  let: (o_succi, x_succi, z_succi) := let f := frames succi in (torig f, tframei f, tframek f) in 
  let: (o_i, z_i) := let f := frames i' in (torig f, tframek f) in 
  link_twist (links i') == angle_between_lines o_i z_i o_succi z_succi z_succi.

Definition joint_angle_prop (joints : joint ^ n) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := Ordinal (leq_trans (ltn_ord i) (leqnSn _)) (* i < n.+1 *) in
  let succi := Ordinal (leq_ltn_trans (ltn_ord i) (ltnSn _)) (* i.+1 < n.+1 *) in
  let: (o_succi, x_succi) := let f := frames succi in (torig f, tframei f) in 
  let: (o_i, x_i, z_i) := let f := frames i' in (torig f, tframei f, tframek f) in 
  joint_angle (joints i) = angle_between_lines o_i x_i o_succi x_succi z_i.

Record chain := mkChain {
  links : {ffun 'I_n.+1 -> link} ;
  frames : {ffun 'I_n.+1 -> frame} ;
  joints : {ffun 'I_n -> joint} ;
  (* the six conditions [angeles] p.141-142 *)
  _ : forall i : 'I_n, Z_joint_axis joints frames i ;
  _ : forall i : 'I_n.+1, X_Z frames i ;
  _ : forall i : 'I_n, link_length_prop links frames i ;
  _ : forall i : 'I_n, link_offset_prop links frames i ;
  _ : forall i : 'I_n, link_twist_prop links frames i ;
  _ : forall i : 'I_n, joint_angle_prop joints frames i }.
(* this leaves the frame n.+1 indefined (?) *)

(*Variable R : rcfType.
Let frame := frame R.

Record joint := mkJoint {
  offset : R ;
  joint_angle : angle R }.

Record link := mkLink {
  length : R ;
  link_angle : angle R }.

Variable n' : nat.
Let n := n'.+1.
Variables chain : {ffun 'I_n -> frame * link * joint}.
Definition frames := fun i => (chain (insubd ord0 i)).1.1.
Definition links := fun i => (chain (insubd ord0 i)).1.2.
Definition joints := fun i => (chain (insubd ord0 i)).2.

Local Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Local Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Definition common_normal_xz (i : 'I_n) :=
  (framej (frames i.-1)) _|_ (framek (frames i)), (framei (frames i.-1)).
 *)

End open_chain.

(*
  option ('rV[R]_3 (* point *) * 'rV[R]_3 (* vec *) ).
Admitted.

Definition intersection (o o' : 'rV[R]_3) (v v' : 'rV[R]_3) : option 'rV[R]_3.
Admitted.

Definition length_prop (i : 'I_n) (f f' : frame) :
  unique_common_orthogonal (origin f) (origin f') ()
  length (links i) = `| |

Definition z_vec (i : 'I_n) := zframes i

joint i is located between links i-1 and i
z_vec (frames i) "is located along the axis of joint i"

the zi axis along the axis of joint i

Definition before_after_joint (i : 'I_n) : option (link * link):=
  match ltnP O i with
    | LtnNotGeq H (* 0 < i*) => Some (links i.-1, links i)
    | GeqNotLtn H (* i <= 0*) => None
  end.

link length and twist along and about the x_i-1 axis

Hypothesis :

Check forall i, (z_ax (basis (frames i))).

x_vec (frames i.-1) _|_ plane (z_vec (frames i.-1)),(z_vec (frames i))

length (links i) = distance from (z_vec (frames i.-1)) to (z_vec (frames i)) along (x_vec)
 *)
