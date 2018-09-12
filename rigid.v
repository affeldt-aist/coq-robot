(* coq-robot (c) 2017 AIST and INRIA. License: LGPL v3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg ssrint div.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

Require Import ssr_ext angle euclidean3 skew vec_angle rot frame.

(*
 OUTLINE:
 1. Section central_isometry_n.
 2. Section central_isometry_3.
 3. Section isometry_3_properties.
 4. Section direct_isometry_3_properties.
 5. section derivative_map
     definition of what it means to preserve the cross-product by a transformation
     (sample lemma: preservation of the cross-product by derivative maps)
 6. Section homogeneous_points_and_vectors
 7. Section homogeneous_matrices.
 8. Section SE3_qualifier.
 9. Section SE3_hom.
    lemmas about the homogeneous representation of SE3
 10. Section Adjoint.
     adjoint transformation associated with an homogeneous matrix
 11. Module EuclideanMotion.
     definition of Euclidean motions as a record
 12. Section coordinate_transformation.
 13. section rigid_transformation_is_homogeneous_transformation
     a direct isometry (i.e., cross-product preserving) can be expressed
     as an Euclidean motion
*)

Reserved Notation "''Iso[' T ]_ n"
  (at level 8, n at level 2, format "''Iso[' T ]_ n").
Reserved Notation "''CIso[' T ]_ n"
  (at level 8, n at level 2, format "''CIso[' T ]_ n").
Reserved Notation "''DIso_3[' T ]" (at level 8, format "''DIso_3[' T ]").
Reserved Notation "''SE3[' T ]" (at level 8, format "''SE3[' T ]").
Reserved Notation "f '`*'" (at level 5, format "f `*").
Reserved Notation "''hP[' T ]" (at level 8, format "''hP[' T ]").
Reserved Notation "''hV[' T ]" (at level 8, format "''hV[' T ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Module Iso.
Section isometry.
Variables (T : rcfType) (n : nat).
Record t := mk {
  f :> 'rV[T]_n -> 'rV[T]_n ;
  P : {mono f : a b / norm (a - b)} }.
End isometry.
End Iso.

Notation "''Iso[' T ]_ n" := (Iso.t T n).
Definition isometry_coercion := Iso.f.
Coercion isometry_coercion : Iso.t >-> Funclass.

Module CIso.
Section central_isometry.
Variable (T : rcfType) (n : nat).
Record t := mk {
  f : 'Iso[T]_n ;
  P : f 0 = 0 }.
End central_isometry.
End CIso.

Notation "''CIso[' T ]_ n" := (CIso.t T n).
Definition cisometry_coercion := CIso.f.
Coercion cisometry_coercion : CIso.t >-> Iso.t.

Section central_isometry_n.

Variable (T : rcfType) (n : nat).
Implicit Types  f : 'CIso[T]_n.

Lemma central_isometry_preserves_norm f : {mono f : x / norm x}.
Proof. by case: f => f f0 p; rewrite -(subr0 (f p)) -f0 Iso.P subr0. Qed.

(* [oneill] first part of lemma 1.6, p.100 *)
Lemma central_isometry_preserves_dotmul f : {mono f : u v / u *d v}.
Proof.
case: f => f f0 a b.
have /eqP : norm (f a - f b) = norm (a - b) by rewrite (Iso.P f).
rewrite /norm eqr_sqrt ?le0dotmul // !dotmulDl !dotmulDr !dotmulvv !normN.
rewrite !(central_isometry_preserves_norm (CIso.mk f0)) !addrA.
rewrite 2!(addrC _ (norm b ^+ 2)) => /eqP/addrI.
rewrite -2!addrA => /addrI.
rewrite -(dotmulC (f a)) dotmulvN -(dotmulC a) dotmulvN -2!mulr2n => /eqP.
rewrite -mulr_natr -[in X in _ == X -> _]mulr_natr 2!mulNr eqr_opp.
by move/eqP/mulIr => -> //; rewrite unitfE pnatr_eq0.
Qed.

End central_isometry_n.

Section central_isometry_3.

Variable T : rcfType.
Implicit Types f : 'CIso[T]_3.

Local Open Scope frame_scope.

Definition frame_central_iso f (p : noframe T) : noframe T.
apply: (@NOFrame.mk _ (col_mx3 (f (p|,0)) (f (p|,1)) (f (p|,2%:R)))).
apply/orthogonal3P.
by rewrite !rowK /= 3!central_isometry_preserves_norm 3!noframe_norm
  3!central_isometry_preserves_dotmul idotj noframe_idotk jdotk !eqxx.
Defined.

(* [oneill] second part of lemma 1.6, p.101 *)
Lemma central_isometry_is_linear f : linear f.
Proof.
move=> k /= a b.
have Hp : forall p,
  f p = p``_0 *: f 'e_0 + p``_1 *: f 'e_1 + p``_2%:R *: f 'e_2%:R.
  move=> p.
  have -> : f p = f p *d f 'e_0 *: f 'e_0 +
                  f p *d f 'e_1 *: f 'e_1 +
                  f p *d f 'e_2%:R *: f 'e_2%:R.
    move: (orthogonal_expansion (frame_central_iso f (can_noframe T)) (f p)).
    by rewrite !rowframeE !rowK /= !rowframeE /= !row1.
  by rewrite 3!central_isometry_preserves_dotmul // 3!coorE.
rewrite Hp (Hp a) (Hp b) !mxE /= !(scalerDl, scalerDr).
rewrite !scalerA -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrC -!addrA.
Qed.

End central_isometry_3.

Section isometry_3_properties.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Let point := 'rV[T]_3.
Implicit Types f : 'Iso[T]_3.

(* [oneill] theorem 1.7, p.101 *)
(** every isometry of E^3 can be uniquely described as an orthogonal
    transformation followed by a translation *)
Lemma trans_ortho_of_iso f :
  { trans : 'rV[T]_3 & { rot : 'M[T]_3 |
    (forall x : 'rV[T]_3, f x == x *m rot + trans) /\
    rot \is 'O[T]_3 /\
    trans = f 0 } }.
Proof.
set m := f 0.
set Tm1f := fun x => f x - m.
have Tm1f_is_iso : {mono Tm1f : a b / norm (a - b)}.
  move=> ? ?; by rewrite /Tm1f -addrA opprB 2!addrA subrK (Iso.P f).
have Tm1f0 : Tm1f 0 = 0 by rewrite /Tm1f subrr.
set c := @CIso.mk _ _ (Iso.mk Tm1f_is_iso) Tm1f0.
have /= linearTm1f := central_isometry_is_linear c.
have /= orthogonalTm1f := central_isometry_preserves_dotmul c.
exists m.
case: (lin1_mx' linearTm1f) => g Hg.
exists (lin1_mx g); split; last first.
  split; last by [].
  apply/orth_preserves_dotmul => u v /=.
  by rewrite 2!mul_rV_lin1 -[in RHS]orthogonalTm1f 2!Hg.
move=> u; by rewrite mul_rV_lin1 -Hg subrK.
Qed.

Definition ortho_of_iso f : 'M[T]_3 := projT1 (projT2 (trans_ortho_of_iso f)).

Definition trans_of_iso f : 'rV[T]_3 := projT1 (trans_ortho_of_iso f).

Lemma trans_of_isoE f : trans_of_iso f = f 0.
Proof.
rewrite /trans_of_iso; by case: (trans_ortho_of_iso _) => ? [C [H1 [H2 H3]]].
Qed.

Lemma ortho_of_iso_is_O f : ortho_of_iso f \is 'O[T]_3.
Proof.
rewrite /ortho_of_iso; by case: (trans_ortho_of_iso _) => ? [C [H1 [H2 H3]]].
Qed.

Lemma trans_ortho_of_isoE f u : u *m ortho_of_iso f = f u - trans_of_iso f.
Proof.
rewrite /ortho_of_iso /trans_of_iso.
case: (trans_ortho_of_iso _) => ? [C [H1 [H2 H3]]] /=.
move: (H1 u) => /eqP ->; by rewrite addrK.
Qed.

Lemma ortho_of_iso_eq f1 f2 : (forall i, Iso.f f1 i = Iso.f f2 i) ->
  ortho_of_iso f1 = ortho_of_iso f2.
Proof.
move=> f12.
apply/eqP/mulmxP => u.
rewrite 2!trans_ortho_of_isoE /= 2!trans_of_isoE /=.
case: f1 f2 f12 => [f1 Hf1] [f2 Hf2] /= f12; by rewrite !f12.
Qed.

Definition iso_sgn f : T := \det (ortho_of_iso f).

Lemma img_vec_iso f (a b : point) :
  f b - f a = (b - a) *m ortho_of_iso f.
Proof.
move/esym/eqP: (trans_ortho_of_isoE f a).
move/esym/eqP: (trans_ortho_of_isoE f b).
rewrite mulmxBl => /eqP <- /eqP <-; by rewrite opprB addrA subrK.
Qed.

Definition displacement f p : vector := f p - p.

Definition relative_displacement f (p a : point) :=
  (p - a) *m (ortho_of_iso f - 1).

(* NB: caused only by rotation *)
Lemma displacement_iso f p a :
  displacement f p = displacement f a + relative_displacement f p a.
Proof.
rewrite /relative_displacement mulmxBr mulmx1 opprB addrA -(addrC a) 2!addrA.
rewrite subrK; congr (_ - _).
apply/eqP; by rewrite addrC -subr_eq img_vec_iso.
Qed.

End isometry_3_properties.

Module DIso.
Section direct_isometry.
Variable (T : rcfType).
Record t := mk {
  f :> 'Iso[T]_3 ;
  P : iso_sgn f == 1 }.
End direct_isometry.
End DIso.

Notation "''DIso_3[' T ]" := (DIso.t T).
Definition disometry_coercion := DIso.f.
Coercion disometry_coercion : DIso.t >-> Iso.t.

Section direct_isometry_3_properties.

Variable T : rcfType.

Lemma ortho_of_diso_is_SO (f : 'DIso_3[T]) : ortho_of_iso f \is 'SO[T]_3.
Proof.
case: f => f; rewrite /iso_sgn => Hf /=; by rewrite rotationE (ortho_of_iso_is_O f).
Qed.

End direct_isometry_3_properties.

Section derivative_map.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Implicit Types f : 'Iso[T]_3.

(* [oneill] theorem 2.1, p. 104 *)
Definition dmap f (v : vector) : vector :=
  let C := ortho_of_iso f in
  (v *m C).

Local Notation "f '`*'" := (@dmap f).

Lemma dmap0 f : f `* 0 = 0.
Proof. by rewrite /dmap /= mul0mx. Qed.

Lemma dmapE f (u : vector) b a :
  u = b - a :> vector ->
  f `* u = f b - f a :> vector.
Proof. move=> uab; by rewrite /dmap /= uab img_vec_iso. Qed.

Lemma derivative_map_preserves_length f :
  {mono (fun x : vector => f`* x) : u v / norm (u - v)}.
Proof.
move=> u v; rewrite /dmap /= -(mulmxBl u v (ortho_of_iso f)).
by rewrite orth_preserves_norm // ortho_of_iso_is_O.
Qed.

Local Open Scope frame_scope.

(* [oneill] lemma 3.2, p.108 *)
Lemma dmap_iso_sgnP (F : tframe T) f :
  let e1 := F|,0 in
  let e2 := F|,1 in
  let e3 := F|,2%:R in
  f`* e1 *d (f `* e2 *v f`* e3) =
  iso_sgn f * (e1 *d (e2 *v e3)).
Proof.
move=> e1 e2 e3.
move: (orthogonal_expansion (can_noframe T) e1).
rewrite !rowframeE !row1.
set a11 := _ *d 'e_0. set a12 := _ *d 'e_1. set a13 := _ *d 'e_2%:R => He1.
move: (orthogonal_expansion (can_noframe T) e2).
rewrite !rowframeE !row1.
set a21 := _ *d 'e_0. set a22 := _ *d 'e_1. set a23 := _ *d 'e_2%:R => He2.
move: (orthogonal_expansion (can_noframe T) e3).
rewrite !rowframeE !row1.
set a31 := _ *d 'e_0. set a32 := _ *d 'e_1. set a33 := _ *d 'e_2%:R => He3.
have e1a : e1 = row3 a11 a12 a13.
  by rewrite (row3_proj e1) !row3D !(add0r,addr0) !coorE.
have e2a : e2 = row3 a21 a22 a23.
  by rewrite (row3_proj e2) !row3D !(add0r,addr0) !coorE.
have e3a : e3 = row3 a31 a32 a33.
  by rewrite (row3_proj e3) !row3D !(add0r,addr0) !coorE.
transitivity (\det ((ortho_of_iso f)^T *m
  (col_mx3 (row3 a11 a12 a13) (row3 a21 a22 a23) (row3 a31 a32 a33))^T)).
  rewrite /= -det_tr trmx_mul trmxK mulmx_col3.
  by rewrite -crossmul_triple -e1a -e2a -e3a trmxK.
rewrite det_mulmx det_tr; congr (_ * _).
rewrite det_tr -crossmul_triple; by congr (_ *d (_ *v _)).
Qed.

(* [oneill] theorem 3.6, p.110 *)
Lemma dmap_preserves_crossmul (u v : vector) f :
  f`* (u *v v) =
    iso_sgn f *: (f`* u *v f`* v) :> vector.
Proof.
set tf := TFrame.trans (can_tframe T) 0.
set u1p := tf|,0. set u2p := tf|,1. set u3p := tf|,2%:R.
move: (orthogonal_expansion tf u).
rewrite !rowframeE !row1.
set u1 := _ *d 'e_0. set u2 := _ *d 'e_1. set u3 := _ *d 'e_2%:R => Hu.
move: (orthogonal_expansion tf v).
rewrite !rowframeE !row1.
set v1 := _ *d 'e_0. set v2 := _ *d 'e_1. set v3 := _ *d 'e_2%:R => Hv.
set e1 := f`* u1p. set e2 := f`* u2p. set e3 := f`* u3p.
have Ku : f`* u = u1 *: e1 + u2 *: e2 + u3 *: e3 :> vector.
  rewrite [in LHS]/= Hu /dmap !mulmxDl.
  rewrite !scalemxAl [in RHS]/=.
  rewrite /u1p /u2p /u3p.
  by rewrite 3!rowframeE 3!rowE !mulmx1.
have Kv : f`* v = v1 *: e1 + v2 *: e2 + v3 *: e3 :> vector.
  rewrite [in LHS]/= Hv /dmap !mulmxDl.
  rewrite !scalemxAl [in RHS]/=.
  rewrite /u1p /u2p /u3p.
  by rewrite 3!rowframeE 3!rowE !mulmx1.
have @f' : noframe T.
apply (@NOFrame.mk _ (col_mx3 e1 e2 e3)).
  apply/orthogonal3P; rewrite !rowK /=.
  do 3! rewrite orth_preserves_norm ?ortho_of_iso_is_O //.
  rewrite /u1p /u2p /u3p.
  rewrite !rowframeE !rowE !mulmx1 3!normeE !eqxx /=.
  rewrite !(proj2 (orth_preserves_dotmul _)) ?ortho_of_iso_is_O //.
  rewrite /u1p /u2p /u3p.
  by rewrite !rowframeE /= !rowE ?mulmx1 !dote2 //= eqxx.
have -> : iso_sgn f = noframe_sgn f'.
  (* TODO: move as a lemma? *)
  rewrite noframe_sgnE.
  have -> : f'|,0 = f`* u1p by rewrite rowframeE rowK.
  have -> : f'|,1 = f`* u2p by rewrite rowframeE rowK.
  have -> : f'|,2%:R = f`* u3p by rewrite rowframeE rowK.
  by rewrite dmap_iso_sgnP /= !rowframeE !rowE !mulmx1 vecjk dote2 mulr1.
have : (((f`* u) *v (f`* v))) =
         noframe_sgn f' *: (f`* (u *v v)) :> vector.
  rewrite /=.
  rewrite (@crossmul_noframe_sgn _ f' (f`* u) u1 u2 u3 (f`* v) v1 v2 v3) //; last 2 first.
    move: Ku.
    by rewrite !rowframeE /= !rowK /=.
    move: Kv.
    by rewrite /= !rowframeE !rowK /=.
  rewrite /=.
  congr (_ *: _).
  rewrite !rowframeE !rowK /= Hu Hv.
  do 2 rewrite linearD [in RHS]/=.
  rewrite /dmap.
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
    rewrite linearZ /=.
    by rewrite vecij.
  rewrite (_ : 'e_0 *v (u3 *: _) = - u3 *: 'e_1); last first.
    rewrite linearZ /=.
    rewrite vecik.
    by rewrite scalerN scaleNr.
  rewrite add0r.
  rewrite mulNmx -[in RHS]scalemxAl [in RHS]mulmxDl.
  rewrite -![in RHS]scalemxAl.
  rewrite [in RHS]scalerDr.
  rewrite opprD.
  rewrite crossmulC [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite scaleNr scalerN opprK.
  rewrite (_ : _ *v _ = - u1 *: 'e_2%:R); last first.
    rewrite linearZ /= crossmulC.
    rewrite vecij.
    by rewrite scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite addr0.
  rewrite (_ : _ *v _ = u3 *: 'e_0); last first.
    by rewrite linearZ /= vecjk.
  rewrite scaleNr opprK mulmxBl.
  rewrite -![in RHS]scalemxAl.
  rewrite scalerDr scalerN.
  rewrite crossmulC [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite (_ : _ *v _ = u1 *: 'e_1); last first.
    rewrite linearZ /= crossmulC.
    by rewrite vecik opprK.
  rewrite (_ : _ *v _ = - u2 *: 'e_0); last first.
    rewrite linearZ /= crossmulC.
    by rewrite vecjk scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite subr0 scaleNr opprK mulmxDl mulNmx.
  rewrite -![in RHS]scalemxAl.
  rewrite -![in RHS]addrA [in RHS]addrC -[in RHS]addrA [in RHS]addrCA -[in RHS]addrA [in RHS]addrC.
  rewrite ![in RHS]addrA -[in RHS]addrA.
  congr (_ + _); last first.
    rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u1).
    by rewrite /e3 /dmap /u3p rowframeE rowE mulmx1.
  rewrite scalerDr.
  rewrite -![in RHS]addrA [in RHS]addrCA [in RHS]addrC ![in RHS]addrA -addrA; congr (_ + _).
    rewrite /e1 /dmap /u1p.
    rewrite rowframeE rowE mulmx1.
    by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u2).
  rewrite /e2 /dmap /u2p.
  rewrite rowframeE rowE mulmx1.
  by rewrite scalerN !scalerA -scalerBl -scaleNr opprB mulrC (mulrC u1).
move=> ->; by rewrite scalerA -expr2 /iso_sgn -sqr_normr abs_noframe_sgn expr1n scale1r.
Qed.

Definition preserves_orientation f :=
  forall (u v : vector),
  f`* (u *v v) = ((f`* u) *v (f`* v))
  :> vector.

Lemma preserves_crossmul_is_diso f (u v : vector) :
  ~~ colinear u v ->
  f`* (u *v v) = (f`* u) *v (f`* v) :> vector ->
  iso_sgn f = 1.
Proof.
move=> uv0.
rewrite dmap_preserves_crossmul => H.
move: (orthogonal_det (ortho_of_iso_is_O f)).
rewrite -/(iso_sgn _).
case: (lerP 0 (iso_sgn f)) => K; first by rewrite ger0_norm.
rewrite ltr0_norm // => /eqP.
rewrite eqr_oppLR => /eqP {K}K.
exfalso.
move: H.
rewrite K scaleN1r => /eqP; rewrite Neqxx_mat.
move: (mulmxr_crossmulr u v (ortho_of_iso_is_O f)).
rewrite -/(iso_sgn f) K scaleN1r => /esym/eqP.
rewrite eqr_oppLR => /eqP ->.
rewrite oppr_eq0 mul_mx_rowfree_eq0; last first.
  apply/row_freeP.
  exists (ortho_of_iso f)^T.
  apply/eqP; by rewrite -orthogonalE ortho_of_iso_is_O.
move: uv0.
rewrite /colinear; by move/negbTE => ->.
Qed.

Lemma diso_preserves_orientation (df : 'DIso_3[T]) : preserves_orientation df.
Proof. move=> u v; by rewrite dmap_preserves_crossmul (eqP (DIso.P df)) scale1r. Qed.

End derivative_map.

Section homogeneous_points_and_vectors.

Variable T : rcfType.
Let point := 'rV[T]_3.
Let vector := 'rV[T]_3.
Let homogeneous := 'rV[T]_4.

Lemma rsubmx_coor3 (x : homogeneous) : @rsubmx _ 1 3 1 x = x``_3%:R%:M.
Proof.
apply/rowP => i; rewrite {i}(ord1 i) !mxE eqxx.
rewrite (_ : (rshift _ _) = 3%:R :> 'I_(3 + 1) ) //; by apply val_inj.
Qed.

Definition from_h (x : homogeneous) : 'rV[T]_3 := @lsubmx _ 1 3 1 x.

Lemma from_hD (x y : homogeneous) : from_h (x + y) = from_h x + from_h y.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hZ k (x : homogeneous) : from_h (k *: x) = k *: from_h x.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hB (x y : homogeneous) : from_h (x - y) = from_h x - from_h y.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hE (x : homogeneous) : from_h x = \row_(i < 3) x 0 (inord i).
Proof.
apply/rowP => i; rewrite !mxE; congr (x 0 _).
apply val_inj => /=; by rewrite inordK // (ltn_trans (ltn_ord i)).
Qed.

Definition hpoint := [qualify x : homogeneous | x``_3%:R == 1].
Fact hpoint_key : pred_key hpoint. Proof. by []. Qed.
Canonical hpoint_keyed := KeyedQualifier hpoint_key.

Lemma hpointE (x : homogeneous) : (x \is hpoint) = (x``_3%:R == 1).
Proof. by []. Qed.

Definition to_hpoint (p : point) : homogeneous := row_mx p 1.

Lemma to_hpointK (p : point) : from_h (to_hpoint p) = p.
Proof. by rewrite /from_h row_mxKl. Qed.

Lemma hpoint_from_h x : (x \is hpoint) = (x == row_mx (from_h x) 1).
Proof.
rewrite hpointE -{2}(@hsubmxK _ 1 3 1 x) rsubmx_coor3.
apply/idP/idP => [/eqP -> // | /eqP/(@eq_row_mx _ 1 3 1) [_ /rowP/(_ ord0)]].
by rewrite !mxE eqxx /= => /eqP.
Qed.

Lemma to_hpointP (p : point) : to_hpoint p \is hpoint.
Proof. by rewrite hpoint_from_h to_hpointK. Qed.

Definition hvector := [qualify x : homogeneous | x``_3%:R == 0].
Fact hvector_key : pred_key hvector. Proof. by []. Qed.
Canonical hvector_keyed := KeyedQualifier hvector_key.

Lemma hvectorE (x : homogeneous) : (x \is hvector) = (x``_3%:R == 0).
Proof. by []. Qed.

Definition to_hvector (v : vector) : homogeneous := row_mx v 0.

Lemma to_hvectorK (v : vector) : from_h (to_hvector v) = v.
Proof. by rewrite /from_h row_mxKl. Qed.

Lemma hvector_from_h (x : homogeneous) : (x \is hvector) = (x == row_mx (from_h x) 0).
Proof.
rewrite hvectorE -{2}(@hsubmxK _ 1 3 1 x) rsubmx_coor3.
apply/idP/idP => [/eqP -> //| /eqP/(@eq_row_mx _ 1 3 1) [_ /rowP/(_ ord0)]].
by rewrite (_ : 0%:M = 0) //; apply/rowP => i; rewrite {i}(ord1 i) !mxE eqxx.
by rewrite !mxE eqxx /= => /eqP.
Qed.

Lemma to_hvectorP (v : vector) : to_hvector v \is hvector.
Proof. by rewrite hvector_from_h to_hvectorK. Qed.

Lemma hpointB (x y : homogeneous) : x \is hpoint -> y \is hpoint -> x - y \is hvector.
Proof.
rewrite 2!hpoint_from_h hvector_from_h => /eqP Hp /eqP Hq.
by rewrite {1}Hp {1}Hq (opp_row_mx (from_h y)) (add_row_mx (from_h x)) subrr -from_hB.
Qed.

Lemma to_hpointB (p q : point) : to_hpoint p - to_hpoint q = to_hvector (p - q).
Proof. by rewrite /to_hpoint (opp_row_mx q) (add_row_mx p) subrr. Qed.

End homogeneous_points_and_vectors.

Notation "''hP[' T ]" := (hpoint T).
Notation "''hV[' T ]" := (hvector T).

Section homogeneous_matrices.

Variable T : rcfType.
Let homogeneous := 'M[T]_4.
Implicit Types M : homogeneous.
Implicit Types r : 'M[T]_3.

Definition hom r (v : 'rV[T]_3) : homogeneous := block_mx r 0 v 1.

Definition rot_of_hom M : 'M[T]_3 := @ulsubmx _ 3 1 3 1 M.

Definition trans_of_hom M : 'rV[T]_3 := @dlsubmx _ 3 1 3 1 M.

Lemma hom10 : hom 1 0 = 1 :> homogeneous.
Proof.
rewrite /hom -[in RHS](@submxK _ 3 1 3 1 1).
congr (@block_mx _ 3 1 3 1); apply/matrixP => i j; rewrite !mxE -val_eqE //.
rewrite {j}(ord1 j) /= addn0; by case: i => -[] // [] // [].
rewrite {i}(ord1 i) /= addn0; by case: j => -[] // [] // [].
Qed.

Lemma det_hom r t : \det (hom r t) = \det r.
Proof. by rewrite /hom (det_lblock r) det1 mulr1. Qed.

Lemma rot_of_hom_hom t r : rot_of_hom (hom r t) = r.
Proof. by rewrite /rot_of_hom /hom block_mxKul. Qed.

Lemma rot_of_hom1 : rot_of_hom 1 = 1 :> 'M[T]__.
Proof. by rewrite -hom10 rot_of_hom_hom. Qed.

Lemma rot_of_homN M : rot_of_hom (- M) = - rot_of_hom M.
Proof. apply/matrixP => i j; by rewrite !mxE. Qed.

Lemma tr_rot_of_hom M : (rot_of_hom M)^T = rot_of_hom M^T.
Proof. by rewrite /rot_of_hom trmx_ulsub. Qed.

Lemma trans_of_hom_hom r t : trans_of_hom (hom r t) = t.
Proof. by rewrite /trans_of_hom /hom block_mxKdl. Qed.

Lemma trans_of_hom1 : trans_of_hom 1 = 0 :> 'rV[T]__.
Proof. by rewrite -hom10 trans_of_hom_hom. Qed.

Lemma homM r r' t t' : hom r t * hom r' t' = hom (r * r') (t *m r' + t').
Proof.
rewrite /hom -mulmxE (mulmx_block r _ _ _ r').
by rewrite !(mulmx0,mul0mx,addr0,add0r,mulmx1) mulmxE mul1mx.
Qed.

Definition inv_hom M := hom (rot_of_hom M)^T (- trans_of_hom M *m (rot_of_hom M)^T).

Lemma trmx_hom (r : 'M[T]_3) t : (hom r t)^T = block_mx r^T t^T 0 1.
Proof. by rewrite /hom (tr_block_mx r) trmx1 trmx0. Qed.

(* elementary rotations in homogeneous form *)
Definition hRx a : homogeneous := hom (Rx a) 0.

Lemma hRx_correct a (p : 'rV[T]_3) : from_h ((to_hpoint p) *m hRx a) = p *m Rx a.
Proof.
rewrite {1}/to_hpoint /hRx /hom (mul_row_block p 1 (Rx a)).
by rewrite !(mulmx0,addr0,add0r,mulmx1) -/(to_hpoint (p *m Rx a)) to_hpointK.
Qed.

Definition hRz a : homogeneous := hom (Rz a) 0.
Definition hRy a : homogeneous := hom (Ry a) 0.

(* elementary translations in homogeneous form *)
Definition hTx d : homogeneous := hom 1 (row3 d 0 0).
Definition hTy d : homogeneous := hom 1 (row3 0 d 0).
Definition hTz d : homogeneous := hom 1 (row3 0 0 d).

Lemma hTxRz (d : T) (a : angle T) :
  hTx d * hRz a = hom (Rz a) (row3 (d * cos a) (d * sin a) 0).
Proof.
by rewrite homM mul1r addr0 mulmx_row3_col3 2!scale0r !addr0 row3Z mulr0.
Qed.

Lemma hTzRz (d : T) (a : angle T) : hTz d * hRz a = hom (Rz a) (row3 0 0 d).
Proof.
rewrite homM mul1r mulmx_row3_col3 2!scale0r !(add0r,addr0) e2row row3Z.
by rewrite !(mulr0,mulr1).
Qed.

End homogeneous_matrices.

Section SE3_qualifier.
Variable T : rcfType.
Implicit Types M : 'M[T]_4.
Definition SE3 := [qualify M |
  [&& rot_of_hom M \is 'SO[T]_3,
      @ursubmx _ 3 1 3 1 M == 0 &
      @drsubmx _ 3 1 3 1 M == 1%:M] ].
Fact SE3_key : pred_key SE3. Proof. by []. Qed.
Canonical SE3_keyed := KeyedQualifier SE3_key.
End SE3_qualifier.
Notation "''SE3[' T ]" := (SE3 T) : ring_scope.

Section SE3_hom.

Variable T : rcfType.

Lemma rot_of_hom_is_SO M : M \is 'SE3[T] -> rot_of_hom M \is 'SO[T]_3.
Proof. by case/and3P. Qed.

Lemma hom_is_SE r t : r \is 'SO[T]_3 -> hom r t \is 'SE3[T].
Proof.
move=> Hr; apply/and3P; rewrite rot_of_hom_hom Hr; split => //.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

Lemma SE3E M : M \is 'SE3[T] -> M = hom (rot_of_hom M) (trans_of_hom M).
Proof.
case/and3P => T1 /eqP T2 /eqP T3.
by rewrite /hom -[in LHS](@submxK _ 3 1 3 1 M) T2 T3.
Qed.

Lemma SE31 : 1 \is 'SE3[T].
Proof.
apply/and3P; split; first by rewrite rot_of_hom1 rotation1.
- apply/eqP/matrixP => i j; rewrite !mxE -val_eqE /= {j}(ord1 j) addn0.
  by case: i => -[] // [] // [].
- by apply/eqP/rowP => i; rewrite {i}(ord1 i) !mxE -val_eqE.
Qed.

Lemma SE3_in_unitmx M : M \is 'SE3[T] -> M \in unitmx.
Proof.
move=> H; rewrite (SE3E H).
by rewrite unitmxE /= det_hom rotation_det // ?unitr1 // rot_of_hom_is_SO.
Qed.

Lemma rot_of_homM M1 M2 : M1 \is 'SE3[T] -> M2 \is 'SE3[T] ->
  rot_of_hom (M1 * M2) = rot_of_hom M1 * rot_of_hom M2.
Proof. move/SE3E => -> /SE3E ->; by rewrite homM !rot_of_hom_hom. Qed.

Lemma trans_of_homM M1 M2 : M1 \is 'SE3[T] -> M2 \is 'SE3[T] ->
  trans_of_hom (M1 * M2) = trans_of_hom M1 *m rot_of_hom M2 + trans_of_hom M2.
Proof.
move/SE3E => -> /SE3E tmp; rewrite [in LHS]tmp; by rewrite homM 2!trans_of_hom_hom.
Qed.

Lemma homV M : M \is 'SE3[T] -> M * inv_hom M = 1.
Proof.
move=> HM.
rewrite (SE3E HM) /= /inv_hom rot_of_hom_hom trans_of_hom_hom.
rewrite homM -rotation_inv ?rot_of_hom_is_SO // divrr; last first.
  by apply/orthogonal_unit/rotation_sub/rot_of_hom_is_SO.
by rewrite mulNmx subrr hom10.
Qed.

Lemma Vhom M : M \is 'SE3[T] -> inv_hom M * M = 1.
Proof.
move=> HM.
rewrite (SE3E HM) /= /inv_hom rot_of_hom_hom trans_of_hom_hom.
rewrite homM -rotation_inv ?rot_of_hom_is_SO // mulVr; last first.
  by apply/orthogonal_unit/rotation_sub/rot_of_hom_is_SO.
rewrite -mulmxA mulVmx ?mulmx1 1?addrC ?subrr ?hom10 // .
by rewrite unitmxE unitfE rotation_det ?oner_eq0 // rot_of_hom_is_SO.
Qed.

Lemma inv_homE M : M \is 'SE3[T] -> inv_hom M = M^-1.
Proof.
move=> HM.
rewrite -[RHS]mul1mx -[X in _ = X *m _ ](Vhom HM) -mulmxA.
by rewrite mulmxV ?mulmx1 // SE3_in_unitmx.
Qed.

Lemma inv_hom_is_SE3 M : M \is 'SE3[T] -> inv_hom M \is 'SE3[T].
Proof.
case/and3P=> ? ? ?; apply/and3P; split.
- by rewrite /inv_hom rot_of_hom_hom rotationV.
- by rewrite /inv_hom /hom block_mxKur.
- by rewrite /inv_hom /hom block_mxKdr.
Qed.

Lemma SE3_invr_closed : invr_closed 'SE3[T].
Proof. move=> M HM; by rewrite -inv_homE // inv_hom_is_SE3. Qed.

Lemma SE3_mulr_closed : mulr_closed 'SE3[T].
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

Lemma SE3_divr_closed : divr_closed 'SE3[T].
Proof.
split; first by rewrite SE31.
move=> A B HA HB.
by rewrite rpredM // SE3_invr_closed.
Qed.

Canonical SE3_is_divr_closed := DivrPred SE3_divr_closed.

End SE3_hom.

Section Adjoint.

Variables (T : rcfType).
Implicit Types g : 'M[T]_4.

(* adjoint transformation associated with g *)
Definition Adjoint g : 'M_6 :=
  let r := rot_of_hom g in
  let t := trans_of_hom g in
  block_mx r 0 (r * \S(t)) r.

Lemma Adjoint1 : Adjoint 1 = 1 :> 'M[T]_6.
Proof.
by rewrite /Adjoint rot_of_hom1 mul1r trans_of_hom1 spin0 -scalar_mx_block.
Qed.

Definition inv_Adjoint g : 'M_6 :=
  let r := rot_of_hom g in
  let t := trans_of_hom g in
  block_mx r^T 0 (- r^T * \S(t *m r^T)) r^T.

Lemma Adjoint_in_unitmx M : M \is 'SE3[T] -> Adjoint M \in unitmx.
Proof.
move=> ?; rewrite unitmxE /Adjoint (det_lblock (rot_of_hom M)).
by rewrite rotation_det ?mulr1 ?unitr1 // rot_of_hom_is_SO.
Qed.

Lemma VAdjoint g : rot_of_hom g \is 'SO[T]_3 -> inv_Adjoint g * Adjoint g = 1.
Proof.
set r := rot_of_hom g. set t := trans_of_hom g. move=> rSO.
rewrite /inv_Adjoint /Adjoint -mulmxE -/r -/t (mulmx_block r^T _ _ _ r).
rewrite !(mul0mx,addr0,mulmx0,add0r) mulmxA orthogonal_tr_mul ?rotation_sub //.
rewrite mul1mx mulmxE 2!mulNr spin_similarity // -mulmxA.
by rewrite orthogonal_tr_mul ?rotation_sub // mulmx1 addrC subrr -scalar_mx_block.
Qed.

Lemma inv_AdjointE g : g \is 'SE3[T] -> inv_Adjoint g = (Adjoint g)^-1.
Proof.
move=> ?; rewrite -[RHS]mul1r -[X in _ = X *m _](@VAdjoint g) ?rot_of_hom_is_SO //.
by rewrite mulmxE -mulrA mulrV ?mulr1 // Adjoint_in_unitmx.
Qed.

(*Lemma inv_Adjoint' g :
  let r := rot_of_hom g in
  let t := trans_of_hom g in
  inv_Adjoint g = block_mx r^T 0 (- \S(t) * r^T) r^T.
Proof.
move=> r t; rewrite /inv_Adjoint; f_equal.
rewrite -mulmxE mulNmx -spin_similarity ?rotationV ?rot_of_hom_SO //.
 rewrite trmxK -/t -/r.*)

(* [murray] exercise 14 (a), p.77 *)
Lemma inv_Adjoint_inv g : g \is 'SE3[T] -> (Adjoint g)^-1 = Adjoint g^-1.
Proof.
move=> ?; rewrite -inv_AdjointE // /inv_Adjoint /Adjoint -inv_homE // /inv_hom.
by rewrite !(rot_of_hom_hom,trans_of_hom_hom) mulNmx mulNr spinN !mulrN.
Qed.

Lemma AdjointM_helper g1 g2 : g1 \is 'SE3[T] -> g2 \is 'SE3[T] ->
  let r1 := rot_of_hom g1 in let r2 := rot_of_hom g2 in
  let t1 := trans_of_hom g1 in let t2 := trans_of_hom g2 in
  Adjoint (g1 * g2) = block_mx (r1 * r2) 0
    ((r1 * r2) * (\S(t2) + r2^T * \S(t1) * r2)) (r1 * r2).
Proof.
move=> Hg1 Hg2 r1 r2 t1 t2.
rewrite /Adjoint -rot_of_homM // trans_of_homM // spinD.
set a := rot_of_hom (_ * _) * _. set b := rot_of_hom (_ * _) * _.
suff : a = b by move=> ->.
rewrite {}/a {}/b; congr (_ * _).
rewrite spin_similarity; last by rewrite rot_of_hom_is_SO.
by rewrite -/t1 -/t2 -/r2 addrC.
Qed.

(* [murray] exercise 14 (b), p. 77 *)
Lemma AdjointM g1 g2 : g1 \is 'SE3[T] -> g2 \is 'SE3[T] ->
  Adjoint (g1 * g2) = Adjoint g1 * Adjoint g2.
Proof.
move=> Hg1 Hg2.
rewrite [in RHS]/Adjoint -[in RHS]mulmxE.
set r1 := rot_of_hom g1. set r2 := rot_of_hom g2.
set t1 := trans_of_hom g1. set t2 := trans_of_hom g2.
rewrite (mulmx_block r1 _ _ _ r2) !(mul0mx,mulmx0,addr0,add0r).
rewrite AdjointM_helper // -/r1 -/r2 -/t1 -/t2; f_equal.
rewrite mulmxE mulrDr [in RHS]addrC -mulrA; congr (_ + _).
rewrite !mulrA; congr (_ * _ * _); rewrite -mulrA.
move: (rot_of_hom_is_SO Hg2).
rewrite rotationE orthogonalE => /andP[/eqP -> _]; by rewrite mulr1.
Qed.

End Adjoint.

Module EuclideanMotion.
Section euclidean_motion.
Variable T : rcfType.

Record t : Type := mk {
  trans_rot : 'rV[T]_3 * 'M[T]_3;
  _ : trans_rot.2 \is 'SO[T]_3 }.

Arguments mk _ _ : clear implicits.
Implicit Types m : t.

Let homogeneous := 'M[T]_4.

Canonical t_subType := [subType for trans_rot].

Definition trans m := (trans_rot m).1.
Definition rot m := (trans_rot m).2.

Lemma rotP m : rot m \is 'SO[T]_3.
Proof. by case: m. Qed.

Local Hint Resolve rotP.

Let vector := 'rV[T]_3.
Let point := 'rV[T]_3.

Definition one := mk (0, _) (@rotation1 _ T).

Definition hom_of m := hom (rot m) (trans m).

Definition from_hom (M : homogeneous) (MSE : M \is 'SE3[T]) : t :=
  mk (trans_of_hom M, _) (rot_of_hom_is_SO MSE).

Definition hrot m := hom (rot m) 0.

Definition htrans m := hom 1 (trans m).

Lemma hom_ofE m : hom_of m = hrot m *m htrans m.
Proof. by rewrite /trans /rot mulmxE homM mulr1 mul0mx add0r. Qed.

Lemma hom_of_is_SE3 m : hom_of m \is 'SE3[T].
Proof.
case: m => -[t r] rSO /=; apply/and3P; split.
- by rewrite /rot_of_hom /hom block_mxKul.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

Definition inv' m : homogeneous := hom (rot m)^T (- trans m *m (rot m)^T).

Definition inv (m : t) : t := insubd one (- trans m *m (rot m)^T, (rot m)^T).

Lemma inv'V m : hom_of m *m inv' m = 1.
Proof.
rewrite /inv' mulmxE homM -rotation_inv // divrr; last first.
  exact/orthogonal_unit/rotation_sub.
by rewrite mulNmx subrr hom10.
Qed.

Lemma invV m : hom_of m *m hom_of (inv m) = 1.
Proof.
case: m => -[t r] /= Hr.
rewrite /hom_of /inv /rot /trans /= insubdK; first exact: (inv'V (mk (t, r) Hr)).
by rewrite -rotationV in Hr.
Qed.

Lemma rot_inv m : rot (inv m) = (rot m)^T.
Proof.
case: m => -[t r] /= Hr.
rewrite /rot /trans /inv /= insubdK //=.
move: (Hr) => Hr'; by rewrite -rotationV in Hr.
Qed.

Lemma trans_inv m : trans (inv m) = - trans m *m (rot m)^T.
Proof.
case: m => -[t r] /= Hr.
rewrite /rot /trans /inv /= insubdK //=.
move: (Hr) => Hr'; by rewrite -rotationV in Hr.
Qed.

(* NB: not used, does not seem interesting *)
(*Definition inv_trans (T : t R) := hom 1 (- SE.trans T).
Lemma inv_transP (T : t R) : trans T *m inv_trans T = 1.
Proof.
by rewrite /trans /inv_trans mulmxE homM mulr1 trmx1 mulmx1 addrC subrr hom10.
Qed.*)

Definition hom_motion (m : t) (x : 'rV[T]_4) : 'rV[T]_4 := x *m hom_of m.

Lemma hom_motion_point (p : 'rV[T]_4) m : p \is 'hP[T] ->
  hom_motion m p = from_h p *m row_mx (rot m) 0 + row_mx (trans m) 1.
Proof.
rewrite hpoint_from_h => /eqP Hp.
rewrite /hom_motion /= {1}Hp (mul_row_block (from_h p) 1 (rot m)).
by rewrite mulmx0 mulmx1 -add_row_mx mul1mx mul_mx_row mulmx0.
Qed.

Lemma hom_motion_vector (u : 'rV[T]_4) m : u \is 'hV[T] ->
  hom_motion m u = from_h u *m row_mx (rot m) 0.
Proof.
rewrite hvector_from_h => /eqP Hu.
rewrite /hom_motion /= /hom {1}Hu (mul_row_block (from_h u) 0 (rot m)).
by rewrite mulmx0 mulmx1 -add_row_mx mul0mx mul_mx_row mulmx0 row_mx0 addr0.
Qed.

Lemma hom_motionB p q m : p \is 'hP[T] -> q \is 'hP[T] ->
  hom_motion m p - hom_motion m q = hom_motion m (p - q).
Proof.
move=> Hu Hv.
rewrite hom_motion_point // hom_motion_point // opprD -addrCA -addrA subrr addr0 addrC.
by rewrite hom_motion_vector ?hpointB // from_hB mulmxBl.
Qed.

Definition motion_point m p := from_h (hom_motion m (to_hpoint p)).

Lemma motion_pointE u m : motion_point m u =
  from_h (u *m row_mx (rot m) 0 + row_mx (trans m) 1).
Proof. by rewrite /motion_point hom_motion_point ?to_hpointP // to_hpointK. Qed.

Definition motion_vector m v := from_h (hom_motion m (to_hvector v)).

Lemma motion_vectorE u m : motion_vector m u = u *m rot m.
Proof.
rewrite /motion_vector hom_motion_vector ?to_hvectorP //.
by rewrite to_hvectorK mul_mx_row mulmx0 to_hvectorK.
Qed.

Lemma motion_pointB u v m :
  motion_point m u - motion_point m v = motion_vector m (u - v).
Proof.
by rewrite /motion_point -from_hB hom_motionB ?to_hpointP // to_hpointB.
Qed.

Lemma motion_vector_preserves_norm m : {mono (motion_vector m) : u / norm u}.
Proof.
by move=> ?; rewrite motion_vectorE orth_preserves_norm // rotation_sub.
Qed.

Lemma rodrigues_homogeneous M u (MSO : M \is 'SO[T]_3) :
  axial M != 0 ->
  Aa.angle M != pi ->
  let a := aangle (angle_axis_of_rot M) in
  let w := aaxis (angle_axis_of_rot M) in
  rodrigues u a w = motion_point (mk (0, _) MSO) u.
Proof.
move=> axis0 api a w.
case/boolP : (Aa.angle M == 0) => a0.
  have M1 : M = 1.
    apply O_tr_idmx; [exact: rotation_sub |].
    apply Aa.angle0_tr => //; exact/eqP.
  rewrite motion_pointE /= /rodrigues /a aangle_of (eqP a0) cos0 sin0 scale0r.
  rewrite addr0 subrr /rot /= /trans /= !(scale0r,subr0,mul0r,addr0) M1.
  by rewrite mul_mx_row mulmx0 mulmx1 add_row_mx add0r addr0 /from_h row_mxKl.
transitivity (u *m M); last first.
  (* TODO: lemma? *)
  by rewrite motion_pointE /= (mul_mx_row u) mulmx0 add_row_mx addr0 add0r to_hpointK.
have w1 : norm w = 1.
 by rewrite /w aaxis_of // ?Aa.vaxis_neq0 // norm_normalize // Aa.vaxis_neq0.
rewrite rodriguesP //; congr (_ *m _) => {u}.
by rewrite (angle_axis_eskew_old MSO) // Aa.vaxis_neq0.
Qed.

End euclidean_motion.
End EuclideanMotion.

Coercion hom_of_euclidean_motion := EuclideanMotion.hom_of.

Section coordinate_transformation.

Variable T : rcfType.
Variable m : EuclideanMotion.t T.
(* the coordinate transformation from frame A to frame B
  (m = motion A -> B or frame configuration of B w.r.t. A) *)

Definition coortrans_vector  :=
  EuclideanMotion.motion_vector (EuclideanMotion.inv m).

Lemma coortrans_vectorE v :
  coortrans_vector v = v *m EuclideanMotion.rot (EuclideanMotion.inv m).
Proof. by rewrite /coortrans_vector EuclideanMotion.motion_vectorE. Qed.

Definition coortrans_point :=
  EuclideanMotion.motion_point (EuclideanMotion.inv m).

Lemma coortrans_pointE p : coortrans_point p =
  from_h (p *m row_mx (EuclideanMotion.rot (EuclideanMotion.inv m)) 0 +
          to_hpoint (EuclideanMotion.trans (EuclideanMotion.inv m))).
Proof. by rewrite /coortrans_point EuclideanMotion.motion_pointE. Qed.

End coordinate_transformation.

Section rigid_transformation_is_homogeneous_transformation.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Variable T : rcfType.
Let point := 'rV[T]_3.
Implicit Types m : EuclideanMotion.t T.

Lemma direct_iso_is_SE (f : 'DIso_3[T]) :
  exists m, f =1 EuclideanMotion.motion_point m.
Proof.
case: f => /= f r1.
pose r := ortho_of_iso f.
have tf0 := trans_of_isoE f.
set t := trans_of_iso f in tf0.
have Hr : r \is 'SO[T]_3 by rewrite rotationE ortho_of_iso_is_O.
set m := @EuclideanMotion.mk _ (t, r) Hr.
exists m => i.
rewrite EuclideanMotion.motion_pointE /=.
move: (trans_ortho_of_isoE f i); rewrite -/r -/t => /eqP.
rewrite eq_sym subr_eq => /eqP ->.
by rewrite mul_mx_row mulmx0 add_row_mx add0r to_hpointK.
Qed.

Lemma SE_preserves_length m :
  {mono (EuclideanMotion.motion_point m) : a b / norm (a - b)}.
Proof.
move=> m0 m1.
rewrite EuclideanMotion.motion_pointB.
by rewrite EuclideanMotion.motion_vector_preserves_norm.
Qed.

Lemma ortho_of_isoE m :
  ortho_of_iso (Iso.mk (SE_preserves_length m)) = EuclideanMotion.rot m.
Proof.
suff : forall x : 'rV[T]_3,
  x *m ortho_of_iso (Iso.mk (SE_preserves_length m)) = x *m EuclideanMotion.rot m.
  move=> Hx;apply/eqP/mulmxP => u; by rewrite -Hx.
move=> x.
rewrite trans_ortho_of_isoE /= trans_of_isoE /=.
by rewrite EuclideanMotion.motion_pointB subr0 EuclideanMotion.motion_vectorE.
Qed.

Definition preserves_angle (f : point -> point) :=
  forall i j k, vec_angle (j - i) (k - i) =
                vec_angle (f j - f i) (f k - f i).

Lemma SE_preserves_angle m : preserves_angle (EuclideanMotion.motion_point m).
Proof.
move=> /= m0 m1 k.
rewrite 2!EuclideanMotion.motion_pointB 2!EuclideanMotion.motion_vectorE.
by rewrite orth_preserves_vec_angle // rotation_sub // EuclideanMotion.rotP.
Qed.

Lemma SE_preserves_orientation m :
  preserves_orientation (Iso.mk (SE_preserves_length m)).
Proof.
move=> u v /=.
rewrite /dmap mulmxr_crossmulr ?ortho_of_iso_is_O // ortho_of_isoE.
by rewrite rotation_det ?scale1r // EuclideanMotion.rotP.
Qed.

End rigid_transformation_is_homogeneous_transformation.
