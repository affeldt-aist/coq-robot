(* coq-robot (c) 2017 AIST and INRIA. License: LGPL v3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg ssrint div.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

Require Import ssr_ext angle euclidean3 skew vec_angle rot frame.

(*
 OUTLINE:
 1. section central_isometry_n
 2. section central_isometry_3
 3. section isometry_3_prop
 4. section diso_3_prop
 4. section tangent_vectors_and_frames
 5. section derivative_map
     definition of what it means to preserve the cross-product by a transformation
     (sample lemma: preservation of the cross-product by derivative maps)
 6. section homogeneous_points_and_vectors
 7. section SE3_def
 8. section SE3_prop
 9. section Adjoint
    adjoint transformation
 10. Module SE
 11. section rigid_transformation_is_homogeneous_transformation
     (a direct isometry (i.e., cross-product preserving) can be expressed in homogeneous coordinates)
*)

Reserved Notation "''Iso[' T ]_ n" (at level 8, n at level 2, format "''Iso[' T ]_ n").
Reserved Notation "''CIso[' T ]_ n" (at level 8, n at level 2, format "''CIso[' T ]_ n").
Reserved Notation "''DIso_3[' T ]" (at level 8, format "''DIso_3[' T ]").
Reserved Notation "''SE3[' T ]" (at level 8, format "''SE3[' T ]").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Module Iso.
Section isometry.
Variables (T : rcfType (*realType*)) (n : nat).
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
Variable (T : rcfType (*realType*)) (n : nat).
Record t := mk {
  f : 'Iso[T]_n ;
  P : f 0 = 0 }.
End central_isometry.
End CIso.

Notation "''CIso[' T ]_ n" := (CIso.t T n).
Definition cisometry_coercion := CIso.f.
Coercion cisometry_coercion : CIso.t >-> Iso.t.

Section central_isometry_n.

Variable (T : rcfType (*realType*)) (n : nat).

Lemma central_isometry_preserves_norm (f : 'CIso[T]_n) : {mono f : x / norm x}.
Proof. by case: f => f f0 p; rewrite -(subr0 (f p)) -f0 Iso.P subr0. Qed.

(* [oneill] first part of lemma 1.6, p.100 *)
Lemma central_isometry_preserves_dotmul (f : 'CIso[T]_n) : {mono f : u v / u *d v}.
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

Variable T : rcfType (*realType*).

Definition frame_central_iso (f : 'CIso[T]_3) (p : NOFrame.t T) : NOFrame.t T.
apply: (@NOFrame.mk _ (col_mx3 (f (p|,0)) (f (p|,1)) (f (p|,2%:R)))).
apply/orthogonal3P.
by rewrite !rowK /= 3!central_isometry_preserves_norm 3!noframe_norm
  3!central_isometry_preserves_dotmul idotj noframe_idotk jdotk !eqxx.
Defined.

(* [oneill] second part of lemma 1.6, p.101 *)
Lemma central_isometry_is_linear (f : 'CIso[T]_3) : linear f.
Proof.
move=> k /= a b.
have Hp : forall p, f p = p``_0 *: f 'e_0 + p``_1 *: f 'e_1 + p``_2%:R *: f 'e_2%:R.
  move=> p.
  have -> : f p = f p *d f 'e_0 *: f 'e_0 + f p *d f 'e_1 *: f 'e_1 + f p *d f 'e_2%:R *: f 'e_2%:R.
    move: (orthogonal_expansion (frame_central_iso f (can_noframe T)) (f p)).
    rewrite !rowframeE !rowK /=.
    by rewrite !rowframeE /= !row1.
  by rewrite 3!central_isometry_preserves_dotmul // 3!coorE.
rewrite Hp (Hp a) (Hp b) !mxE /= !(scalerDl, scalerDr).
rewrite !scalerA -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrC -!addrA.
Qed.

End central_isometry_3.

Definition lin1_mx' (T : rcfType (*realType*)) n (f : 'rV[T]_n -> 'rV[T]_n) : linear f ->
  {M : {linear 'rV[T]_n -> 'rV[T]_n} & forall x, f x = M x}.
Proof.
move=> H.
have @g : {linear 'rV[T]_n -> 'rV[T]_n}.
  exists f; exact: (GRing.Linear.class_of_axiom H).
by exists g.
Defined.

Section isometry_3_prop.

Variable T : rcfType (*realType*).
Let vector := 'rV[T]_3.
Let point := 'rV[T]_3.
Implicit Types f : 'Iso[T]_3.

(* [oneill] theorem 1.7, p.101 *)
(** every isometry of E^3 can be uniquely described as an orthogonal transformation
    followed by a translation *)
Lemma trans_ortho_of_iso f :
  { trans : 'rV[T]_3 & { rot : 'M[T]_3 |
    (forall x : 'rV[T]_3, f x == x *m rot + trans) /\
    rot \is 'O[T]_3 /\
    trans = f 0 } }.
Proof.
set T' := f 0.
set Tm1f := fun x => f x - T'.
have Tm1f_is_iso : {mono Tm1f : a b / norm (a - b)}.
  move=> ? ?; by rewrite /Tm1f -addrA opprB 2!addrA subrK (Iso.P f).
have Tm1f0 : Tm1f 0 = 0 by rewrite /Tm1f subrr.
set c := @CIso.mk _ _ (Iso.mk Tm1f_is_iso) Tm1f0.
have /= linearTm1f := central_isometry_is_linear c.
have /= orthogonalTm1f := central_isometry_preserves_dotmul c.
exists T'.
case: (lin1_mx' linearTm1f) => g Hg.
exists (lin1_mx g); split; last first.
  split; last by done.
  apply/orth_preserves_dotmul => u v /=.
  by rewrite 2!mul_rV_lin1 -[in RHS]orthogonalTm1f 2!Hg.
move=> u; by rewrite mul_rV_lin1 -Hg subrK.
Qed.

Definition ortho_of_iso f : 'M[T]_3 := projT1 (projT2 (trans_ortho_of_iso f)).

Definition trans_of_iso f : 'rV[T]_3 := projT1 (trans_ortho_of_iso f).

Lemma trans_of_isoE f : trans_of_iso f = f 0.
Proof.
rewrite /trans_of_iso; by case: (trans_ortho_of_iso _) => T' [C [H1 [H2 H3]]] /=.
Qed.

Lemma ortho_of_iso_is_O f : ortho_of_iso f \is 'O[T]_3.
Proof.
rewrite /ortho_of_iso; by case: (trans_ortho_of_iso _) => T' [C [H1 [H2 H3]]] /=.
Qed.

Lemma trans_ortho_of_isoE f u : u *m ortho_of_iso f = f u - trans_of_iso f.
Proof.
rewrite /ortho_of_iso /trans_of_iso.
case: (trans_ortho_of_iso _) => T' [C [H1 [H2 H3]]] /=.
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

End isometry_3_prop.

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

Section diso_3_prop.

Variable T : rcfType.

Lemma ortho_of_diso_is_SO (f : 'DIso_3[T]) : ortho_of_iso f \is 'SO[T]_3.
Proof.
case: f => f; rewrite /iso_sgn => Hf /=; by rewrite rotationE (ortho_of_iso_is_O f).
Qed.

End diso_3_prop.

Section tangent_frames.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Let point := 'rV[T]_3.
Implicit Types p : point.

Definition tframe_i (f : TFrame.t T) : vector := (f|,0).
Definition tframe_j (f : TFrame.t T) : vector := (f|,1).
Definition tframe_k (f : TFrame.t T) : vector := (f|,2%:R).

End tangent_frames.

Lemma tvec_of_line (T : rcfType) (l : Line.t T) :
  Line.vector l = (Line.vector l).
Proof. by case: l. Qed.

Lemma line_of_tvec (T : rcfType) p (v : 'rV[T]_3) :
  Line.vector (Line.mk p v) = v.
Proof. by case: v => v /=. Qed.

Section derivative_map.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Implicit Types f : 'Iso[T]_3.

(* [oneill] theorem 2.1, p. 104 *)
Definition dmap f (v : vector) : vector :=
  let C := ortho_of_iso f in
  (v *m C).

Local Notation "f '`*'" := (@dmap f) (at level 5, format "f `*").

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

(* [oneill] lemma 3.2, p.108 *)
Lemma dmap_iso_sgnP (tf : TFrame.t T) f :
  let e1 := tf|,0 in
  let e2 := tf|,1 in
  let e3 := tf|,2%:R in
  let p := TFrame.o tf in
  f`* e1 *d (f `* e2 *v f`* e3) =
  iso_sgn f * (e1 *d (e2 *v e3)).
Proof.
move=> e1 e2 e3 p.
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
  by rewrite (row3E e1) !row3D !(add0r,addr0) !coorE.
have e2a : e2 = row3 a21 a22 a23.
  by rewrite (row3E e2) !row3D !(add0r,addr0) !coorE.
have e3a : e3 = row3 a31 a32 a33.
  by rewrite (row3E e3) !row3D !(add0r,addr0) !coorE.
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
set u1p := tframe_i tf. set u2p := tframe_j tf. set u3p := tframe_k tf.
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
  rewrite /u1p /u2p /u3p /tframe_i /tframe_j /tframe_k.
  by rewrite 3!rowframeE 3!rowE !mulmx1.
have Kv : f`* v = v1 *: e1 + v2 *: e2 + v3 *: e3 :> vector.
  rewrite [in LHS]/= Hv /dmap !mulmxDl.
  rewrite !scalemxAl [in RHS]/=.
  rewrite /u1p /u2p /u3p /tframe_i /tframe_j /tframe_k.
  by rewrite 3!rowframeE 3!rowE !mulmx1.
have @f' : NOFrame.t T.
apply (@NOFrame.mk _ (col_mx3 e1 e2 e3)).
  apply/orthogonal3P; rewrite !rowK /=.
  do 3! rewrite orth_preserves_norm ?ortho_of_iso_is_O //.
  rewrite /u1p /u2p /u3p /tframe_i /tframe_j /tframe_k.
  rewrite !rowframeE !rowE !mulmx1 3!normeE !eqxx /=.
  rewrite !(proj2 (orth_preserves_dotmul _)) ?ortho_of_iso_is_O //.
  rewrite /u1p /u2p /u3p /tframe_i /tframe_j /tframe_k.
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
    by rewrite /e3 /dmap /u3p /tframe_k rowframeE rowE mulmx1.
  rewrite scalerDr.
  rewrite -![in RHS]addrA [in RHS]addrCA [in RHS]addrC ![in RHS]addrA -addrA; congr (_ + _).
    rewrite /e1 /dmap /u1p /tframe_i.
    rewrite rowframeE rowE mulmx1.
    by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u2).
  rewrite /e2 /dmap /u2p /tframe_j.
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

(* Notation "f '`*'" := (@dmap _ f _) (at level 5, format "f '`*'"). *)

Section homogeneous_points_and_vectors.

Variable T : rcfType (*realType*).
Let point := 'rV[T]_3.
Let vector := 'rV[T]_3.

Definition hpoint := [qualify u : 'rV[T]_4 | u``_3%:R == 1].
Fact hpoint_key : pred_key hpoint. Proof. by []. Qed.
Canonical hpoint_keyed := KeyedQualifier hpoint_key.

Lemma hpointE p : (p \in hpoint) = (p``_3%:R == 1).
Proof. by []. Qed.

Definition hvector := [qualify u : 'rV[T]_4 | u``_3%:R == 0].
Fact hvector_key : pred_key hvector. Proof. by []. Qed.
Canonical hvector_keyed := KeyedQualifier hvector_key.

Lemma hvectorE p : (p \in hvector) = (p``_3%:R == 0).
Proof. by []. Qed.

Definition from_h (x : 'rV[T]_4) : 'rV[T]_3 := @lsubmx _ 1 3 1 x.

Definition to_hpoint (p : point) : 'rV[T]_4 := row_mx p 1.

Definition to_hvector (v : vector) : 'rV[T]_4 := row_mx v 0.

Lemma to_hpointK p : from_h (to_hpoint p) = p.
Proof. by rewrite /from_h row_mxKl. Qed.

Lemma to_hvectorK v : from_h (to_hvector v) = v.
Proof. by rewrite /from_h row_mxKl. Qed.

Lemma from_hD (a' b : 'rV[T]_4) : from_h (a' + b) = from_h a' + from_h b.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hZ k (a' : 'rV[T]_4) : from_h (k *: a') = k *: from_h a'.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hB (a b : 'rV[T]_4) : from_h (a - b) = from_h a - from_h b.
Proof. apply/rowP => i; by rewrite !mxE. Qed.

Lemma from_hE (x : 'rV[T]_4) : from_h x = \row_(i < 3) x 0 (inord i).
Proof.
apply/rowP => i; rewrite !mxE; congr (x 0 _).
apply val_inj => /=; by rewrite inordK // (ltn_trans (ltn_ord i)).
Qed.

Lemma rsubmx_coor3 (x : 'rV[T]_4) : @rsubmx _ 1 3 1 x = x``_3%:R%:M.
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

Notation "''hP[' T ]" := (hpoint T) (at level 8, format "''hP[' T ]").
Notation "''hV[' T ]" := (hvector T) (at level 8, format "''hV[' T ]").

Section SE3_def.

Variable T : rcfType (*realType*).

Definition hom (r : 'M[T]_3) (t : 'rV[T]_3) : 'M[T]_4 :=
  block_mx r 0 t 1.

Definition rot_of_hom (M : 'M[T]_4) : 'M[T]_3 := @ulsubmx _ 3 1 3 1 M.

Definition SE3 := [qualify M : 'M[T]_4 |
  [&& rot_of_hom M \is 'SO[T]_3,
      @ursubmx _ 3 1 3 1 M == 0 &
      @drsubmx _ 3 1 3 1 M == 1%:M] ].
Fact SE3_key : pred_key SE3. Proof. by []. Qed.
Canonical SE3_keyed := KeyedQualifier SE3_key.

End SE3_def.

Notation "''SE3[' T ]" := (SE3 T) : ring_scope.

Section SE3_prop.

Variable T : rcfType (*realType*).

Lemma hom10 : hom 1 0 = 1 :> 'M[T]_4.
Proof.
rewrite /hom -[in RHS](@submxK _ 3 1 3 1 1).
congr (@block_mx _ 3 1 3 1); apply/matrixP => i j; rewrite !mxE -val_eqE //.
rewrite {j}(ord1 j) /= addn0; by case: i => -[] // [] // [].
rewrite {i}(ord1 i) /= addn0; by case: j => -[] // [] // [].
Qed.

Lemma det_hom (r : 'M[T]_3) t : \det (hom r t) = \det r.
Proof. by rewrite /hom (det_lblock r) det1 mulr1. Qed.

Lemma rot_of_hom_hom r t : rot_of_hom (hom r t) = r :> 'M[T]_3.
Proof. by rewrite /rot_of_hom /hom block_mxKul. Qed.

Lemma rot_of_hom1 : rot_of_hom 1 = 1 :> 'M[T]__.
Proof. by rewrite -hom10 rot_of_hom_hom. Qed.

Lemma rot_of_homN (M : 'M[T]_4) : rot_of_hom (- M) = - rot_of_hom M.
Proof. apply/matrixP => i j; by rewrite !mxE. Qed.

Lemma tr_rot_of_hom (M : 'M[T]__) : (rot_of_hom M)^T = rot_of_hom M^T.
Proof. by rewrite /rot_of_hom trmx_ulsub. Qed.

Lemma rot_of_hom_SO (M : 'M[T]_4) : M \is 'SE3[T] ->
  rot_of_hom M \is 'SO[T]_3.
Proof. by case/and3P. Qed.

Definition trans_of_hom (M : 'M[T]_4) : 'rV[T]_3 := @dlsubmx _ 3 1 3 1 M.

Lemma trans_of_hom_hom r t : trans_of_hom (hom r t) = t.
Proof. by rewrite /trans_of_hom /hom block_mxKdl. Qed.

Lemma trans_of_hom1 : trans_of_hom 1 = 0 :> 'rV[T]__.
Proof. by rewrite -hom10 trans_of_hom_hom. Qed.

Lemma hom_is_SE r t : r \is 'SO[T]_3 -> hom r t \is 'SE3[T].
Proof.
move=> Hr; apply/and3P; rewrite rot_of_hom_hom Hr; split => //.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

Lemma SE3E T' : T' \is 'SE3[T] -> T' = hom (rot_of_hom T') (trans_of_hom T').
Proof.
move=> HT.
case/and3P : HT => T1 /eqP T2 /eqP T3.
by rewrite /hom -[in LHS](@submxK _ 3 1 3 1 T') T2 T3 /rot_of_hom /trans_of_hom.
Qed.

Lemma SE31 : 1 \is 'SE3[T].
Proof.
apply/and3P; split; first by rewrite rot_of_hom1 rotation1.
- apply/eqP/matrixP => i j; rewrite !mxE -val_eqE /= {j}(ord1 j) addn0.
  by case: i => -[] // [] // [].
- by apply/eqP/rowP => i; rewrite {i}(ord1 i) !mxE -val_eqE.
Qed.

Lemma SE3_is_unitmx (M : 'M[T]_4) : M \is 'SE3[T] -> M \in unitmx.
Proof.
move=> HM.
by rewrite (SE3E HM) unitmxE /= det_hom rotation_det // ?unitr1 // ?rot_of_hom_SO.
Qed.

Lemma homM r r' t t' : hom r t * hom r' t' = hom (r * r') (t *m r' + t') :> 'M[T]_4.
Proof.
rewrite /hom -mulmxE (mulmx_block r _ _ _ r') !(mulmx0,mul0mx,addr0,add0r,mulmx1).
by rewrite mulmxE mul1mx.
Qed.

Lemma rot_of_homM (g1 g2 : 'M[T]_4) : g1 \is 'SE3[T] -> g2 \is 'SE3[T] ->
  rot_of_hom (g1 * g2) = rot_of_hom g1 * rot_of_hom g2.
Proof. move/SE3E => -> /SE3E ->; by rewrite homM !rot_of_hom_hom. Qed.

Lemma trans_of_homM (g1 g2 : 'M[T]_4) : g1 \is 'SE3[T] -> g2 \is 'SE3[T] ->
  trans_of_hom (g1 * g2) = trans_of_hom g1 *m rot_of_hom g2 + trans_of_hom g2.
Proof.
move/SE3E => -> /SE3E tmp; rewrite [in LHS]tmp; by rewrite homM 2!trans_of_hom_hom.
Qed.

Definition inv_hom (M : 'M[T]_4) :=
  hom (rot_of_hom M)^T (- trans_of_hom M *m (rot_of_hom M)^T).

Lemma trmx_hom (r : 'M[T]_3) t : (hom r t)^T = block_mx r^T t^T (0 : 'rV_3) 1.
Proof. by rewrite /hom (tr_block_mx r) trmx1 trmx0. Qed.

Lemma homV (T' : 'M[T]_4) : T' \is 'SE3[T] -> T' * inv_hom T' = 1.
Proof.
move=> HT.
rewrite (SE3E HT) /= /inv_hom rot_of_hom_hom trans_of_hom_hom.
rewrite homM -rotation_inv ?rot_of_hom_SO // divrr; last first.
  by apply/orthogonal_unit/rotation_sub/rot_of_hom_SO.
by rewrite mulNmx subrr hom10.
Qed.

Lemma Vhom (T' : 'M[T]_4) : T' \is 'SE3[T] -> inv_hom T' * T' = 1.
Proof.
move=> HT.
rewrite (SE3E HT) /= /inv_hom rot_of_hom_hom trans_of_hom_hom.
rewrite homM -rotation_inv ?rot_of_hom_SO // mulVr; last first.
  by apply/orthogonal_unit/rotation_sub/rot_of_hom_SO.
rewrite -mulmxA mulVmx ?mulmx1 1?addrC ?subrr ?hom10 // .
by rewrite unitmxE unitfE rotation_det ?oner_eq0 // rot_of_hom_SO.
Qed.

Lemma SE3_inv (M : 'M[T]_4) (HM : M \is 'SE3[T]) : M^-1 = inv_hom M.
Proof.
rewrite -[LHS]mul1mx -[X in X *m _ = _](Vhom HM) -mulmxA.
by rewrite mulmxV ?mulmx1 // SE3_is_unitmx.
Qed.

Lemma SE3_invr_closed : invr_closed 'SE3[T].
Proof.
move=> M HM.
rewrite SE3_inv //.
case/and3P : HM => M1 M2 M3.
apply/and3P; split.
- by rewrite /inv_hom rot_of_hom_hom rotationV.
- by rewrite /inv_hom /hom block_mxKur.
- by rewrite /inv_hom /hom block_mxKdr.
Qed.

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

(* elementary rotations in homogeneous form *)
Definition hRx a : 'M[T]_4 := hom (Rx a) 0.

Lemma hRx_correct a (p : 'rV[T]_3) : from_h ((to_hpoint p) *m hRx a) = p *m Rx a.
Proof.
rewrite {1}/to_hpoint /hRx /hom (mul_row_block p 1 (Rx a)).
by rewrite !(mulmx0,addr0,add0r,mulmx1) -/(to_hpoint (p *m Rx a)) to_hpointK.
Qed.

Definition hRz a : 'M[T]_4 := hom (Rz a) 0.
Definition hRy a : 'M[T]_4 := hom (Ry a) 0.

(* elementary translations in homogeneous form *)
Definition hTx d : 'M[T]_4 := hom 1 (row3 d 0 0).
Definition hTy d : 'M[T]_4 := hom 1 (row3 0 d 0).
Definition hTz d : 'M[T]_4 := hom 1 (row3 0 0 d).

Definition FromToDisp (T : rcfType (*realType*)) (B A : TFrame.t T) (x : 'rV[T]_3) : 'rV[T]_3 :=
  x *m (B _R^ A) + TFrame.o B.

End SE3_prop.

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

(*Lemma inv_Adjoint' g :
  let r := rot_of_hom g in
  let t := trans_of_hom g in
  inv_Adjoint g = block_mx r^T 0 (- \S(t) * r^T) r^T.
Proof.
move=> r t; rewrite /inv_Adjoint; f_equal.
rewrite -mulmxE mulNmx -spin_similarity ?rotationV ?rot_of_hom_SO //.
 rewrite trmxK -/t -/r.*)

(* [murray] exercise 14 (a), p.77 *)
Lemma inv_AdjointE g : g \is 'SE3[T] -> inv_Adjoint g = Adjoint g^-1.
Proof.
move/SE3_inv => ->.
rewrite /inv_Adjoint /Adjoint /inv_hom.
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
rewrite spin_similarity; last by rewrite rot_of_hom_SO.
by rewrite -/t1 -/t2 -/r2 addrC.
Qed.

(* [murray] exercise 14 (b), p. 77 *)
Lemma AdjointM g1 g2 : g1 \is 'SE3[T] -> g2 \is 'SE3[T] ->
  let r1 := rot_of_hom g1 in let r2 := rot_of_hom g2 in
  let t1 := trans_of_hom g1 in let t2 := trans_of_hom g2 in
  Adjoint (g1 * g2) = Adjoint g1 * Adjoint g2.
Proof.
move=> Hg1 Hg2 r1 r2 t1 t2.
rewrite [in RHS]/Adjoint -[in RHS]mulmxE -/r1 -/r2 -/t1 -/t2.
rewrite (mulmx_block r1 _ _ _ r2) !(mul0mx,mulmx0,addr0,add0r).
rewrite AdjointM_helper // -/r1 -/r2 -/t1 -/t2; f_equal.
rewrite mulmxE mulrDr [in RHS]addrC -mulrA; congr (_ + _).
rewrite !mulrA; congr (_ * _ * _); rewrite -mulrA.
move: (rot_of_hom_SO Hg2).
rewrite rotationE orthogonalE => /andP[/eqP -> _]; by rewrite mulr1.
Qed.

End Adjoint.

Module SE.

Section se.

Variable T : rcfType.
Let vector := 'rV[T]_3.
Let point := 'rV[T]_3.

Record t : Type := mk {
  trans : 'rV[T]_3;
  rot : 'M[T]_3 ;
  rotP : rot \in 'SO[T]_3 }.

Coercion mx (T : t) := hom (rot T) (trans T).

Definition hrot (T : t) := hom (rot T) 0.

Definition htrans (T : t) := hom 1 (trans T).

Lemma tE (T' : t) : T' = hrot T' *m htrans T' :> 'M[T]_4.
Proof. by rewrite /mx /trans /rot mulmxE homM mulr1 mul0mx add0r. Qed.

Lemma mxSE_in_SE3 (T' : t) : mx T' \is 'SE3[T].
Proof.
rewrite /mx.
case: T' => t r rSO /=; apply/and3P; split.
- by rewrite /rot_of_hom /hom block_mxKul.
- by rewrite /hom block_mxKur.
- by rewrite /hom block_mxKdr.
Qed.

Definition inv (T' : t) := hom (rot T')^T (- trans T' *m (rot T')^T).

Lemma invV (T' : t) : T' *m inv T' = 1.
Proof.
rewrite /mx /inv mulmxE homM -rotation_inv; last by case: T'.
rewrite divrr; last by apply orthogonal_unit, rotation_sub; case: T'.
by rewrite mulNmx subrr hom10.
Qed.

(* NB: not used, does not seem interesting *)
(*Definition inv_trans (T : t R) := hom 1 (- SE.trans T).
Lemma inv_transP (T : t R) : trans T *m inv_trans T = 1.
Proof.
by rewrite /trans /inv_trans mulmxE homM mulr1 trmx1 mulmx1 addrC subrr hom10.
Qed.*)

Definition hom_ap (T' : t) x : 'rV[T]_4 := x *m T'.

Lemma hom_ap_point (p : 'rV[T]_4) (T' : t) : p \is 'hP[T] ->
  hom_ap T' p = from_h p *m row_mx (rot T') 0 + row_mx (trans T') 1.
Proof.
rewrite hpoint_from_h => /eqP Hp.
rewrite /hom_ap /= /mx {1}Hp (mul_row_block (from_h p) 1 (rot T')).
by rewrite mulmx0 mulmx1 -add_row_mx mul1mx mul_mx_row mulmx0.
Qed.

Lemma hom_ap_vector (u : 'rV[T]_4) (T' : t) : u \is 'hV[T] ->
  hom_ap T' u = from_h u *m row_mx (rot T') 0.
Proof.
rewrite hvector_from_h => /eqP Hu.
rewrite /hom_ap /mx /= /hom {1}Hu (mul_row_block (from_h u) 0 (rot T')).
by rewrite mulmx0 mulmx1 -add_row_mx mul0mx mul_mx_row mulmx0 row_mx0 addr0.
Qed.

Lemma hom_apB p q (T' : t) : p \is 'hP[T] -> q \is 'hP[T] ->
  hom_ap T' p - hom_ap T' q = hom_ap T' (p - q).
Proof.
move=> Hu Hv.
rewrite hom_ap_point // hom_ap_point // opprD -addrCA -addrA subrr addr0 addrC.
by rewrite hom_ap_vector ?hpointB // from_hB mulmxBl.
Qed.

(* TODO: cannot be total anymore
Lemma linear_ap_hvect (T : t) : linear (ap_hvect T).
Proof. move=> k u v; rewrite 3!ap_hvectE mulmxDl scalemxAl. Qed.
*)

Definition ap_point T' p := from_h (hom_ap T' (to_hpoint p)).

Lemma ap_pointE u T' : ap_point T' u = from_h (u *m row_mx (rot T') 0 + row_mx (trans T') 1).
Proof. by rewrite /ap_point hom_ap_point ?to_hpointP // to_hpointK. Qed.

Definition ap_vector T v := from_h (hom_ap T (to_hvector v)).

Lemma ap_vectorE u (T' : t) : ap_vector T' u = u *m rot T'.
Proof.
by rewrite /ap_vector hom_ap_vector ?to_hvectorP // to_hvectorK mul_mx_row mulmx0 to_hvectorK.
Qed.

Lemma ap_pointB u v (T' : t) : ap_point T' u - ap_point T' v = ap_vector T' (u - v).
Proof. by rewrite /ap_point -from_hB hom_apB ?to_hpointP // to_hpointB. Qed.

Lemma ap_vector_preserves_norm (T' : t) : {mono (ap_vector T') : u / norm u}.
Proof.
move=> ?; rewrite ap_vectorE orth_preserves_norm // rotation_sub //; by case: T'.
Qed.

Lemma rodrigues_homogeneous M u (HM : M \in 'SO[T]_3) :
  axial M != 0 ->
  Aa.angle M != pi ->
  let a := aangle (angle_axis_of_rot M) in
  let w := aaxis (angle_axis_of_rot M) in
  rodrigues u a w = ap_point (mk 0 HM) u.
Proof.
move=> axis0 api a w.
case/boolP : (Aa.angle M == 0) => a0.
  have M1 : M = 1.
    apply O_tr_idmx; [by apply rotation_sub |].
    apply Aa.angle0_tr => //; by apply/eqP.
  rewrite ap_pointE /= /rodrigues /a aangle_of (eqP a0) cos0 sin0 scale0r addr0 subrr.
  rewrite !(scale0r,subr0,mul0r,addr0) M1.
  by rewrite mul_mx_row mulmx0 mulmx1 add_row_mx add0r addr0 /from_h row_mxKl.
transitivity (u *m M); last first.
  (* TODO: lemma? *)
  by rewrite ap_pointE /= (mul_mx_row u) mulmx0 add_row_mx addr0 add0r to_hpointK.
have w1 : norm w = 1.
 by rewrite /w aaxis_of // ?Aa.vaxis_neq0 // norm_normalize // Aa.vaxis_neq0.
rewrite rodriguesP //; congr (_ *m _) => {u}.
by rewrite (angle_axis_eskew_old HM) // Aa.vaxis_neq0.
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

Variable T : rcfType (*realType*).
Let vector := 'rV[T]_3.
Let point := 'rV[T]_3.

Lemma direct_iso_is_SE (f : 'DIso_3[T]) :
  exists T' : SE.t T, f =1 SE.ap_point T'.
Proof.
case: f => /= f r1.
pose r := ortho_of_iso f.
have tf0 := trans_of_isoE f.
set t := trans_of_iso f in tf0.
have Hr : r \is 'SO[T]_3 by rewrite rotationE ortho_of_iso_is_O.
set T' := SE.mk t Hr.
exists T' => i.
rewrite SE.ap_pointE /=.
move: (trans_ortho_of_isoE f i); rewrite -/r -/t => /eqP.
rewrite eq_sym subr_eq => /eqP ->.
by rewrite mul_mx_row mulmx0 add_row_mx add0r to_hpointK.
Qed.

Lemma SE_preserves_length (T' : SE.t T) :
  {mono (SE.ap_point T') : a b / norm (a - b)}.
Proof. move=> m0 m1; by rewrite SE.ap_pointB SE.ap_vector_preserves_norm. Qed.

Lemma ortho_of_isoE (T' : SE.t T) :
  ortho_of_iso (Iso.mk (SE_preserves_length T')) = SE.rot T'.
Proof.
suff : forall x : 'rV[T]_3, x *m ortho_of_iso (Iso.mk (SE_preserves_length T')) = x *m SE.rot T'.
  move=> Hx;   apply/eqP/mulmxP => u; by rewrite -Hx.
move=> x.
by rewrite trans_ortho_of_isoE /= trans_of_isoE /= SE.ap_pointB subr0 SE.ap_vectorE.
Qed.

Definition preserves_angle (f : point -> point) :=
  forall i j k, vec_angle (j - i) (k - i) =
                vec_angle (f j - f i) (f k - f i).

Lemma SE_preserves_angle (T' : SE.t T) : preserves_angle (SE.ap_point T').
Proof.
move=> /= m0 m1 k.
rewrite 2!SE.ap_pointB 2!SE.ap_vectorE orth_preserves_vec_angle //.
by rewrite rotation_sub // SE.rotP.
Qed.

Lemma SE_preserves_orientation (T' : SE.t T) :
  preserves_orientation (Iso.mk (SE_preserves_length T')).
Proof.
move=> u v /=.
rewrite /dmap.
rewrite mulmxr_crossmulr ?ortho_of_iso_is_O // ortho_of_isoE.
rewrite rotation_det ?scale1r //; by case: T'.
Qed.

End rigid_transformation_is_homogeneous_transformation.
