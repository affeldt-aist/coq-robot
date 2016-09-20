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

Require Import aux angle euclidean3 skew vec_angle.

(* OUTLINE:
  1. section non_oriented_frame
  2. section oriented_frame
     (mostly about positive frames)
  3. definition of the canonical frame (e_0, e_1, e_2)
  4. Module Base1
     build a positive frame out of a unit vector
  5. Module Base
     build a positive frame out of a non-zero vector
  6. section relative_frame.
  7. Module FromTo.
     definition of the rotation from one frame to another
     FromTo.mkT
  8. section triad
    (construction of a frame out of three non-colinear points)
  9. section transformation_given_three_points
     (construction d'une transformation (rotation + translation) etant donnes
     trois points de depart et leurs positions d'arrivee)
     sample lemma: the rotation obtained behaves like a change of coordinates from left to right
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Module NOFrame.
Section non_oriented_frame_def.
Variable R : rcfType.
Record t := mk {
  i : 'rV[R]_3 ;
  j : 'rV[R]_3 ;
  k : 'rV[R]_3 ;
  normi : norm i = 1 ;
  normj : norm j = 1 ;
  normk : norm k = 1 ;
  idotj : i *d j = 0 ;
  jdotk : j *d k = 0 ;
  idotk : i *d k = 0 }.
End non_oriented_frame_def.
End NOFrame.

Coercion matrix_of_noframe (R : rcfType) (f : NOFrame.t R) :=
  col_mx3 (NOFrame.i f) (NOFrame.j f) (NOFrame.k f).

Section non_oriented_frame_properties.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Type p : 'rV[R]_3.

Variable f : NOFrame.t R.
Local Notation "'i'" := (NOFrame.i f).
Local Notation "'j'" := (NOFrame.j f).
Local Notation "'k'" := (NOFrame.k f).

Definition noframe_of_O (M : 'M[R]_3) (HM : M \is 'O[R]_3) : NOFrame.t R.
apply (@NOFrame.mk _ (row 0 M) (row 1 M) (row 2%:R M)).
by rewrite norm_row_of_O.
by rewrite norm_row_of_O.
by rewrite norm_row_of_O.
by apply/orthogonalP.
by apply/orthogonalP.
by apply/orthogonalP.
Defined.

Lemma noframe_is_ortho : col_mx3 i j k \in 'O[R]_3.
Proof.
apply matrix_is_orthogonal; rewrite !rowK /=.
by rewrite (NOFrame.normi f).
by rewrite (NOFrame.normj f).
by rewrite (NOFrame.normk f).
by rewrite (NOFrame.idotj f).
by rewrite (NOFrame.idotk f).
by rewrite (NOFrame.jdotk f).
Qed.

Lemma noframe_inv : (matrix_of_noframe f)^-1 = f^T.
Proof. by rewrite -(orthogonal_inv noframe_is_ortho). Qed.

Lemma orthogonal_expansion_helper p : 
  p *d i = 0 -> p *d j = 0 -> p *d k = 0 -> p = 0.
Proof.
do 3 rewrite dotmulE sum3E.
move=> H1 H2 H3.
have /eqP : p *m (col_mx3 i j k) ^T = 0.
  by rewrite col_mx3_mul dotmulE sum3E H1 dotmulE sum3E H2 dotmulE sum3E H3 row30.
rewrite mul_mx_rowfree_eq0; first by move/eqP.
apply/row_freeP; exists (col_mx3 i j k).
apply/eqP; rewrite -orthogonalEC.
apply matrix_is_orthogonal; rewrite !rowK /=; by case: f.
Qed.

Lemma orthogonal_expansion p : 
  p = (p *d i) *: i + (p *d j) *: j + (p *d k) *: k.
Proof.
set y : 'rV[R]_3 := (p *d i) *: i + (p *d j) *: j + (p *d k) *: k.
suff /eqP : p - y = 0; first by rewrite subr_eq0 => /eqP.
apply orthogonal_expansion_helper.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv dotmulvv (NOFrame.normi f) expr1n mulr1.
  rewrite 2!opprD 2!addrA subrr add0r dotmulZv (dotmulC j) (NOFrame.idotj f) mulr0 oppr0.
  by rewrite dotmulZv (dotmulC k) (NOFrame.idotk f) mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv (NOFrame.idotj f) mulr0 add0r.
  rewrite dotmulZv dotmulvv (NOFrame.normj f) expr1n mulr1 opprD addrA subrr.
  by rewrite dotmulZv (dotmulC k) (NOFrame.jdotk f) mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv (NOFrame.idotk f) mulr0 add0r dotmulZv.
  by rewrite (NOFrame.jdotk f) mulr0 add0r dotmulZv dotmulvv (NOFrame.normk f) expr1n mulr1 subrr.
Qed.

Definition frame_sgn := i *d (j *v k).

Lemma noframe_sgn : `| frame_sgn | = 1.
Proof.
rewrite /frame_sgn crossmul_triple.
apply/orthogonal_det/matrix_is_orthogonal; rewrite !rowK /=; by case: f.
Qed.

Lemma noframek : k = i *v j \/ k = - i *v j.
Proof.
move: noframe_sgn.
case: (lerP 0 (i *d (j *v k))) => H.
  rewrite ger0_norm // => {H}.
  rewrite /frame_sgn dotmul_crossmulA.
  move/dotmul1_inv => H; left; rewrite H //; last by case: f.
  rewrite norm_crossmul (NOFrame.normj f) (NOFrame.normi f) !mul1r.
  rewrite cos0sin1 //.
  do 2 rewrite -[LHS](mul1r).
  rewrite -{1}(NOFrame.normi f) -(NOFrame.normj f) mulrA.
  rewrite -dotmul_cos; by case: f.
rewrite ltr0_norm // => {H} /eqP.
rewrite eqr_oppLR => /eqP.
rewrite /frame_sgn dotmul_crossmulA.
move/dotmulN1_inv => H; right; rewrite crossmulNv H // ?opprK //; last by case: f.
rewrite norm_crossmul (NOFrame.normj f) (NOFrame.normi f) !mul1r.
rewrite cos0sin1 //.
do 2 rewrite -[LHS](mul1r).
rewrite -{1}(NOFrame.normi f) -(NOFrame.normj f) mulrA.
rewrite -dotmul_cos; by case: f.
Qed.

Lemma noframe_pos : k = i *v j -> frame_sgn = 1.
Proof.
move=> H.
rewrite /frame_sgn H double_crossmul dotmulvv (dotmulC j).
rewrite (NOFrame.normj f) (NOFrame.idotj f).
by rewrite scale0r subr0 expr1n scale1r dotmulvv (NOFrame.normi f) expr1n.
Qed.

Lemma noframe_neg : k = - i *v j -> frame_sgn = - 1.
Proof.
move=> H.
rewrite /frame_sgn H double_crossmul dotmulvv dotmulvN scaleNr opprK (dotmulC j).
rewrite (NOFrame.normj f) (NOFrame.idotj f).
by rewrite scale0r addr0 expr1n scale1r dotmulvN dotmulvv (NOFrame.normi f) expr1n.
Qed.

Lemma noframe_pos_crossmul : frame_sgn = 1 -> k = i *v j.
Proof.
case: noframek => // /noframe_neg -> /esym/eqP.
by rewrite -subr_eq0 opprK -mulr2n pnatr_eq0.
Qed.

Lemma noframe_posP : k = i *v j -> j = k *v i /\ i = j *v k.
Proof.
move=> H; split.
  rewrite H crossmulC double_crossmul.
  by rewrite (NOFrame.idotj f) scale0r add0r opprK dotmulvv (NOFrame.normi f) expr1n scale1r.
rewrite H double_crossmul.
by rewrite dotmulvv (NOFrame.normj f) expr1n scale1r dotmulC (NOFrame.idotj f) scale0r subr0.
Qed.

Lemma noframe_negP : k = - i *v j -> j = i *v k /\ i = k *v j.
Proof.
move=> H; split.
  rewrite H crossmulNv crossmulvN double_crossmul.
  by rewrite dotmulvv (NOFrame.normi f) expr1n scale1r (NOFrame.idotj f) scale0r add0r opprK.
rewrite H crossmulNv crossmulC crossmulvN opprK double_crossmul.
by rewrite dotmulvv (NOFrame.normj f) expr1n scale1r dotmulC (NOFrame.idotj f) scale0r subr0.
Qed.

(* [oneill] lemma 3.5, p.110 *)
Lemma crossmul_noframe_sgn v v1 v2 v3 w w1 w2 w3 :
  v = v1 *: i + v2 *: j + v3 *: k ->
  w = w1 *: i + w2 *: j + w3 *: k ->
  v *v w = frame_sgn *: ((v2 * w3 - v3 * w2) *: i -
                           (v1 * w3 - v3 * w1) *: j +
                           (v1 * w2 - v2 * w1) *: k).
Proof.
move=> -> ->.
rewrite !linearD /=.
rewrite !linearZ /=.
rewrite (crossmulC _ i).
rewrite (crossmulC _ j).
rewrite (crossmulC _ k).
rewrite !linearD /=.
rewrite (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 add0r.
case: noframek => e3e1e2.
  case: (noframe_posP e3e1e2) => H1 H2.
  rewrite (_ : _ *v _ = v2 *: k); last by rewrite linearZ /= -e3e1e2.
  rewrite scalerN (_ : _ *v _ = - v3 *: j); last first.
    by rewrite linearZ /= crossmulC -H1 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = - v1 *: k); last first.
    by rewrite linearZ /= crossmulC e3e1e2 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  rewrite (_ : _ *v _ = v3 *: i); last by rewrite linearZ /= -H2.
  rewrite scalerN (_ : _ *v _ = v1 *: j); last by rewrite linearZ /= H1.
  rewrite scalerN (_ : _ *v _ = - v2 *: i); last first.
    by rewrite linearZ /= crossmulC -H2 scaleNr scalerN.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  rewrite (noframe_pos e3e1e2).
  rewrite !scale1r -![in LHS]addrA addrC.
  rewrite -![in LHS]addrA.
  rewrite addrCA.
  rewrite addrC.
  rewrite ![in LHS]addrA.
  rewrite -addrA; congr (_ + _); last first.
    by rewrite !scalerA -scaleNr -scalerDl /= addrC mulrC (mulrC w1).
  rewrite -addrA addrACA addrC; congr (_ + _).
    by rewrite -scaleNr !scalerA -scalerDl addrC mulrC mulNr (mulrC w2).
  by rewrite !scalerA -scalerBl scalerN -scaleNr opprB mulrC (mulrC w3).
case: (noframe_negP e3e1e2) => H1 H2.
rewrite (_ : _ *v _ = - v2 *: k); last first.
  by rewrite linearZ /= e3e1e2 crossmulNv scalerN scaleNr opprK.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = v3 *: j); last first.
  by rewrite linearZ /= -H1.
rewrite scalerN.
rewrite (_ : _ *v _ = v1 *: k); last first.
  by rewrite linearZ /= crossmulC -crossmulNv -e3e1e2.
rewrite scalerN.
rewrite (_ : _ *v _ = 0); last first.
  by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 addr0.
rewrite (_ : _ *v _ = - v3 *: i); last first.
  by rewrite linearZ /= crossmulC -H2 scalerN scaleNr.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = - v1 *: j); last first.
  by rewrite linearZ /= crossmulC -H1 scalerN scaleNr.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = v2 *: i); last first.
  by rewrite linearZ /= -H2.
rewrite scalerN.
rewrite (_ : _ *v _ = 0); last first.
  by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 addr0.
rewrite (noframe_neg e3e1e2).
rewrite -![in LHS]addrA addrC -addrA.
rewrite addrCA -addrA addrC ![in LHS]addrA -addrA; congr (_ + _); last first.
  by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w2).
rewrite -addrA addrACA; congr (_ + _).
  by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w3).
by rewrite !scalerA -scalerBl scalerN mulrN1 scaleNr opprK mulrC (mulrC w1).
Qed.

End non_oriented_frame_properties.

Lemma noframe_is_unit (R : rcfType) (f : NOFrame.t R) :
  matrix_of_noframe f \is a GRing.unit.
Proof.
apply/orthogonal_unit/matrix_is_orthogonal => /=; rewrite !rowK /=; by case: f.
Qed.

(* TODO: move *)
Lemma mxE_col_row {R : Type} (M : 'M[R]_3) i j : M i j = (col j (row i M)) 0 0.
Proof. by rewrite !mxE. Qed.

Lemma colE (R : rcfType) (v : 'rV[R]_3) j : col j v = 'e_j *m v^T.
Proof.
apply/colP => i; rewrite {i}(ord1 i) !mxE coorE /dotmul mxE.
apply eq_bigr => /= i _; by rewrite !mxE eqxx /= mulrC.
Qed.

Lemma dotrow {R : rcfType} (M : 'M[R]_3) i j : M i j = 'e_j *d row i M.
Proof. by rewrite mxE_col_row /dotmul colE. Qed.

Module Frame.
Section frame.
Variable R : rcfType.

Record t := mk {
  noframe_of :> NOFrame.t R ;
  P : frame_sgn noframe_of = 1}.

Definition i (f : t) := NOFrame.i f.
Definition j (f : t) := NOFrame.j f.
Definition k (f : t) := NOFrame.k f.

Variable f : t.

Local Notation "'i'" := (i f).
Local Notation "'j'" := (j f).
Local Notation "'k'" := (k f).

Lemma icrossj : k = i *v j.
Proof. exact: (noframe_pos_crossmul (P f)). Qed.

Lemma icrossk : i *v k = - j.
Proof. by rewrite crossmulC -(proj1 (@noframe_posP _ f icrossj)). Qed.

Lemma jcrossk : j *v k = i.
Proof. by rewrite -(proj2 (@noframe_posP _ f icrossj)). Qed.

End frame.
End Frame.

Coercion noframe_of_frame (R : rcfType) (f : Frame.t R) : NOFrame.t R := 
  let: Frame.mk f' _ := f in f'.

Section oriented_frame_properties.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Record nframe := mkNFrame {
  noframe_of_nframe :> NOFrame.t R ;
  nframeP : frame_sgn noframe_of_nframe = -1}.

Variable f : Frame.t R.
Local Notation "'i'" := (Frame.i f).
Local Notation "'j'" := (Frame.j f).
Local Notation "'k'" := (Frame.k f).

(*
TODO: restor
Lemma pframe_swap01 i j k : pframe i j k -> pframe j (- i) k.
Proof.
case => -[] i1 j1 k1 ij jk ik Hsgn.
apply: mkPFrame.
  apply: mkNOFrame => //.
  by rewrite normN.
  by rewrite dotmulvN dotmulC ij oppr0.
  by rewrite dotmulNv ik oppr0.
move=> f.
rewrite /frame_sgn dotmul_crossmulA linearN /= crossmulC -(icrossj (mkPFrame Hsgn)).
by rewrite opprK dotmulvv k1 expr1n.
Qed.
*)

Lemma frame_is_rot : matrix_of_noframe f \in 'SO[R]_3.
Proof.
apply matrix_is_rotation; rewrite !rowK /=.
by rewrite (NOFrame.normi f).
by rewrite (NOFrame.normj f).
by rewrite (NOFrame.idotj f).
exact: Frame.icrossj.
Qed.

Definition frame_of_SO (M : 'M[R]_3) (HM : M \is 'SO[R]_3) : Frame.t R.
apply (@Frame.mk _ (noframe_of_O (rotation_sub HM))).
by rewrite /frame_sgn crossmul_triple /= -col_mx3_rowE rotation_det.
Defined.

(* TODO: use rowE *)
Lemma row0_frame : row 0 f = NOFrame.i f.
Proof. apply/rowP => a; by rewrite 2!mxE. Qed.
Lemma row1_frame : row 1 f = NOFrame.j f.
Proof. apply/rowP => a; by rewrite 2!mxE. Qed.
Lemma row2_frame : row 2%:R f = NOFrame.k f.
Proof. apply/rowP => a; by rewrite !mxE. Qed.

Lemma norm_row (a : 'I_3) : norm (row a f) = 1.
Proof.
case/boolP : (a == 0) => [/eqP ->|]. 
  by rewrite row0_frame NOFrame.normi.
rewrite ifnot0 => /orP [] /eqP ->.
  by rewrite row1_frame NOFrame.normj.
by rewrite row2_frame NOFrame.normk.
Qed.

End oriented_frame_properties.

(* frame with an origin (tangent frame) *)
Module TFrame.
Section tframe.
Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.

Record t := mk {
  o : point ;
  frame_of :> Frame.t R }.

Definition trans (f : t) (u : vector) : t := mk (o f + u) f.

End tframe.
End TFrame.

Coercion frame_of_tframe (R : rcfType) (f : TFrame.t R) :=
  let: TFrame.mk _ f' := f in f'.

Section canonical_frame.

Variable R : rcfType.

Definition can_noframe := NOFrame.mk
  (norm_delta_mx R 0) (norm_delta_mx _ 1) (norm_delta_mx _ 2%:R)
  (dote2 _ 0 1) (dote2 _ 1 2%:R) (dote2 _ 0 2%:R).

Lemma can_frameP : frame_sgn can_noframe = 1.
Proof. rewrite /frame_sgn crossmulE dotmulE sum3E !mxE /=. by Simp.r. Qed.

Definition can_frame := Frame.mk can_frameP.

Definition can_frame_1 : can_frame = 1 :> 'M_3.
Proof. by apply/matrix3P; rewrite !mxE. Qed.

(*Lemma mulmx_can_frame (v : 'rV[R]_3) : v *m can_frame = v.
Proof.
rewrite [RHS]row_sum_delta.
by apply/rowP => i; rewrite !mxE sum3E /= summxE sum3E !mxE.
Qed.*)

(* rotation M <-> canonical_frame *)
Lemma rotation_can_frame (M : Frame.t R) i j : M i j = row j can_frame *d row i M.
Proof.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite row0_frame /= dotrow.
  rewrite ifnot0 => /orP [] /eqP ->.
    by rewrite row1_frame /= dotrow.
  by rewrite row2_frame /= dotrow.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite row0_frame /= dotrow.
  rewrite ifnot0 => /orP [] /eqP ->.
    by rewrite row1_frame /= dotrow.
  by rewrite row2_frame /= dotrow.
case/boolP : (j == 0) => [/eqP ->|].
  by rewrite row0_frame /= dotrow.
rewrite ifnot0 => /orP [] /eqP ->.
  by rewrite row1_frame /= dotrow.
by rewrite row2_frame /= dotrow.
Qed.

Definition can_tframe := TFrame.mk 0 can_frame. 

End canonical_frame.

(* TODO: go to euclidean3.v? *)
Lemma basis_change (R : rcfType) (M : 'M[R]_3) (f : NOFrame.t R) (A : 'M[R]_3) :
  let i := NOFrame.i f in
  let j := NOFrame.j f in
  let k := NOFrame.k f in
  i *m M = A 0 0 *: i + A 0 1 *: j + A 0 2%:R *: k ->
  j *m M = A 1 0 *: i + A 1 1 *: j + A 1 2%:R *: k ->
  k *m M = A 2%:R 0 *: i + A 2%:R 1 *: j + A 2%:R 2%:R *: k ->
  let P := col_mx3 i j k in
  M = P^-1 * A * P.
Proof.
move=> i j k H1 H2 H3 P.
have : P * M = A * P.
  rewrite /P -mulmxE mulmx_col3 (col_mx3_rowE A).
  rewrite mulmx_col3 H1 H2 H3.
  congr col_mx3; apply/rowP => a; by rewrite !mxE sum3E !mxE.
rewrite -mulrA => <-.
rewrite mulrA mulVr ?mul1r // unitmxE unitfE /P det_col_mx3.
move: (noframe_sgn f) => /=.
by rewrite /frame_sgn dotmul_crossmulA -normr_gt0 => ->; rewrite ltr01.
Qed.

(* TODO: useful? *)
Lemma e1_colinear (R : rcfType) (i : 'rV[R]_3) (ie0 : colinear i 'e_0) :
  norm i = 1 ->
  normalcomp 'e_1 (normalize i) = 'e_1.
Proof.
move=> normi.
rewrite ortho_normalcomp // dotmulvZ normi invr1 mul1r.
case/colinearP : ie0 => [|[_ [p [Hp ipe0]]]].
  by rewrite -norm_eq0 normeE oner_eq0.
by rewrite ipe0 dotmulvZ dote2 mulr0.
Qed.

Module Base1.
Section base1.
Variable R : rcfType.
Variable i : 'rV[R]_3.
Hypothesis normi : norm i = 1.

Definition j := if colinear i 'e_0 then 'e_1 else normalize (normalcomp 'e_0 i).

Definition k := i *v j.

Lemma idotj : i *d j = 0.
Proof.
rewrite /j; case: ifPn => [|_]; last first.
  by rewrite dotmulvZ -{3}(normalizeI normi) dotmul_orthogonalize mulr0.
case/colinearP => [| [_ [k [Hk ->]]]].
  by rewrite -norm_eq0 norm_delta_mx (negbTE (oner_neq0 _)).
by rewrite dotmulZv dote2 mulr0.
Qed.

Lemma idotk : i *d k = 0.
Proof. by rewrite /k dotmul_crossmulA crossmulvv dotmul0v. Qed.

Lemma jdotk : j *d k = 0.
Proof. by rewrite /k dotmul_crossmulCA crossmulvv dotmulv0. Qed.

Lemma normj : norm j = 1.
Proof.
rewrite /j; case: ifPn => iVi; first by rewrite norm_delta_mx.
rewrite norm_normalize //; apply: contra iVi.
by rewrite normalcomp_colinear // colinear_sym.
Qed.

Lemma normk : norm k = 1.
Proof.
by rewrite /k norm_crossmul_normal // ?norm_normalize // ?normj // idotj // mulr0.
Qed.

Definition noframe := NOFrame.mk normi normj normk idotj jdotk idotk.

Lemma sgn_noframe : frame_sgn noframe = 1.
Proof.
rewrite /frame_sgn /= dotmul_crossmulA dotmulvv.
by rewrite -/k normk expr1n.
Qed.

Definition frame := Frame.mk sgn_noframe.

End base1.

Section base1_lemmas.

Variable (R : rcfType).

Lemma je0 : j 'e_0 = 'e_1 :> 'rV[R]_3.
Proof. by rewrite /j colinear_refl. Qed.

Lemma ke0 : k 'e_0 = 'e_2%:R :> 'rV[R]_3.
Proof. by rewrite /k /j colinear_refl vece2 odd_perm301 -exprnP expr0 scale1r. Qed.

Variable u : 'rV[R]_3.
Hypothesis u0 : u != 0.

Lemma jN : j (- u) = j u.
Proof. by rewrite /j colinearNv normalcompvN. Qed.

Lemma kN : k (- u) = - k u.
Proof. by rewrite /k jN crossmulNv. Qed.

End base1_lemmas.
End Base1.

Module Base.
Section build_base.
Variables (R : rcfType) (u : 'rV[R]_3).
Hypothesis u0 : u != 0.

Definition i := normalize u.

Let normi : norm i = 1.
Proof. by rewrite norm_normalize. Qed.

Definition j := Base1.j i.

Definition k := Base1.k i.

Lemma udotj : u *d j = 0.
Proof.
move: (Base1.idotj normi) => /eqP.
by rewrite dotmulZv mulf_eq0 invr_eq0 norm_eq0 (negPf u0) => /eqP.
Qed.

Lemma udotk : u *d k = 0.
Proof.
move/eqP: (Base1.idotk i); by rewrite dotmulZv mulf_eq0 invr_eq0 norm_eq0 (negPf u0) => /eqP.
Qed.

Definition frame := Base1.frame normi.

Lemma icrossj : k = i *v j.
Proof. exact: (Frame.icrossj frame). Qed.

Lemma icrossk : i *v k = - j.
Proof. exact: (Frame.icrossk frame). Qed.

End build_base.

Section build_base_lemmas.

Variable (R : rcfType) (u : 'rV[R]_3).
Hypothesis u0 : u != 0.

Lemma jZ p (p0 : 0 < p) : j (p *: u) = j u.
Proof. by rewrite /j /i normalizeZ. Qed.

Lemma jN : j (- u) = j u.
Proof. by rewrite /j /i normalizeN Base1.jN. Qed.

Lemma kZ p (p0 : 0 < p) : k (p *: u) = k u.
Proof. by rewrite /k /i normalizeZ. Qed.

Lemma kN : k (- u) = - k u.
Proof. by rewrite /k /i normalizeN Base1.kN. Qed.

Lemma iE : i u = Frame.i (frame u0).
Proof. done. Qed.

Lemma jE : j u = Frame.j (frame u0).
Proof. done. Qed.

Lemma kE : k u = Frame.k (frame u0).
Proof. done. Qed.

Lemma j_tr_mul (v : 'rV[R]_3) (v1 : norm v = 1) : j v *m v^T *m v = 0.
Proof.
rewrite /Base.j /Base.i normalizeI // /Base1.j.
case: ifPn => [|_].
  case/colinearP => [|[_[k [Hk1 Hk2]]]].
    move/eqP/rowP/(_ ord0).
    rewrite !mxE !eqxx /= => /eqP; by rewrite oner_eq0.
  rewrite Hk2 !linearZ /= -scalemxAl scalerA -expr2 -sqr_normr Hk1 v1 normeE.
  rewrite div1r invr1 expr1n scale1r (mx11_scalar ('e_1 *m _)) -/('e_1 *d 'e_0).
  by rewrite dote2 oner_eq0 /= mul_scalar_mx scale0r.
apply/eqP.
by rewrite /normalize -!scalemxAl scaler_eq0 normalcomp_mul_tr // orbT.
Qed.

Lemma k_tr_mul (v : 'rV[R]_3) (v1 : norm v = 1) : k v *m v^T *m v = 0.
Proof.
rewrite /Base.k /Base.i normalizeI // /Base1.k /Base1.j.
case: ifPn => [|_].
  case/colinearP => [|[_[k [Hk1 Hk2]]]].
    move/eqP/rowP/(_ ord0).
    rewrite !mxE !eqxx /= => /eqP; by rewrite oner_eq0.
  rewrite Hk2 !linearZ /= -scalemxAl scalerA -expr2 -sqr_normr Hk1 v1 normeE.
  rewrite div1r invr1 expr1n scale1r crossmulZv vecij -!scalemxAl.
  rewrite (mx11_scalar ('e_2%:R *m _)) -/('e_2%:R *d 'e_0) dote2 /=.
  by rewrite mul_scalar_mx scale0r scaler0.
apply/eqP.
rewrite /normalize crossmulvZ -!scalemxAl scaler_eq0; apply/orP; right.
rewrite /normalcomp linearD /= crossmulvN 2!crossmulvZ crossmulvv 2!scaler0 subr0.
move: (axialcompE (v *v 'e_0) v).
rewrite v1 expr1n invr1 scale1r => <-.
by rewrite axialcomp_crossmul.
(*
apply/eqP.
rewrite /normalize crossmulvZ -!scalemxAl scaler_eq0; apply/orP; right.
rewrite /normalcomp linearD /= crossmulvN crossmulvZ crossmulvv scaler0 subr0.
by rewrite -axialcompE axialcomp_crossmul.
*)
Qed.

End build_base_lemmas.

End Base.

(*Module Frame.
Section frame_section.
Variable R : rcfType.
Local Notation coordinate := 'rV[R]_3.
Local Notation basisType := 'M[R]_3.
Definition x_ax : basisType -> 'rV[R]_3 := row 0.
Definition y_ax : basisType -> 'rV[R]_3 := row 1%R.
Definition z_ax : basisType -> 'rV[R]_3 := row 2%:R.

Record t := mkT {
  origin : coordinate ;
  basis :> basisType ;
  _ : unitmx basis }.

Lemma unit (f : t) : basis f \in GRing.unit. Proof. by case: f. Qed.
End frame_section.
End Frame.

Coercion Framebasis R (f : Frame.t R) : 'M[R]_3 := Frame.basis f.
*)
(*Hint Immediate Frame.unit.*)

(* base vectors of A in terms of the basis vectors of B: *)
Definition FromTo (R : rcfType) (A B : Frame.t R) :=
  \matrix_(i, j) (row i A *d row j B).
(* = the rotation matrix that transforms a vector expressed in coordinate frame A
   to a vector expressed in coordinate frame B *)
(* = orientation of frame A relative to B *)

Notation "A _R^ B" := (@FromTo _ A B) (at level 5).

Section FromTo_properties.

Variable R : rcfType.
Implicit Types A B C : Frame.t R.

Lemma FromToE A B : (A _R^ B) = A *m (matrix_of_noframe B)^-1 :> 'M[R]_3.
Proof.
apply/matrixP => i j.
rewrite mxE dotmulE /= mxE; apply eq_bigr => /= k _.
rewrite mxE; congr (_ * _).
by rewrite mxE noframe_inv [in RHS]mxE.
Qed.

Lemma FromTo_to_can A : A _R^ (can_frame R) = A.
Proof. by rewrite FromToE can_frame_1 invr1 mulmx1. Qed.

Lemma FromTo_from_can A : (can_frame R) _R^ A = A^T.
Proof. by rewrite FromToE can_frame_1 mul1mx noframe_inv. Qed.

Lemma FromToI A : A _R^ A = 1.
Proof.
apply/matrix3P;
  rewrite !mxE /= ?dotmulvv ?norm_row_of_O ?noframe_is_ortho // ?expr1n //;
  by apply/orthogonalP/noframe_is_ortho.
Qed.

Lemma trmx_FromTo A B : (A _R^ B)^T = B _R^ A.
Proof. apply/matrix3P; rewrite !mxE /=; by rewrite dotmulC. Qed.

Lemma FromTo_is_O A B : A _R^ B \is 'O[R]_3.
Proof.
rewrite orthogonalE FromToE trmx_mul.
rewrite {2}(noframe_inv B) trmxK -mulmxE mulmxA -(mulmxA _ (matrix_of_noframe B)^-1).
by rewrite mulVmx ?noframe_is_unit // mulmx1 -noframe_inv mulmxV // noframe_is_unit.
Qed.

Lemma FromTo_is_SO A B : A _R^ B \is 'SO[R]_3.
Proof.
by rewrite FromToE rpredM // ?frame_is_rot // noframe_inv rotationV frame_is_rot.
Qed.

Lemma FromTo_comp A B C : (C _R^ B) *m (B _R^ A) = C _R^ A.
Proof.
rewrite 2!FromToE -mulmxA (mulmxA _ B) mulVmx; last first.
  by rewrite unitmxE (rotation_det (frame_is_rot B)) unitr1.
rewrite mul1mx; apply/matrixP => i j.
rewrite !mxE dotmulE; apply/eq_bigr => k _.
rewrite 2![row _ _ _ _]mxE; congr (_ * _).
by rewrite noframe_inv mxE.
Qed.

End FromTo_properties.

Definition noframe_of_FromTo (R : rcfType) (A B : Frame.t R) : NOFrame.t R.
refine (@NOFrame.mk _ (row 0 (A _R^ B)) (row 1 (A _R^ B)) (row 2%:R (A _R^ B)) _ _ _ _ _ _).
by rewrite norm_row_of_O // FromTo_is_O.
by rewrite norm_row_of_O // FromTo_is_O.
by rewrite norm_row_of_O // FromTo_is_O.
by apply/orthogonalP/FromTo_is_O.
by apply/orthogonalP/FromTo_is_O.
by apply/orthogonalP/FromTo_is_O.
Defined.

Definition frame_of_FromTo (R : rcfType) (B A : Frame.t R) : Frame.t R.
refine (@Frame.mk _ (noframe_of_FromTo B A) _).
rewrite /frame_sgn.
rewrite crossmul_triple.
apply rotation_det.
rewrite /=.
rewrite -col_mx3_rowE.
by apply: FromTo_is_SO.
Defined.

Module rFrame.
Section rframe.
Variable R : rcfType.
Variable A : Frame.t R.
Record t := mk {
  B : Frame.t R ;
  M := B _R^ A
}.
End rframe.
End rFrame.

Section change_of_coordinate.

Variable R : rcfType.
Implicit Types A B : Frame.t R.

Inductive vec (f : Frame.t R) : Type := Vec of 'rV[R]_3.

Definition vec_of f (x : vec f) := let: Vec v := x in v.

Lemma vec_ofK A (x : vec A) : Vec A (vec_of x) = x.
Proof. by case: x. Qed.

Lemma VecK A (x : 'rV[R]_3) : vec_of (Vec A x) = x.
Proof. by case: x. Qed.

(* change of coordinates: "mapping" from frame A to frame B *)
Definition to_coord A B (x : vec A) : vec B := Vec _ (vec_of x *m (A _R^ B)).

Lemma to_coordK A B (x : vec A) : to_coord A (to_coord B x) = x.
Proof.
rewrite /to_coord /= 2!FromToE -2!mulmxA (mulmxA ((matrix_of_noframe B)^-1)).
rewrite mulmxE mulVr ?noframe_is_unit // mulmxA mul1r -mulmxA mulmxE.
by rewrite divrr ?noframe_is_unit // mulmx1 vec_ofK.
Qed.

Lemma to_coordE A B (x : 'rV[R]_3) :
  to_coord B (Vec A x) = Vec _ (x *m A (*A->can*) *m B^T(*can->B*)).
Proof. by rewrite /to_coord VecK FromToE noframe_inv mulmxA. Qed.

Lemma to_coordE_from_can A (x : 'rV[R]_3) :
  to_coord A (Vec (can_frame R) x) = Vec _ (x *m A^T).
Proof. by rewrite to_coordE can_frame_1 mulmx1. Qed.

Lemma to_coordE_to_can A (x : 'rV[R]_3) :
  to_coord (can_frame R) (Vec A x) = Vec _ (x *m A).
Proof. by rewrite to_coordE can_frame_1 trmx1 mulmx1. Qed.

End change_of_coordinate.

(*Section about_frame.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := Frame.t R.

(* coordinate in frame f *)
Inductive coor (f : frame) : Type := Coor of 'rV[R]_3.

Definition absolute_coor (f : frame) (x : coor f) : 'rV[R]_3 :=
  match x with Coor v => Frame.origin f + v *m Frame.basis f end.

Definition relative_coor f (x : coordinate) : coor f :=
  Coor _ ((x - Frame.origin f) *m (Frame.basis f)^-1).

Lemma absolute_coorK f (x : coor f) : relative_coor f (absolute_coor x) = x.
Proof.
case: x => /= v.
by rewrite /relative_coor addrC addKr -mulmxA mulmxV // ?mulmx1 // Frame.unit.
Qed.

Lemma relative_coorK f (x : coordinate) : absolute_coor (relative_coor f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // ?Frame.unit // mulmx1 addrC addrNK. Qed.

(* vector in frame f *)
Inductive vec (f : frame) : Type := Vec of 'rV[R]_3.

Definition absolute_vec f (x : vec f) : 'rV[R]_3 :=
  match x with Vec v => v *m Frame.basis f end.

Definition relative_vec f (x : vector) : vec f :=
  Vec _ (x *m (Frame.basis f)^-1).

Lemma absolute_vecK f (x : vec f) : relative_vec f (absolute_vec x) = x.
Proof. case: x => /= v. by rewrite /relative_vec -mulmxA mulmxV // ?Frame.unit // mulmx1. Qed.

Lemma relative_vecK f (x : vector) : absolute_vec (relative_vec f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // ?Frame.unit // mulmx1. Qed.

End about_frame.*)

Module triad.
Section triad.
Variable R : rcfType.
Let point := 'rV[R]_3.

Variables a b c : point.
Hypothesis ab : a != b.
Hypothesis abc : ~~ colinear (b - a) (c - a).

Definition i := normalize (b - a).

Definition j := normalize (normalcomp (c - a) i).

Definition k := i *v j.

Definition t := (i, j, k).

Let ac : a != c.
Proof. by apply: contra abc => /eqP ->; rewrite subrr /colinear crossmulv0. Qed.

Lemma normi : norm i = 1.
Proof. by rewrite /i norm_normalize // subr_eq0 eq_sym. Qed.

Lemma i_neq0 : i != 0.
Proof. by rewrite -norm_eq0 normi oner_neq0. Qed.

Lemma normj : norm j = 1.
Proof.
rewrite /j norm_normalize // normalcomp_colinear ?normi //.
apply: contra (abc); rewrite colinearvZ invr_eq0 norm_eq0 subr_eq0.
by rewrite eq_sym (negPf ab) /= colinear_sym.
Qed.

Lemma j_neq0 : j != 0.
Proof. by rewrite -norm_eq0 normj oner_neq0. Qed.

Lemma idotj : i *d j = 0.
Proof. by rewrite /= /i /j dotmulZv dotmulvZ dotmul_orthogonalize 2!mulr0. Qed.

Lemma jdotk : j *d k = 0.
Proof. by rewrite /k dotmul_crossmulCA crossmulvv dotmulv0. Qed.

Lemma idotk : i *d k = 0.
Proof. by rewrite /k dotmul_crossmulA crossmulvv dotmul0v. Qed.

Lemma normk : norm k = 1.
Proof. by rewrite norm_crossmul_normal // ?normi // ?normj // idotj. Qed.

Lemma k_neq0 : k != 0.
Proof. by rewrite -norm_eq0 normk oner_neq0. Qed.

Definition noframe := NOFrame.mk normi normj normk idotj jdotk idotk.

Lemma noframe_is_pos : frame_sgn noframe = 1.
Proof.
rewrite /frame_sgn /k double_crossmul dotmulvv normj expr1n scale1r (dotmulC j).
by rewrite idotj scale0r subr0 dotmulvv normi expr1n.
Qed.

Definition frame := Frame.mk noframe_is_pos.

End triad.
End triad.

Section transformation_given_three_points.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.

Variables l1 l2 l3 r1 r2 r3 : point.
Hypotheses (l12 : l1 != l2) (r12 : r1 != r2).
Hypotheses (l123 : ~~ colinear (l2 - l1) (l3 - l1))
           (r123 : ~~ colinear (r2 - r1) (r3 - r1)).

Definition lmat := triad.frame l12 l123.
Definition rmat := triad.frame r12 r123.

(* TODO: move? *)
Lemma mulmx_tr (M1 M2 : 'M[R]_3) : M1^T *m M2 = \matrix_(i < 3, j < 3) (row i M1^T *d row j M2^T).
Proof.
apply/matrixP => i j; rewrite /dotmul !mxE.
apply eq_bigr => /= k _; by rewrite !mxE.
Qed.

Definition rot_l2r := lmat^T *m rmat.

Definition trans3 : vector := r1 - l1 *m rot_l2r.

Lemma i_l_r : triad.i l1 l2 *m rot_l2r = triad.i r1 r2.
Proof.
rewrite /rot_l2r /= mulmxA col_mx3_mul dotmulvv triad.normi // expr1n.
rewrite triad.idotj triad.idotk /matrix_of_noframe mulmx_row3_col3.
by rewrite !scale0r scale1r !addr0.
Qed.

Lemma j_l_r : triad.j l1 l2 l3 *m rot_l2r = triad.j r1 r2 r3.
Proof.
rewrite /rot_l2r /= mulmxA col_mx3_mul dotmulC triad.idotj dotmulvv triad.normj //.
rewrite expr1n dotmul_crossmulCA crossmulvv dotmulv0 /matrix_of_noframe /=.
rewrite col_mx3E row3_row_mx (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite (mul_row_col 1%:M) mul_scalar_mx scale1r mul_scalar_mx scale0r addr0.
Qed.

Lemma k_l_r : triad.k l1 l2 l3 *m rot_l2r = triad.k r1 r2 r3.
Proof.
rewrite /rot_l2r /= mulmxA col_mx3_mul {1}/triad.k dotmulC dotmul_crossmulA.
rewrite crossmulvv dotmul0v {1}/triad.k -dotmul_crossmulA crossmulvv dotmulv0.
rewrite /matrix_of_noframe /= dotmulvv triad.normk // expr1n col_mx3E row3_row_mx.
do 2 rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite mul_scalar_mx scale1r.
Qed.

End transformation_given_three_points.
