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

Section non_oriented_frame_properties.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Type p : 'rV[R]_3.

Variable f : NOFrame.t R.
Local Notation "'i'" := (NOFrame.i f).
Local Notation "'j'" := (NOFrame.j f).
Local Notation "'k'" := (NOFrame.k f).

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

Coercion matrix_of_noframe (R : rcfType) (f : NOFrame.t R) :=
  col_mx3 (NOFrame.i f) (NOFrame.j f) (NOFrame.k f).

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

Lemma frame_is_rot : col_mx3 i j k \in 'SO[R]_3.
Proof.
apply matrix_is_rotation; rewrite !rowK /=.
by rewrite (NOFrame.normi f).
by rewrite (NOFrame.normj f).
by rewrite (NOFrame.idotj f).
exact: Frame.icrossj.
Qed.

(* TODO: use rowE *)
Lemma row0_frame : row 0 f = Frame.i f.
Proof. apply/rowP => a; by rewrite 2!mxE. Qed.
Lemma row1_frame : row 1 f = Frame.j f.
Proof. apply/rowP => a; by rewrite 2!mxE. Qed.
Lemma row2_frame : row 2%:R f = Frame.k f.
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

Lemma mulmx_can_frame (v : 'rV[R]_3) : v *m can_frame = v.
Proof.
rewrite [RHS]row_sum_delta.
by apply/rowP => i; rewrite !mxE sum3E /= summxE sum3E !mxE.
Qed.

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

Module Base1.
Section base1.
Variable R : rcfType.
Variable i : 'rV[R]_3.
Hypothesis normi : norm i = 1.

(* TODO: useful? *)
Lemma e1_colinear (ie0 : colinear i 'e_0) :
  normalcomp 'e_1 (normalize i) = 'e_1.
Proof.
rewrite ortho_normalcomp // dotmulvZ.
case/colinearP : ie0 => [|[_ [p [Hp ipe0]]]].
  by rewrite -norm_eq0 norm_delta_mx (negbTE (@oner_neq0 _)).
by rewrite {2}ipe0 dotmulvZ dotmulC dote2 2!mulr0.
Qed.

Definition j := if colinear i 'e_0 then 'e_1 else normalize (normalcomp 'e_0 i).

Definition k := i *v j.

Lemma idotj : i *d j = 0.
Proof.
rewrite /j; case: ifPn => [|_]; last first.
  by rewrite dotmulvZ -{3}(normalizeI normi) normalcompP mulr0.
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
Proof. by rewrite /j colinearNv normalcompN. Qed.

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

Section relative_frame.

Variable R : rcfType.
Implicit Types f : Frame.t R.

Inductive vec f : Type := Vec of 'rV[R]_3.

Definition vec_of f (x : vec f) := let: Vec v := x in v.

(* consider "frame" to be w.r.t. the canonical frame *)
(* x *m f : *rotate* a vector in the canonical frame according to the frame
  (we obtain a new vector but still in the canonical frame after rotation)
 rotational operator *)
Definition rotate_wrt_frame f (x : vec (can_frame R)) : vec (can_frame R) :=
  Vec _ (vec_of x *m f).

Lemma rotate_wrt_canonical_frame (x : vec (can_frame R)) :
  rotate_wrt_frame (can_frame R) x = x.
Proof. case: x => x; congr Vec => /=; by rewrite mulmx_can_frame. Qed.

(* change of coordinates: same vector but with coord in the canonical frame *)
(* "mapping" from frame f to canonical frame *)
Definition can_of_rel_coord f (x : vec f) : vec (can_frame R) :=
  Vec _ (vec_of x *m f).

(* change of coordinates: same vector but with coord given in f *)
Definition rel_of_can_coord f (x : vec (can_frame R)) : vec f :=
  Vec _ (vec_of x *m f^T).

Lemma can_of_rel_coordK f (x : vec f) :
  rel_of_can_coord _ (can_of_rel_coord x) = x.
Proof.
rewrite /rel_of_can_coord /can_of_rel_coord /=; case: x => x; congr Vec => /=.
rewrite -mulmxA -(rotation_inv (frame_is_rot f)) mulmxV ?mulmx1 // unitmxE.
by rewrite (rotation_det (frame_is_rot f)) unitr1.
Qed.

Lemma rel_of_can_coordK f (x : vec _) :
  can_of_rel_coord (rel_of_can_coord f x) = x.
Proof.
rewrite /rel_of_can_coord /can_of_rel_coord /=; case: x => x; congr Vec => /=.
rewrite -mulmxA -(rotation_inv (frame_is_rot f)) mulVmx ?mulmx1 // unitmxE.
by rewrite (rotation_det (frame_is_rot f)) unitr1.
Qed.

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

End relative_frame.

Module FromTo.
Section tmp.
Variable R : rcfType.
Variables A B : Frame.t R.
Record t := mkT {
  M :> 'M[R]_3 ;
  HM : M == \matrix_(i, j) (row i A^T *d row j B^T)
  (* transpose of def 1.1 of handbook ->
     "orientation of coor frame B related to coor frame A" (A ^R_ B) *)
}.
End tmp.
End FromTo.

Coercion RotM {R} (A B : Frame.t R) := @FromTo.M _ A B.

Notation "A %> B" := (@FromTo.t _ A B) (at level 5).

Section FromTo_properties.

Variable R : rcfType.
Implicit Types A B C : Frame.t R.

Lemma FromToE A B (M : A %> B) : 
  M = (matrix_of_noframe A)^-1 *m B :> 'M[R]_3.
Proof.
case: M => /= M /eqP ->; apply/matrixP => i j.
rewrite mxE dotmulE /= mxE; apply eq_bigr => /= k _.
by rewrite mxE [row _ _ _ _]mxE mxE (rotation_inv (frame_is_rot A)) 2![_^T _ _]mxE.
Qed.

Lemma FromToCan A (M : A %> (can_frame R)) (x : vec A) :
  [fun x : 'rV_3 => x *m M] =1 [fun x => x *m A^T].
Proof.
move=> i /=.
by rewrite (FromToE M) mulmxA mulmx_can_frame (rotation_inv (frame_is_rot A)).
Qed.

Lemma FromToPi A B (M : A %> B) : NOFrame.i A *m M = NOFrame.i B.
Proof.
rewrite (FromToE M) mulmxA (_ : (A : 'M__)^-1 = A^T); last first.
  by apply/rotation_inv/(frame_is_rot A).
rewrite /matrix_of_noframe col_mx3_mul dotmulvv (NOFrame.normi A) expr1n.
rewrite (NOFrame.idotj A) (NOFrame.idotk A) row3_row_mx col_mx3E.
rewrite (mul_row_col 1%:M) mul1mx (mul_row_col 0%:M).
by rewrite !mul_scalar_mx scale0r scale0r 2!addr0.
Qed.

Lemma FromTo_is_SO A B (M : A %> B) : FromTo.M M \is 'SO[R]_3.
Proof.
move: (FromToE M); case: M => /= M _ ->.
by rewrite rpredM // ?(frame_is_rot B) // rotation_inv // ?rotationV // (frame_is_rot A).
Qed.

Lemma FromToComp_proof A B C (M1 : A %> B) (M2 : B %> C) :
  (M1 *m M2) == \matrix_(i, j) (row i A^T *d row j C^T).
Proof.
rewrite (FromToE M1) (FromToE M2) -mulmxA (mulmxA B) mulmxV; last first.
  by rewrite unitmxE (rotation_det (frame_is_rot B)) unitr1.
rewrite mul1mx; apply/eqP/matrixP => i j.
rewrite !mxE dotmulE; apply/eq_bigr => k _.
by rewrite 2![row _ _ _ _]mxE (rotation_inv (frame_is_rot A)) 2![_^T _ _]mxE mulrC.
Qed.

Definition FromToComp A B C (M1 : A %> B) (M2 : B %> C) : A %> C :=
  FromTo.mkT (FromToComp_proof M1 M2).

Lemma FromToCompE A B (M : A %> B) (u : 'rV[R]_3) :
  u *m M = u *m A^T *m B.
Proof. by rewrite -mulmxA (FromToE M) (rotation_inv (frame_is_rot A)). Qed.

End FromTo_properties.

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
apply: contra (abc); rewrite colinear_sym colinearZv invr_eq0 norm_eq0.
by rewrite subr_eq0 eq_sym (negPf ab).
Qed.

Lemma j_neq0 : j != 0.
Proof. by rewrite -norm_eq0 normj oner_neq0. Qed.

Lemma idotj : i *d j = 0.
Proof. by rewrite /= /i /j dotmulZv dotmulvZ normalcompP 2!mulr0. Qed.

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
(* therefore, x * frame_triad^T turns a vector x in the canonical frame into the frame_triad *)

(*Lemma is_SO : col_mx3 i j k \is 'SO[R]_3.
Proof. exact: (frame_is_rot frame). Qed.*)

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

Definition lframe := triad.frame l12 l123.
Definition rframe := triad.frame r12 r123.

Definition rot3 := lframe^T *m rframe.

Definition trans3 : vector := r1 - l1 *m rot3.

Lemma j_l_r : triad.j l1 l2 l3 *m rot3 = triad.j r1 r2 r3.
Proof.
rewrite /rot3 /= mulmxA col_mx3_mul dotmulC triad.idotj dotmulvv triad.normj //.
rewrite expr1n dotmul_crossmulCA crossmulvv dotmulv0 /matrix_of_noframe /=.
rewrite col_mx3E row3_row_mx (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite (mul_row_col 1%:M) mul_scalar_mx scale1r mul_scalar_mx scale0r addr0.
Qed.

Lemma k_l_r : triad.k l1 l2 l3 *m rot3 = triad.k r1 r2 r3.
Proof.
rewrite /rot3 /= mulmxA col_mx3_mul {1}/triad.k dotmulC dotmul_crossmulA.
rewrite crossmulvv dotmul0v {1}/triad.k -dotmul_crossmulA crossmulvv dotmulv0.
rewrite /matrix_of_noframe /= dotmulvv triad.normk // expr1n col_mx3E row3_row_mx.
do 2 rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite mul_scalar_mx scale1r.
Qed.

(* TODO: move? *)
Lemma mulmx_tr (M1 M2 : 'M[R]_3) : M1^T *m M2 = \matrix_(i < 3, j < 3) (row i M1^T *d row j M2^T).
Proof.
apply/matrixP => i j; rewrite /dotmul !mxE.
apply eq_bigr => /= k _; by rewrite !mxE.
Qed.

Definition FromLeftToRight : lframe %> rframe.
apply FromTo.mkT with (lframe^T *m rframe).
rewrite -(trmxK lframe) mulmx_tr.
apply/eqP/matrixP => i j; by rewrite [in LHS]mxE [in RHS]mxE dotmulC.
Qed.

Lemma FromLeftToRightE (u : 'rV[R]_3) : u *m FromLeftToRight = u *m rot3.
Proof. by rewrite FromToCompE /rot3 ?trmx_mul mulmxA. Qed.

End transformation_given_three_points.
