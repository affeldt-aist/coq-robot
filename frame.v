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
  1. Module NOFrame
     Section non_oriented_frame_properties
  2. Module Frame
     Section oriented_frame_properties
     mostly about positive frames
  3. Module TFrame
     positive frames with an origin
  3. definition of the canonical frame <e_0, e_1, e_2>
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

Module NOFrameInterface.
Section noframe_interface.
Variable R : rcfType.
Record t (R : rcfType) : Type := mk {
  i : 'rV[R]_3 ;
  j : 'rV[R]_3 ;
  k : 'rV[R]_3 ;
  normi : norm i = 1 ;
  normj : norm j = 1 ;
  normk : norm k = 1 ;
  idotj : i *d j = 0 ;
  jdotk : j *d k = 0 ;
  idotk : i *d k = 0
}.
End noframe_interface.
End NOFrameInterface.
Definition normi := NOFrameInterface.normi.
Definition normj := NOFrameInterface.normj.
Definition normk := NOFrameInterface.normk.
Definition idotj := NOFrameInterface.idotj.
Definition jdotk := NOFrameInterface.jdotk.
Definition idotk := NOFrameInterface.idotk.

Module NOFrame.
Section non_oriented_frame_def.

Variable R : rcfType.
Record t := mk {
  M :> 'M[R]_3 ;
  MO : M \is 'O[R]_3 }.
Parameter rowframe : t -> 'I_3 -> 'rV[R]_3.
Axiom rowframeE : forall f i, rowframe f i = row i (M f).
End non_oriented_frame_def.
End NOFrame.

Coercion matrix_of_noframe (R : rcfType) (f : NOFrame.t R) : 'M[R]_3 := 
  NOFrame.M f.

Definition rowframeE := NOFrame.rowframeE.
Notation "f '|,' i" := (NOFrame.rowframe f i)
  (at level 3, i at level 2, left associativity, format "f '|,' i") : ring_scope.

Section non_oriented_frame_properties.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types p : 'rV[R]_3.
Variable f : NOFrame.t R.

Lemma noframe_norm (k : 'I_3) : norm f|,k = 1.
Proof. rewrite rowframeE; apply norm_row_of_O; by case: f. Qed.

Local Notation "'i'" := (f |, 0).
Local Notation "'j'" := (f |, 1).
Local Notation "'k'" := (f |, 2%:R).

Lemma noframe_idotj : i *d j = 0.
Proof. rewrite !rowframeE; apply/orthogonalP; by case: f. Qed.

Lemma noframe_jdotk : j *d k = 0.
Proof. rewrite !rowframeE; apply/orthogonalP; by case: f. Qed.

Lemma noframe_idotk : i *d k = 0.
Proof. rewrite !rowframeE; apply/orthogonalP; by case: f. Qed.

Canonical noframe_is_noframe :=
  NOFrameInterface.mk (noframe_norm 0) (noframe_norm 1) (noframe_norm 2%:R)
  noframe_idotj noframe_jdotk noframe_idotk.

Lemma noframe_is_unit : matrix_of_noframe f \is a GRing.unit.
Proof. apply/orthogonal_unit. by case: f. Qed.

Lemma noframe_inv : (matrix_of_noframe f)^-1 = f^T.
Proof. rewrite -orthogonal_inv //; by case: f. Qed.

Lemma norm_icrossj : norm (i *v j) = 1.
Proof.
by rewrite norm_crossmul_normal // ?idotj // ?normi // normj.
Qed.

Definition noframe_sgn := \det f.

Lemma noframe_sgnE : noframe_sgn = i *d (j *v k).
Proof. by rewrite crossmul_triple /noframe_sgn [in LHS](col_mx3_rowE f) !rowframeE. Qed.

Lemma abs_noframe_sgn : `| noframe_sgn | = 1.
Proof. apply orthogonal_det; by case: f. Qed.

Lemma noframek : k = i *v j \/ k = - i *v j.
Proof.
move: abs_noframe_sgn; rewrite noframe_sgnE.
case: (lerP 0 (i *d (j *v k))) => [/ger0_norm ->|/ltr0_norm -> /eqP].
- rewrite dot_crossmulC => /dotmul1_inv H.
  by left; rewrite H // ?noframe_norm // norm_icrossj.
- rewrite eqr_oppLR => /eqP.
  rewrite dot_crossmulC => /dotmulN1_inv H.
  by right; rewrite crossmulNv H // ?opprK // ?noframe_norm // norm_icrossj.
Qed.

Lemma noframe_pos : (k == i *v j) = (noframe_sgn == 1).
Proof.
apply/idP/idP => [/eqP H|].
  by rewrite noframe_sgnE H dot_crossmulC dotmulvv norm_icrossj expr1n.
case: noframek => [/eqP //|] /eqP.
rewrite crossmulNv -eqr_oppLR noframe_sgnE dot_crossmulC => /eqP <-.
by rewrite dotmulNv dotmulvv noframe_norm expr1n Neqxx oner_eq0.
Qed.

Lemma noframe_neg : (k == - i *v j) = (noframe_sgn == - 1).
Proof.
apply/idP/idP => [/eqP H|].
- rewrite noframe_sgnE H dot_crossmulC crossmulNv dotmulvN dotmulvv.
  by rewrite norm_icrossj expr1n.
case: noframek => [|/eqP //] /eqP.
rewrite noframe_sgnE => /eqP ->.
rewrite double_crossmul dotmulvv normj expr1n scale1r (dotmulC j) idotj.
by rewrite scale0r subr0 dotmulvv normi expr1n -eqr_oppLR Neqxx oner_eq0.
Qed.

Lemma noframe_posP : k = i *v j -> j = k *v i /\ i = j *v k.
Proof.
move=> ->; split.
- rewrite crossmulC double_crossmul idotj scale0r add0r opprK.
  by rewrite dotmulvv noframe_norm expr1n scale1r.
- rewrite double_crossmul dotmulvv noframe_norm expr1n scale1r dotmulC.
  by rewrite idotj scale0r subr0.
Qed.

Lemma noframe_negP : k = - i *v j -> j = i *v k /\ i = k *v j.
Proof.
move=> ->; split.
- rewrite crossmulNv crossmulvN double_crossmul dotmulvv.
  by rewrite noframe_norm expr1n scale1r idotj scale0r add0r opprK.
- rewrite crossmulNv crossmulC crossmulvN opprK double_crossmul dotmulvv.
  by rewrite noframe_norm expr1n scale1r dotmulC idotj scale0r subr0.
Qed.

Lemma orthogonal_expansion_helper p :
  p *d i = 0 -> p *d j = 0 -> p *d k = 0 -> p = 0.
Proof.
do 3 rewrite dotmulE sum3E.
move=> H1 H2 H3.
have /eqP : p *m (col_mx3 i j k) ^T = 0.
  by rewrite col_mx3_mul dotmulE sum3E H1 dotmulE sum3E H2 dotmulE sum3E H3 row30.
rewrite mul_mx_rowfree_eq0; first by move/eqP.
apply/row_freeP; exists (col_mx3 i j k).
apply/eqP; by rewrite -orthogonalEC !rowframeE -col_mx3_rowE (NOFrame.MO _).
Qed.

Lemma orthogonal_expansion p :
  p = (p *d i) *: i + (p *d j) *: j + (p *d k) *: k.
Proof.
set y : 'rV[R]_3 := (p *d i) *: i + (p *d j) *: j + (p *d k) *: k.
suff /eqP : p - y = 0; first by rewrite subr_eq0 => /eqP.
apply orthogonal_expansion_helper.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv dotmulvv noframe_norm expr1n mulr1.
  rewrite 2!opprD 2!addrA subrr add0r dotmulZv (dotmulC j) idotj mulr0 oppr0.
  by rewrite dotmulZv (dotmulC k) idotk mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv idotj mulr0 add0r.
  rewrite dotmulZv dotmulvv noframe_norm expr1n mulr1 opprD addrA subrr.
  by rewrite dotmulZv (dotmulC k) jdotk mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv idotk mulr0 add0r dotmulZv.
  by rewrite jdotk mulr0 add0r dotmulZv dotmulvv noframe_norm expr1n mulr1 subrr.
Qed.

(* [oneill] lemma 3.5, p.110 *)
Lemma crossmul_noframe_sgn v v1 v2 v3 w w1 w2 w3 :
  v = v1 *: i + v2 *: j + v3 *: k ->
  w = w1 *: i + w2 *: j + w3 *: k ->
  v *v w = noframe_sgn *: ((v2 * w3 - v3 * w2) *: i -
                           (v1 * w3 - v3 * w1) *: j +
                           (v1 * w2 - v2 * w1) *: k).
Proof.
move=> -> ->.
rewrite !linearD /=.
rewrite !linearZ /=.
rewrite (crossmulC _ i).
rewrite (crossmulC _ j).
rewrite (crossmulC _ k).
rewrite ![in LHS]linearD /=.
rewrite (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 add0r.
case: noframek => e3e1e2.
- case: (noframe_posP e3e1e2) => Hj Hi.
  rewrite (_ : _ *v _ = v2 *: k); last by rewrite linearZ /= -e3e1e2.
  rewrite scalerN (_ : _ *v _ = - v3 *: j); last first.
    by rewrite linearZ /= crossmulC -Hj scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = - v1 *: k); last first.
    by rewrite linearZ /= crossmulC e3e1e2 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  rewrite (_ : _ *v _ = v3 *: i); last by rewrite linearZ /= -Hi.
  rewrite scalerN (_ : _ *v _ = v1 *: j); last by rewrite linearZ /= Hj.
  rewrite scalerN (_ : _ *v _ = - v2 *: i); last first.
    by rewrite linearZ /= crossmulC -Hi scaleNr scalerN.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  move/esym : noframe_pos; rewrite e3e1e2 eqxx => /eqP ->.
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
- case: (noframe_negP e3e1e2) => Hj Hi.
  rewrite (_ : _ *v _ = - v2 *: k); last first.
    by rewrite linearZ /= e3e1e2 crossmulNv scalerN scaleNr opprK.
  rewrite scaleNr opprK.
  rewrite (_ : _ *v _ = v3 *: j); last by rewrite linearZ /= -Hj.
  rewrite scalerN.
  rewrite (_ : _ *v _ = v1 *: k); last first.
    by rewrite linearZ /= crossmulC -crossmulNv -e3e1e2.
  rewrite scalerN.
  rewrite (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite oppr0 scaler0 addr0.
  rewrite (_ : _ *v _ = - v3 *: i); last first.
    by rewrite linearZ /= crossmulC -Hi scalerN scaleNr.
  rewrite scaleNr opprK.
  rewrite (_ : _ *v _ = - v1 *: j); last first.
    by rewrite linearZ /= crossmulC -Hj scalerN scaleNr.
  rewrite scaleNr opprK.
  rewrite (_ : _ *v _ = v2 *: i); last by rewrite linearZ /= -Hi.
  rewrite scalerN.
  rewrite (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite oppr0 scaler0 addr0.
  move: noframe_neg; rewrite {1}e3e1e2 eqxx => /esym/eqP ->.
  rewrite -![in LHS]addrA addrC -addrA.
  rewrite addrCA -addrA addrC ![in LHS]addrA -addrA; congr (_ + _); last first.
    by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w2).
  rewrite -addrA addrACA; congr (_ + _).
    by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w3).
  by rewrite !scalerA -scalerBl scalerN mulrN1 scaleNr opprK mulrC (mulrC w1).
Qed.

End non_oriented_frame_properties.

(* TODO: move? *)
Lemma mxE_col_row (R : Type) (M : 'M[R]_3) i j : M i j = (col j (row i M)) 0 0.
Proof. by rewrite !mxE. Qed.

Lemma colE (R : rcfType) (v : 'rV[R]_3) j : col j v = 'e_j *m v^T.
Proof.
apply/colP => i; rewrite {i}(ord1 i) !mxE coorE /dotmul mxE.
apply eq_bigr => /= i _; by rewrite !mxE eqxx /= mulrC.
Qed.

Lemma dotrow (R : rcfType) (M : 'M[R]_3) i j : M i j = 'e_j *d row i M.
Proof. by rewrite mxE_col_row /dotmul colE. Qed.

Module FrameInterface.
Section frame_interface.
Variable R : rcfType.
Record t (R : rcfType) : Type := mk {
  f : NOFrameInterface.t R ;
  icrossj : NOFrameInterface.i f *v NOFrameInterface.j f = NOFrameInterface.k f
}.
End frame_interface.
End FrameInterface.
Definition icrossj := FrameInterface.icrossj.

Module Frame.
Section frame.
Variable R : rcfType.

Record t := mk {
  noframe_of :> NOFrame.t R ;
  MSO : NOFrame.M noframe_of \is 'SO[R]_3}.

End frame.
End Frame.

Coercion noframe_of_frame (R : rcfType) (f : Frame.t R) : NOFrame.t R :=
  Frame.noframe_of f.

Section oriented_frame_properties.

Variable R : rcfType.
Variable f : Frame.t R.

Local Notation "'i'" := (f |, 0).
Local Notation "'j'" := (f |, 1).
Local Notation "'k'" := (f |, 2%:R).

(* TODO: useful? *)
Lemma frame_icrossj : i *v j = k.
Proof. move: (Frame.MSO f); rewrite !rowframeE; by move/SO_icrossj. Qed.

Lemma frame_icrossk : i *v k = - j.
Proof. move: (Frame.MSO f); rewrite !rowframeE; by move/SO_icrossk. Qed.

Lemma frame_jcrossk : j *v k = i.
Proof. move: (Frame.MSO f); rewrite !rowframeE; by move/SO_jcrossk. Qed.

Definition frame_of_SO (M : 'M[R]_3) (HM : M \is 'SO[R]_3) : Frame.t R :=
  @Frame.mk _ (NOFrame.mk (rotation_sub HM)) HM.

(* negative frame *)
Record nframe := mkNFrame {
  noframe_of_nframe :> NOFrame.t R ;
  nframeP : noframe_sgn noframe_of_nframe = -1}.

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

Coercion frame_of_tframe (R : rcfType) (f : TFrame.t R) : Frame.t R :=
  TFrame.frame_of f.

Definition xaxis R (f : TFrame.t R) := Line.mk (TFrame.o f) (f |, 0).
Definition yaxis R (f : TFrame.t R) := Line.mk (TFrame.o f) (f |, 1).
Definition zaxis R (f : TFrame.t R) := Line.mk (TFrame.o f) (f |, 2%:R).

Section canonical_frame.

Variable R : rcfType.

Definition can_noframe := NOFrame.mk (@orthogonal1 2 R).

Lemma can_frame_is_SO : NOFrame.M can_noframe \is 'SO[R]_3.
Proof. by rewrite /= rotationE det1 orthogonal1 eqxx. Qed.

Definition can_frame := Frame.mk can_frame_is_SO.

Lemma can_frame_1 : can_frame = 1 :> 'M_3.
Proof. by apply/matrix3P/and9P; split; rewrite !mxE. Qed.

(* TODO: usful? *)
Lemma rotation_can_frame (f : Frame.t R) i j : f i j = row j can_frame *d row i f.
Proof.
by rewrite /can_frame /= /can_noframe /= row1 dotrow.
Qed.

Definition can_tframe := TFrame.mk 0 can_frame. 

End canonical_frame.

Lemma basis_change (R : rcfType) (M : 'M[R]_3) (f : NOFrame.t R) (A : 'M[R]_3) :
  let i := f |, 0 in
  let j := f |, 1 in
  let k := f |, 2%:R in
  i *m M = A 0 0 *: i + A 0 1 *: j + A 0 2%:R *: k ->
  j *m M = A 1 0 *: i + A 1 1 *: j + A 1 2%:R *: k ->
  k *m M = A 2%:R 0 *: i + A 2%:R 1 *: j + A 2%:R 2%:R *: k ->
  let P := col_mx3 i j k in
  M = P^-1 * A * P.
Proof.
move=> i j k H1 H2 H3 P.
have : P * M = A * P.
  rewrite /P -mulmxE mulmx_col3 (col_mx3_rowE A) mulmx_col3 H1 H2 H3.
  congr col_mx3; apply/rowP => a; by rewrite !mxE sum3E !mxE.
rewrite -mulrA => <-.
rewrite mulrA mulVr ?mul1r // unitmxE unitfE /P -crossmul_triple.
by rewrite -normr_gt0 -noframe_sgnE (abs_noframe_sgn f) ltr01.
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
Proof. by rewrite /k dot_crossmulC crossmulvv dotmul0v. Qed.

Lemma jdotk : j *d k = 0.
Proof. by rewrite /k dot_crossmulCA crossmulvv dotmulv0. Qed.

Lemma normj : norm j = 1.
Proof.
rewrite /j; case: ifPn => iVi; first by rewrite norm_delta_mx.
rewrite norm_normalize //; apply: contra iVi.
by rewrite normalcomp_colinear // ?norm1_neq0 // colinear_sym.
Qed.

Lemma normk : norm k = 1.
Proof.
by rewrite /k norm_crossmul_normal // ?norm_normalize // ?normj // idotj // mulr0.
Qed.

Lemma is_O : col_mx3 i j k \is 'O[R]_3.
Proof.
apply/orthogonal3P;
  by rewrite !rowK /= normi normj normk idotj idotk jdotk !eqxx.
Qed.

Definition noframe := NOFrame.mk is_O.

Lemma is_SO : NOFrame.M noframe \is 'SO[R]_3.
Proof.
apply/rotation3P; by rewrite !rowK /= normi normj idotj !eqxx.
Qed.

Definition frame := Frame.mk is_SO.

End base1.

Section base1_lemmas.

Variable (R : rcfType).

(* NB: for information *)
Lemma je0 : j 'e_0 = 'e_1 :> 'rV[R]_3.
Proof. by rewrite /j colinear_refl. Qed.

Lemma ke0 : k 'e_0 = 'e_2%:R :> 'rV[R]_3.
Proof. by rewrite /k /j colinear_refl vece2 odd_perm301 -exprnP expr0 scale1r. Qed.

Variable u : 'rV[R]_3.

Lemma jN : j (- u) = j u.
Proof. by rewrite /j colinearNv normalcompvN. Qed.

Lemma kN : k (- u) = - k u.
Proof.
rewrite /k (_ : j (- u) = j u); last by rewrite -jN.
by rewrite crossmulNv.
Qed.

End base1_lemmas.
End Base1.

Canonical base1_is_noframe (R : rcfType) (u : 'rV[R]_3) (u1 : norm u = 1) :=
  NOFrameInterface.mk u1 (Base1.normj u1) (Base1.normk u1)
  (Base1.idotj u1) (Base1.jdotk u) (Base1.idotk u).

Module Base.
Section build_base.
Variables (R : rcfType) (u : 'rV[R]_3).

Definition i := if u == 0 then 'e_0 else normalize u.
Definition j := if u == 0 then 'e_1 else Base1.j i.
Definition k := if u == 0 then 'e_2%:R else Base1.k i.

Lemma normi : norm i = 1.
Proof.
rewrite /i; case: ifP => [_|/eqP/eqP ?]; first by rewrite normeE.
by rewrite norm_normalize.
Qed.

Parameter frame : 'rV[R]_3 -> Frame.t R.
Axiom frameE : frame u = Base1.frame normi.

Lemma iE : i = (frame u) |, 0.
Proof. by rewrite !rowframeE frameE rowK. Qed.
Lemma jE : j = (frame u) |, 1.
Proof.
rewrite !rowframeE frameE /= !rowK /= /j; case: ifP => // u0.
by rewrite /Base1.j /i u0 colinear_refl.
Qed.
Lemma kE : k = (frame u) |, 2%:R.
Proof.
rewrite !rowframeE frameE /= !rowK /= /k; case: ifP => // u0.
by rewrite /Base1.k /Base1.j /i u0 colinear_refl vecij.
Qed.

Lemma normj : norm j = 1.
Proof.
rewrite /j; case: ifP => [|/eqP/eqP u0]; first by rewrite normeE.
by rewrite Base1.normj // normi.
Qed.
Lemma normk : norm k = 1.
Proof.
rewrite /k; case: ifP => [|/eqP/eqP u0]; first by rewrite normeE.
by rewrite /k normk // normi.
Qed.

Lemma idotj : i *d j = 0.
Proof.
rewrite /i /j; case: ifP => [|/eqP/eqP u0]; first by rewrite dote2.
by rewrite Base1.idotj // norm_normalize.
Qed.
Lemma idotk : i *d k = 0.
Proof.
rewrite /i /k; case: ifP => [|/eqP/eqP u0]; first by rewrite dote2.
by rewrite Base1.idotk // norm_normalize.
Qed.
Lemma jdotk : j *d k = 0.
Proof.
rewrite /j /k; case: ifP => [|/eqP/eqP u0]; first by rewrite dote2.
by rewrite Base1.jdotk // norm_normalize.
Qed.

Lemma icrossj : i *v j = k.
Proof.
move: (frame_icrossj (frame u)).
rewrite !rowframeE frameE !rowK /= /i /j /k; case: ifP => // u0 _; by rewrite vecij.
Qed.
Lemma icrossk : i *v k = - j.
Proof.
move: (frame_icrossk (frame u)).
rewrite !rowframeE frameE !rowK /= /i /j /k; case: ifP => // u0 _; by rewrite vecik.
Qed.
Lemma jcrossk : j *v k = i.
Proof.
move: (frame_jcrossk (frame u)).
rewrite !rowframeE frameE !rowK /= /i /j /k; case: ifP => // u0 _; by rewrite vecjk.
Qed.

Lemma is_SO : col_mx3 i j k \is 'SO[R]_3.
Proof.
rewrite /i /j /k; case/boolP : (u == 0) => u0.
  apply/rotation3P; by rewrite !rowK /= !normeE !dote2 vecij !eqxx.
rewrite /i /j (negbTE u0); exact: (Base1.is_SO (norm_normalize u0)).
Qed.

End build_base.

Section build_base_lemmas.

Variable (R : rcfType) (u : 'rV[R]_3).

Lemma jZ p (p0 : 0 < p) : j (p *: u) = j u.
Proof.
rewrite /j /i; case/boolP : (u == 0) => u0.
  by rewrite scaler_eq0 u0 orbT.
by rewrite scaler_eq0 gtr_eqF //= (negbTE u0) normalizeZ.
Qed.

Lemma jN : j (- u) = j u.
Proof.
rewrite /j /i; case/boolP : (u == 0) => u0.
  by rewrite eqr_oppLR oppr0 u0.
by rewrite eqr_oppLR oppr0 (negbTE u0) normalizeN Base1.jN.
Qed.

Lemma jZN p (p0 : p < 0) : j (p *: u) = j u.
Proof.
rewrite /j; case/boolP : (u == 0) => u0.
  by rewrite scaler_eq0 u0 ltr_eqF //.
rewrite scaler_eq0 ltr_eqF //= (negbTE u0).
rewrite /i scaler_eq0 ltr_eqF; last assumption.
by rewrite (negbTE u0) /= -(opprK p) scaleNr /j /i normalizeN Base1.jN
  normalizeZ // -oppr_lt0 opprK.
Qed.

Lemma kZ p (p0 : 0 < p) : k (p *: u) = k u.
Proof.
rewrite /k scaler_eq0; case/boolP : (u == 0) => u0 /=.
  by rewrite orbT.
rewrite orbF gtr_eqF; last assumption.
by rewrite /i scaler_eq0 (negbTE u0) orbF (gtr_eqF p0) normalizeZ.
Qed.

Lemma kN : k (- u) = if u == 0 then 'e_2%:R else - k u.
Proof.
rewrite /k /i eqr_oppLR oppr0.
case/boolP : (u == 0) => // u0; by rewrite normalizeN Base1.kN.
Qed.

Lemma kZN p (p0 : p < 0) : k (p *: u) = if u == 0 then 'e_2%:R else - k u.
Proof.
rewrite /k /i scaler_eq0 (ltr_eqF p0) /=.
case/boolP : (u == 0) => u0 //; rewrite -(opprK p) scaleNr normalizeN.
by rewrite normalizeZ // -?oppr_lt0 ?opprK // Base1.kN.
Qed.

Lemma j_tr_mul (v : 'rV[R]_3) (v1 : norm v = 1) : j v *m v^T = 0.
Proof.
rewrite /j (negbTE (norm1_neq0 v1)) /Base1.j.
case: ifPn => [|_].
  case/colinearP => [|[_[k [Hk1 Hk2]]]].
    move/eqP/rowP/(_ ord0).
    rewrite !mxE !eqxx /= => /eqP; by rewrite oner_eq0.
  rewrite /i (negbTE (norm1_neq0 v1)) normalizeI // in Hk2.
  by rewrite dotmulP Hk2 dotmulvZ dote2 oner_eq0 mulr0 (mx11_scalar 0) mxE.
apply/eqP.
rewrite -scalemxAl scaler_eq0 {2}/i (negbTE (norm1_neq0 v1)) normalizeI //.
by rewrite normalcomp_mul_tr // orbT.
Qed.

Lemma k_tr_mul (v : 'rV[R]_3) (v1 : norm v = 1) : k v *m v^T *m v = 0.
Proof.
rewrite /k (negbTE (norm1_neq0 v1)) /Base1.k /Base1.j.
case: ifPn => [|_].
  case/colinearP => [|[_[k [Hk1 Hk2]]]].
    move/eqP/rowP/(_ ord0).
    rewrite !mxE !eqxx /= => /eqP; by rewrite oner_eq0.
  rewrite /i (negbTE (norm1_neq0 v1)) normalizeI // in Hk2.
  rewrite /i (negbTE (norm1_neq0 v1)) normalizeI //.
  rewrite {1}Hk2 crossmulZv vecij -2!scalemxAl {1}Hk2 linearZ /= -scalemxAr.
  by rewrite dotmulP dote2 scale_scalar_mx mulr0 mul_scalar_mx scale0r scaler0.
apply/eqP.
rewrite /normalize crossmulvZ -!scalemxAl scaler_eq0; apply/orP; right.
rewrite /normalcomp linearD /= crossmulvN 2!crossmulvZ crossmulvv 2!scaler0 subr0.
move: (axialcompE (v *v 'e_0) v).
rewrite v1 expr1n invr1 scale1r /i (negbTE (norm1_neq0 v1)) normalizeI // => <-.
by rewrite axialcomp_crossmul.
Qed.

End build_base_lemmas.

End Base.

Canonical base_is_noframe (R : rcfType) (u : 'rV[R]_3) (*(u0 : u != 0)*) :=
  NOFrameInterface.mk (Base.normi u) (Base.normj u) (Base.normk u)
  (Base.idotj u) (Base.jdotk u) (Base.idotk u).

Canonical frame_is_frame (R : rcfType) (u : 'rV[R]_3) (*(u0 : u != 0)*) :=
  @FrameInterface.mk _ (base_is_noframe u) (Base.icrossj u).

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
Proof. by rewrite FromToE mulmxE mulrV // noframe_is_unit. Qed.

Lemma trmx_FromTo A B : (A _R^ B)^T = B _R^ A.
Proof. apply/matrix3P/and9P; split; rewrite !mxE /=; by rewrite dotmulC. Qed.

Lemma FromTo_is_O A B : A _R^ B \is 'O[R]_3.
Proof.
rewrite orthogonalE FromToE trmx_mul.
rewrite {2}(noframe_inv B) trmxK -mulmxE mulmxA -(mulmxA _ (matrix_of_noframe B)^-1).
by rewrite mulVmx ?noframe_is_unit // mulmx1 -noframe_inv mulmxV // noframe_is_unit.
Qed.

Lemma FromTo_is_SO A B : A _R^ B \is 'SO[R]_3.
Proof.
by rewrite FromToE rpredM // ?Frame.MSO // noframe_inv rotationV Frame.MSO.
Qed.

Lemma FromTo_comp A B C : (C _R^ B) *m (B _R^ A) = C _R^ A.
Proof.
rewrite 2!FromToE -mulmxA (mulmxA _ B) mulVmx; last first.
  by rewrite unitmxE (rotation_det (Frame.MSO B)) unitr1.
rewrite mul1mx; apply/matrixP => i j.
rewrite !mxE dotmulE; apply/eq_bigr => k _.
rewrite 2![row _ _ _ _]mxE; congr (_ * _).
by rewrite noframe_inv mxE.
Qed.

End FromTo_properties.

Definition noframe_of_FromTo (R : rcfType) (A B : Frame.t R) : NOFrame.t R := 
  NOFrame.mk (FromTo_is_O A B).

Definition frame_of_FromTo (R : rcfType) (B A : Frame.t R) : Frame.t R :=
  @Frame.mk _ (noframe_of_FromTo B A) (FromTo_is_SO B A).

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
rewrite /j norm_normalize // normalcomp_colinear; last first.
  by rewrite -norm_eq0 normi oner_neq0.
apply: contra (abc); rewrite colinearvZ invr_eq0 norm_eq0 subr_eq0.
by rewrite eq_sym (negPf ab) /= colinear_sym.
Qed.

Lemma j_neq0 : j != 0.
Proof. by rewrite -norm_eq0 normj oner_neq0. Qed.

Lemma idotj : i *d j = 0.
Proof. by rewrite /= /i /j dotmulZv dotmulvZ dotmul_orthogonalize 2!mulr0. Qed.

Lemma jdotk : j *d k = 0.
Proof. by rewrite /k dot_crossmulCA crossmulvv dotmulv0. Qed.

Lemma idotk : i *d k = 0.
Proof. by rewrite /k dot_crossmulC crossmulvv dotmul0v. Qed.

Lemma normk : norm k = 1.
Proof. by rewrite norm_crossmul_normal // ?normi // ?normj // idotj. Qed.

Lemma k_neq0 : k != 0.
Proof. by rewrite -norm_eq0 normk oner_neq0. Qed.

Lemma is_O : col_mx3 i j k \is 'O[R]_3.
Proof.
apply/orthogonal3P;
  by rewrite !rowK /= normi normj normk idotj idotk jdotk !eqxx.
Qed.

Definition noframe := NOFrame.mk is_O.

Lemma is_SO : NOFrame.M noframe \is 'SO[R]_3.
Proof.
rewrite rotationE /= is_O /= -crossmul_triple double_crossmul dotmulvv normj.
by rewrite expr1n scale1r (dotmulC j) idotj scale0r subr0 dotmulvv normi expr1n.
Qed.

Definition frame := Frame.mk is_SO.

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
rewrite expr1n dot_crossmulCA crossmulvv dotmulv0 /matrix_of_noframe /=.
rewrite col_mx3E row3_row_mx (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite (mul_row_col 1%:M) mul_scalar_mx scale1r mul_scalar_mx scale0r addr0.
Qed.

Lemma k_l_r : triad.k l1 l2 l3 *m rot_l2r = triad.k r1 r2 r3.
Proof.
rewrite /rot_l2r /= mulmxA col_mx3_mul {1}/triad.k dotmulC dot_crossmulC.
rewrite crossmulvv dotmul0v {1}/triad.k -dot_crossmulC crossmulvv dotmulv0.
rewrite /matrix_of_noframe /= dotmulvv triad.normk // expr1n col_mx3E row3_row_mx.
do 2 rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite mul_scalar_mx scale1r.
Qed.

End transformation_given_three_points.
