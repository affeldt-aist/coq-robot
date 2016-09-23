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

Require Import aux angle euclidean3 skew vec_angle rot frame.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

(* NB: should go to euclidean3.v *)
Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Section line_line_intersection.

Variable R : rcfType.
Let point := 'rV[R]_3.
Implicit Types l : Line.t R.

Definition is_interpoint p l1 l2 :=
  (p \in (l1 : pred _)) && (p \in (l2 : pred _)).

Definition interpoint_param x l1 l2 :=
  let p1 := Line.point l1 in let p2 := Line.point l2 in
  let v1 := Line.vector l1 in let v2 := Line.vector l2 in
  \det (col_mx3 (p2 - p1) x (v1 *v v2)) / norm (v1 *v v2) ^+ 2. 

Definition interpoint_s l1 l2 := interpoint_param (Line.vector l1) l1 l2.

Definition interpoint_t l1 l2 := interpoint_param (Line.vector l2) l1 l2.

Lemma interpointP p l1 l2 : ~~ parallel l1 l2 ->
  let p1 := Line.point l1 in let p2 := Line.point l2 in
  let v1 := Line.vector l1 in let v2 := Line.vector l2 in
  is_interpoint p l1 l2 <->
  let s := interpoint_s l1 l2 in let t := interpoint_t l1 l2 in
  p1 + t *: v1 = p /\ p2 + s *: v2 = p.
Proof.
move=> l1l2 p1 p2 v1 v2; split; last first.
  move=> [Hs Ht]; rewrite /is_interpoint; apply/andP; split; apply/lineP;
  by [exists (interpoint_t l1 l2) | exists (interpoint_s l1 l2)].
case/andP => /lineP[t' Hs] /lineP[s' Ht] s t.
have Ht' : t' = interpoint_t l1 l2.
  have : t' *: (v1 *v v2) = (p2 - p1) *v v2.
    move: (Ht); rewrite Hs -/p1 -/p2 -/v1 -/v2 => /(congr1 (fun x => x - p1)).
    rewrite addrAC subrr add0r addrAC => /(congr1 (fun x => x *v v2)).
    by rewrite crossmulZv crossmulDl crossmulZv crossmulvv scaler0 addr0.
  move/(congr1 (fun x => x *d (v1 *v v2))).
  rewrite dotmulZv dotmulvv.
  move/(congr1 (fun x => x / (norm (v1 *v v2)) ^+ 2)).
  rewrite -mulrA divrr ?mulr1; last by rewrite unitfE sqrf_eq0 norm_eq0.
  by rewrite -dotmul_crossmulA crossmul_triple.
have Hs' : s' = interpoint_s l1 l2.
  have : s' *: (v1 *v v2) = (p2 - p1) *v v1.
    move: (Ht); rewrite Hs -/p1 -/p2 -/v1 -/v2 => /(congr1 (fun x => x - p2)).
    rewrite [in X in _ = X -> _]addrAC subrr add0r addrAC => /(congr1 (fun x => x *v v1)).
    rewrite [in X in _ = X -> _]crossmulZv crossmulDl crossmulZv crossmulvv scaler0 addr0.
    rewrite -(opprB p2 p1) (crossmulC v2) scalerN => /eqP.
    by rewrite crossmulNv eqr_opp => /eqP.
  move/(congr1 (fun x => x *d (v1 *v v2))).
  rewrite dotmulZv dotmulvv.
  move/(congr1 (fun x => x / (norm (v1 *v v2)) ^+ 2)).
  rewrite -mulrA divrr ?mulr1; last by rewrite unitfE sqrf_eq0 norm_eq0.
  by rewrite -dotmul_crossmulA crossmul_triple.
by rewrite /t /s -Ht' -Hs'.
Qed.

Definition intersection l1 l2 : option point :=
  if ~~ intersects l1 l2 then None
  else Some (Line.point l1 + interpoint_t l1 l2 *: Line.vector l1).

End line_line_intersection.

(* [ angeles2014: p.102-203] *)
Module Plucker.
Section plucker.
Variable R : rcfType.
Let vector := 'rV[R]_3.

Record array := mkArray {
  e : vector ; (* direction *)
  n : vector ; (* location, moment *)
  _ : e *d e == 1 ;
  _ : n *d e == 0 }.

End plucker.
End Plucker.

Coercion plucker_array_mx (R : rcfType) (p : Plucker.array R) :=
  row_mx (Plucker.e p) (Plucker.n p).

Section plucker_of_line.

Variable R : rcfType.
Implicit Types l : Line.t R.

Definition normalized_plucker_direction l :=
  let p1 := Line.point l in
  let p2 := Line.point2 l in
  (norm (p2 - p1))^-1 *: (p2 - p1).

Lemma normalized_plucker_directionP (l : Line.t R) : Line.vector l != 0 ->
  let e := normalized_plucker_direction l in e *d e == 1.
Proof.
move=> l0 /=.
rewrite /normalized_plucker_direction dotmulZv dotmulvZ dotmulvv.
rewrite /Line.point2 addrAC subrr add0r.
rewrite mulrA mulrAC expr2 mulrA mulVr ?unitfE ?norm_eq0 // mul1r.
by rewrite divrr // unitfE norm_eq0.
Qed.

Definition normalized_plucker_position l :=
  let p1 := Line.point l in
  p1 *v normalized_plucker_direction l.

Lemma normalized_plucker_positionP l :
  normalized_plucker_position l *d normalized_plucker_direction l == 0.
Proof.
rewrite /normalized_plucker_position /normalized_plucker_direction /Line.point2 addrAC subrr add0r crossmulvZ.
by rewrite dotmulvZ dotmulZv -dotmul_crossmulA crossmulvv dotmulv0 2!mulr0.
Qed.

Definition normalized_plucker l : 'rV[R]_6 :=
  row_mx (normalized_plucker_direction l) (normalized_plucker_position l).

Definition plucker_of_line l : 'rV[R]_6 :=
  let p1 := Line.point l in
  let p2 := Line.point2 l in
  row_mx (p2 - p1) (p1 *v (p2 - p1)).

Lemma normalized_pluckerP l :
  let p1 := Line.point l in
  let p2 := Line.point2 l in
  Line.vector l != 0 ->
  plucker_of_line l = norm (p2 - p1) *: normalized_plucker l.
Proof.
move=> p1 p2 l0.
rewrite /normalized_plucker /normalized_plucker_direction /normalized_plucker_position.
rewrite -/p1 -/p2 crossmulvZ -scale_row_mx scalerA.
by rewrite divrr ?scale1r // unitfE norm_eq0 /p2 /Line.point2 -/p1 addrAC subrr add0r.
Qed.

Lemma plucker_of_lineE l (l0 : Line.vector l != 0) :
  plucker_of_line l = norm (Line.point2 l - Line.point l) *:
  (Plucker.mkArray (normalized_plucker_directionP l0) (normalized_plucker_positionP l) : 'M__).
Proof.
rewrite /plucker_of_line /plucker_array_mx /=.
rewrite /normalized_plucker_direction /normalized_plucker_position crossmulvZ -scale_row_mx.
rewrite scalerA divrr ?scale1r //.
by rewrite unitfE norm_eq0 /Line.point2 addrAC subrr add0r.
Qed.

Definition plucker_eqn p l :=
  let p1 := Line.point l in let p2 := Line.point2 l in
  p *m (\S( p2 ) - \S( p1 )) + p1 *v (p2 - p1).

Lemma in_plucker p l : p \in (l : pred _)->
  let p1 := Line.point l in let p2 := Line.point2 l in
  plucker_eqn p l = 0.
Proof.
rewrite inE => /orP[/eqP -> p1 p2|].
  rewrite /plucker_eqn -/p1 mulmxBr linearB /= !skew_mxE crossmulvv.
  by rewrite 2!subr0 crossmulC addrC subrr.
case/andP => l0 H p1 p2; rewrite -/p1 in H.
rewrite /plucker_eqn.
rewrite /p2 /Line.point2 -/p1 addrAC subrr add0r skew_mxD addrAC subrr add0r.
rewrite skew_mxE crossmulC addrC -crossmulBl crossmulC -crossmulvN opprB; by apply/eqP.
Qed.

Definition homogeneous_plucker_eqn l :=
  let p1 := Line.point l in let p2 := Line.point2 l in
  col_mx (\S( p2 ) - \S( p1 )) (p1 *v (p2 - p1)).

Require Import rigid.

Lemma homogeneous_in_plucker p (l : Line.t R) : p \is 'hP[R] ->
  from_h p \in (l : pred _) ->
  let p1 := Line.point l in let p2 := Line.point2 l in
  p *m homogeneous_plucker_eqn l = 0.
Proof.
move=> hp /in_plucker Hp p1 p2 /=.
rewrite /homogeneous_plucker_eqn -/p1 -/p2.
move: (hp); rewrite hpoint_from_h => /eqP ->.
by rewrite (mul_row_col (from_h p) 1) mul1mx.
Qed.

End plucker_of_line.

(* TODO: move *)
Lemma k_e2 (R : rcfType) (f : Frame.t R) : Frame.k f *m f^T = 'e_2%:R.
Proof.
case: f => -[i j k ni nj nk /= ij jk ik Hsgn].
rewrite /Frame.k /= /matrix_of_noframe /= col_mx3_mul.
by rewrite dotmulC ik dotmulC jk dotmulvv nk expr1n -e2row.
Qed.

Lemma i_e0 (R : rcfType) (f : Frame.t R) : Frame.i f = 'e_0%:R *m f.
Proof.
case: f => -[i j k ni nj nk /= ij jk ik Hsgn].
rewrite /Frame.i /= /matrix_of_noframe /= e0row mulmx_row3_col3.
by rewrite scale1r !scale0r !addr0.
Qed.

Section denavit_hartenberg_homogeneous_matrix.

Variable R : rcfType.

Definition dh_mat (jangle : angle R) loffset llength (ltwist : angle R) : 'M[R]_4 :=
  hRx ltwist * hTx llength * hTz loffset * hRz jangle.

Definition dh_rot (jangle ltwist : angle R) := col_mx3
  (row3 (cos jangle) (sin jangle) 0)
  (row3 (cos ltwist * - sin jangle) (cos ltwist * cos jangle) (sin ltwist))
  (row3 (sin ltwist * sin jangle) (- sin ltwist * cos jangle) (cos ltwist)).

Lemma dh_rot_i (f1 f0 : Frame.t R) t a : f1 _R^ f0 = dh_rot t a ->
  Frame.i f1 *m f0^T = row3 (cos t) (sin t) 0.
Proof.
rewrite i_e0 -mulmxA FromToE noframe_inv => ->.
by rewrite /dh_rot e0row mulmx_row3_col3 !scale0r !addr0 scale1r.
Qed.

Lemma dh_matE jangle loffset llength ltwist : dh_mat jangle loffset llength ltwist =
  hom (dh_rot jangle ltwist)
  (row3 (llength * cos jangle) (llength * sin jangle) loffset).
Proof.
rewrite /dh_mat /hRz /hTz homM mulr1 mul0mx add0r /hTx homM mulr1 mulmx1 row3D.
rewrite !(add0r,addr0) /hRx homM addr0; congr hom; last first.
  rewrite /Rx mulmx_row3_col3 scale0r addr0 e2row 2!row3Z !(mulr1,mulr0).
  by rewrite row3D addr0 !(addr0,add0r).
rewrite /Rx /Rz -mulmxE mulmx_col3; congr col_mx3.
- by rewrite e0row mulmx_row3_col3 scale1r !scale0r !addr0.
- rewrite e2row mulmx_row3_col3 scale0r add0r 2!row3Z !mulr0 row3D.
  by rewrite !(addr0,mulr1,add0r).
- rewrite e2row mulmx_row3_col3 scale0r add0r 2!row3Z !mulr0 mulr1 row3D.
  by rewrite !(addr0,add0r) mulrN mulNr opprK.
Qed.

End denavit_hartenberg_homogeneous_matrix.

Section denavit_hartenberg_convention.

Variable R : rcfType.
Variable F0 F1 : TFrame.t R.
Definition From1To0 := locked (F1 _R^ F0).
Definition p1_in_0 : 'rV[R]_3 := (TFrame.o F1 - TFrame.o F0) *m (can_frame R) _R^ F0.

Hypothesis dh1 : Frame.i F1 *d Frame.k F0 = 0.
Hypothesis dh2 : exists p, is_interpoint p (xaxis F1) (zaxis F0).

(* [spong] an homogeneous transformation that satisfies dh1 and dh2 
   can be represented by means of only four parameters *)
Lemma dh_mat_correct : exists alpha theta d a,
  hom From1To0 p1_in_0 = dh_mat theta d a alpha.
Proof.
have H1 : From1To0 0 2%:R = 0.
  by rewrite /From1To0 -lock /FromTo mxE row0_frame row2_frame.
have [H2a H2b] : From1To0 0 0 ^+ 2 + From1To0 0 1 ^+ 2 = 1 /\
  From1To0 1 2%:R ^+ 2 + From1To0 2%:R 2%:R ^+ 2 = 1.
  move: (norm_row_of_O (FromTo_is_O F1 F0) 0) => /= /(congr1 (fun x => x ^+ 2)).
  rewrite expr1n -dotmulvv dotmulE sum3E [_ 0 2%:R]mxE.
  move: (H1); rewrite {1}/From1To0 -lock => ->.
  rewrite  mulr0 addr0 -!expr2 => H1a.
  split.
    rewrite [_ 0 0]mxE [_ 0 1]mxE in H1a.
    by rewrite /From1To0 -lock.
  move: (norm_col_of_O (FromTo_is_O F1 F0) 2%:R) => /= /(congr1 (fun x => x ^+ 2)).
  rewrite expr1n -dotmulvv dotmulE sum3E 2![_ 0 0]mxE.
  move: (H1); rewrite {1}/From1To0 -lock => ->.
  by rewrite mulr0 add0r -!expr2 tr_col [_ 0 1]mxE [_ 0 2%:R]mxE /From1To0 -lock !mxE.
have [theta [alpha [H00 [H01 [H22 H12]]]]] : exists theta alpha,
  From1To0 0 0 = cos theta /\ From1To0 0 1 = sin theta /\ 
  From1To0 2%:R 2%:R = cos alpha /\ From1To0 1 2%:R = sin alpha.
  case/sqrD1_cossin : H2a => theta Htheta.
  rewrite addrC in H2b.
  case/sqrD1_cossin : H2b => alpha Halpha.
  exists theta, alpha; by intuition.

move/orthogonalPcol : (FromTo_is_O F1 F0) => /(_ 1 2%:R) /=.
rewrite dotmulE sum3E !tr_col 2![_ 0 0]mxE [_ 2%:R 0]mxE.
move: (H1); rewrite {1}/From1To0 -lock => ->.
rewrite mulr0 add0r [_ 0 1]mxE [_ 1 1]mxE [_ 0 1]mxE [_ 2%:R 1]mxE.
move: (H12); rewrite {1}/From1To0 -lock => ->.
rewrite 2![_ 0 2%:R]mxE [_ 1 2%:R]mxE [_ 2%:R 2%:R]mxE.
move: (H22); rewrite {1}/From1To0 -lock => -> /eqP.
rewrite addr_eq0 => /eqP H11_H21.

move/orthogonalPcol : (FromTo_is_O F1 F0) => /(_ 2%:R 0) /=.
rewrite dotmulE sum3E !tr_col 3![_ 0 0]mxE [_ 2%:R 0]mxE.
move: (H1); rewrite {1}/From1To0 -lock => ->.
rewrite mul0r add0r [_ 0 1]mxE [_ 2%:R 1]mxE.
move: (H12); rewrite {1}/From1To0 -lock => ->.
rewrite 2![_ 0 1]mxE [_ 0 2%:R]mxE [_ 2%:R 2%:R]mxE.
move: (H22);   rewrite {1}/From1To0 -lock => ->.
rewrite 2![_ 0 2%:R]mxE => /eqP.
rewrite addr_eq0 => /eqP H10_H20.

move: (norm_col_of_O (FromTo_is_O F1 F0) 1) => /= /(congr1 (fun x => x ^+ 2)).
rewrite expr1n sqr_norm sum3E tr_col [_ 0 0]mxE [_ 1 0]mxE.
move: (H01); rewrite {1}/From1To0 -lock => ->.
rewrite [_ 0 1]mxE [_ 1 1]mxE [_ 0 2%:R]mxE [_ 1 2%:R]mxE.
move/eqP. rewrite -addrA eq_sym addrC -subr_eq -cos2sin2. move/eqP.
move/(congr1 (fun x => (sin alpha)^+2 * x)).
rewrite mulrDr -(@exprMn _ _ (sin alpha) (_ 1 1)) (mulrC _ (_ 1 1)) H11_H21.
rewrite sqrrN exprMn (mulrC _ (_ ^+ 2)) -mulrDl cos2Dsin2 mul1r => /esym sqr_H21.

move: (norm_col_of_O (FromTo_is_O F1 F0) 0) => /= /(congr1 (fun x => x ^+ 2)).
rewrite sqr_norm sum3E 2![_ 0 0]mxE.
move: (H00); rewrite {1}/From1To0 -lock => ->.
rewrite expr1n [_ 0 1]mxE [_ 1 0]mxE [_ 0 2%:R]mxE [_ 2%:R 0]mxE.
move=> H10_H20_save; move: (H10_H20_save).
move/eqP. rewrite -addrA eq_sym addrC -subr_eq -sin2cos2. move/eqP.
move/(congr1 (fun x => (sin alpha)^+2 * x)).
rewrite mulrDr -(@exprMn _ _ (sin alpha) (_ 1 0)) H10_H20 sqrrN.
rewrite exprMn -mulrDl cos2Dsin2 mul1r => /esym sqr_H20.

have : \det From1To0 = 1 by apply rotation_det; rewrite /From1To0 -lock; apply: FromTo_is_SO.
rewrite {1}/From1To0 -lock det_mx33.
move: (H1); rewrite {1}/From1To0 -lock => ->; rewrite mul0r addr0.
move: (H00); rewrite {1}/From1To0 -lock => ->.
move: (H01); rewrite {1}/From1To0 -lock => ->.
move: (H12); rewrite {1}/From1To0 -lock => ->.
move: (H22); rewrite {1}/From1To0 -lock => -> Hrot.

have H4 : From1To0 = dh_rot theta alpha.
  rewrite /dh_rot [LHS]col_mx3_rowE row_row3 H00 H01 2!row_row3 H1 H12 H22.
  case/boolP : (sin alpha == 0) => sa0.
    move/eqP in sqr_H21; rewrite (eqP sa0) expr0n mul0r sqrf_eq0 in sqr_H21.
    move/eqP in sqr_H20; rewrite (eqP sa0) expr0n mul0r sqrf_eq0 in sqr_H20.
    rewrite (eqP sqr_H20) mul0r add0r (eqP sqr_H21) mul0r subr0 in Hrot.
    rewrite !(mulrA,mulrN) -mulrBl in Hrot.
    rewrite {4}/From1To0 -lock (eqP sqr_H21) (eqP sa0) !(mul0r,oppr0).
    rewrite {3}/From1To0 -lock (eqP sqr_H20).
    move/eqP : (sa0) => /sin0cos1 /eqP.
    rewrite eqr_norml ler01 andbT.

    move: (norm_row_of_O (FromTo_is_O F1 F0) 1) => /= /(congr1 (fun x => x ^+ 2)).
    rewrite expr1n sqr_norm sum3E [_ 0 0]mxE [_ 0 1]mxE [_ 0 2%:R]mxE.
    move: (H12); rewrite {1}/From1To0 -lock => ->; rewrite (eqP sa0) expr0n addr0.
    move=> H10_H11.

    case/orP => /eqP ca1.
      rewrite ca1 !mul1r.
      move: Hrot; rewrite ca1 mulr1 => Hrot.
      move: H10_H20_save; rewrite (eqP sqr_H20) expr0n addr0 => /eqP. 
      rewrite eq_sym addrC -subr_eq -sin2cos2 eq_sym eqf_sqr => /orP[] H10.
        move/eqP : Hrot.
        rewrite (eqP H10) -expr2.
        move: H10_H11; rewrite (eqP H10) => /eqP; rewrite eq_sym -addrC -subr_eq -cos2sin2 eq_sym.
        rewrite eqf_sqr => /orP[] /eqP H11.
          rewrite {2}/From1To0 -lock H11 {1}/From1To0 -lock (eqP H10).
          rewrite -expr2 sin2cos2 opprB addrA subr_eq -!mulr2n eqr_muln2r /=.
          rewrite -sqr_normr sqrp_eq1 ?normr_ge0 //.
          move/eqP/cos1sin0 => ->.
          by rewrite oppr0.
        rewrite H11 mulrN -expr2 cos2sin2 opprB addrAC subrr add0r.
        by rewrite eq_sym -subr_eq0 opprK (_ : 1 + 1 = 2%:R) // pnatr_eq0.
      move: H10_H11.
      rewrite (eqP H10) sqrrN => /eqP; rewrite eq_sym addrC -subr_eq -cos2sin2 eq_sym.
      rewrite eqf_sqr => /orP[] /eqP H11.
        by rewrite /From1To0 -lock (eqP H10) H11.
      move/eqP : Hrot.
      rewrite (eqP H10) mulrN opprK -expr2 H11 mulrN -expr2 eq_sym -subr_eq -cos2sin2.
      rewrite -subr_eq0 opprK -mulr2n mulrn_eq0 /= sqrf_eq0 => /eqP ct0.
      by rewrite /From1To0 -lock (eqP H10) H11 ct0 oppr0.
    rewrite ca1 !mulN1r opprK.
    move: Hrot.
    rewrite ca1 mulrN1 opprB => Hrot.

    move: H10_H20_save.
    rewrite (eqP sqr_H20) expr0n addr0 => /eqP; rewrite eq_sym addrC -subr_eq.
    rewrite -sin2cos2 eq_sym.
    rewrite eqf_sqr => /orP[] /eqP H10.
      move: H10_H11.
      rewrite H10 => /eqP; rewrite eq_sym addrC -subr_eq -cos2sin2 eq_sym.
      rewrite eqf_sqr => /orP[] /eqP H11.
        move: Hrot.
        rewrite H10 H11 -!expr2 => /eqP; rewrite cos2sin2 opprB addrA -mulr2n.
        rewrite subr_eq eqr_muln2r /= -sqr_normr.
        rewrite sqrp_eq1 ?normr_ge0 // => /eqP/sin1cos0 => ct0.
        by rewrite {1 2}/From1To0 -lock H10 H11 ct0 oppr0.
      by rewrite /From1To0 -lock H10 H11.
    move: H10_H11.
    rewrite H10 => /eqP; rewrite sqrrN addrC eq_sym -subr_eq -cos2sin2 eq_sym.
    rewrite eqf_sqr => /orP[] /eqP H11.
      move: Hrot.
      rewrite H10 H11 mulrN -!expr2 -opprD addrC cos2Dsin2 => /eqP.
      by rewrite eq_sym -subr_eq0 opprK (_ : 1 + 1 = 2%:R) // pnatr_eq0.
    move: Hrot.
    rewrite H10 H11 !mulrN -!expr2 opprK cos2sin2 addrCA -opprD -mulr2n => /eqP.
    rewrite -opprB eqr_oppLR.
    rewrite subr_eq addrC subrr mulrn_eq0 /=.
    rewrite -sqr_normr sqrf_eq0 normrE => /eqP st0.
    by rewrite st0 /From1To0 -lock H10 st0 oppr0 H11.

  move/eqP : sqr_H20.
  rewrite -exprMn eqf_sqr => /orP[/eqP H20|H20].
    rewrite {3}/From1To0 -lock H20.
    move: H10_H20.
    rewrite H20 mulrCA -mulrN.
    move/(congr1 (fun x => (sin alpha)^-1 * x)).
    rewrite !mulrA mulVr ?mul1r ?unitfE // => H10.
    rewrite {1}/From1To0 -lock H10 -mulrN.
    move/eqP : sqr_H21.
    rewrite -exprMn eqf_sqr => /orP[H21|/eqP H21]; last first.
      rewrite {2}/From1To0 -lock H21 -mulNr.
      move: H11_H21.
      rewrite H21 [in X in X -> _]mulNr opprK (mulrC _ (sin alpha)).
      move/(congr1 (fun x => (sin alpha)^-1 * x)).
      rewrite !mulrA mulVr ?mul1r ?unitfE // => H11.
      by rewrite {1}/From1To0 -lock H11 (mulrC (cos theta) (cos alpha)).
    move: H11_H21.
    rewrite (eqP H21).
    rewrite -mulrA -mulrN (mulrC _ (sin alpha)).
    move/(congr1 (fun x => (sin alpha)^-1 * x)).
    rewrite !mulrA mulVr ?unitfE // !mul1r => H11.
    move: Hrot.
    rewrite H11 (eqP H21) H10 !mulNr opprK H20 -(mulrA (cos theta)) -expr2 mulrAC.
    rewrite -expr2 -opprD (mulrC (cos theta) (_ ^+ 2)) -mulrDl cos2Dsin2 mul1r.
    rewrite mulrN -expr2 mulrAC -expr2 mulrAC -expr2 -mulrDl (addrC (_ ^+ 2)).
    rewrite cos2Dsin2 mul1r -expr2 sin2cos2 addrCA -opprD -mulr2n => /eqP.
    rewrite subr_eq addrC -subr_eq subrr eq_sym mulrn_eq0 /= sqrf_eq0 => ct0.
    rewrite {1}/From1To0 -lock H11 {1}/From1To0 -lock (eqP H21).
    by rewrite (eqP ct0) !(mulr0,mul0r) oppr0.
  rewrite {3}/From1To0 -lock (eqP H20).
  rewrite (eqP H20) mulrN opprK mulrCA in H10_H20.
  move/(congr1 (fun x => (sin alpha)^-1 * x)) : H10_H20.
  rewrite !mulrA mulVr ?unitfE // !mul1r => H10.
  rewrite {1}/From1To0 -lock H10.
  move/eqP : sqr_H21.
  rewrite -exprMn eqf_sqr => /orP[H21|/eqP H21]; last first.
    rewrite {2}/From1To0 -lock H21 -mulNr.
    move: H11_H21.
    rewrite H21 [in X in X -> _]mulNr opprK (mulrC _ (sin alpha)).
    move/(congr1 (fun x => (sin alpha)^-1 * x)).
    rewrite !mulrA mulVr ?mul1r ?unitfE // => H11.
    rewrite {1}/From1To0 -lock H11.
    move: Hrot.
    rewrite H11 H21 H10 !mulNr opprK (eqP H20) -(mulrA (cos theta)) -expr2 mulrAC.
    rewrite -expr2 (mulrC (cos theta) (_ ^+ 2)) -mulrDl cos2Dsin2 mul1r.
    rewrite mulNr mulrAC -!expr2 (mulrAC (cos alpha)) -expr2 -opprD -mulrDl.
    rewrite (addrC _ (cos _ ^+ 2)) cos2Dsin2 mul1r mulrN -expr2 cos2sin2 -addrA -opprD.
    rewrite -mulr2n => /eqP; rewrite subr_eq addrC -subr_eq subrr eq_sym mulrn_eq0 /=.
    rewrite sqrf_eq0 => /eqP st0.
    by rewrite st0 !(mulr0,oppr0) (mulrC (cos theta)).
  rewrite {2}/From1To0 -lock (eqP H21).
  move: H11_H21.
  rewrite (eqP H21) -mulrA -mulrN (mulrC _ (sin alpha)). 
  move/(congr1 (fun x => (sin alpha)^-1 * x)).
  rewrite !mulrA mulVr ?mul1r ?unitfE // => H11.
  rewrite {1}/From1To0 -lock H11.
  move: Hrot.
  rewrite H11 (eqP H21) (eqP H20) H10 mulNr -(mulrA _ (cos alpha)) -expr2.
  rewrite mulrAC -expr2 -opprD (mulrC (cos theta) (_ ^+ 2)) -mulrDl cos2Dsin2 mul1r mulrN.
  rewrite -expr2 mulNr mulrAC -expr2 (mulrAC (cos alpha)) -expr2 -opprD -mulrDl.
  rewrite (addrC (sin _ ^+ 2)) cos2Dsin2 mul1r mulrN -expr2 -opprD cos2Dsin2 => /eqP.
  by rewrite -subr_eq0 -opprD eqr_oppLR oppr0 (_ : 1 + 1 = 2%:R) // pnatr_eq0.
have [d [a H5]] : exists d a,
  TFrame.o F1 = TFrame.o F0 + d *: (Frame.k F0) + a *: (Frame.i F1).
  case: dh2 => p.
  rewrite /is_interpoint => /andP[/lineP[k1 /= Hk1] /lineP[k2 /= Hk2]].
  exists k2, (- k1).
  rewrite -Hk2.
  by apply/eqP; rewrite Hk1 scaleNr addrK.
exists alpha, theta, d, a.
rewrite dh_matE -H4; congr hom.
suff -> : p1_in_0 = (* TFrame.o F1 w.r.t. 0 *)
    0 (* TFrame.o F0 w.r.t. 0*) + d *: 'e_2%:R (* (Frame.k F0) in 0 *)
      + a *: row3 (cos theta) (sin theta) 0 (* (Frame.i F1) in 0*).
  by rewrite add0r e2row 2!row3Z row3D !(mulr0,add0r,mulr1,addr0).
move/eqP : H5.
rewrite -addrA addrC -subr_eq.
move/eqP.
move/(congr1 (fun x => x *m F0^T)).
rewrite [in X in _ = X -> _]mulmxDl -scalemxAl k_e2.
rewrite -scalemxAl (@dh_rot_i _ _ _ theta alpha); last first.
  by rewrite {1}/From1To0 -lock in H4.
rewrite add0r => <-.
by rewrite -FromTo_from_can.
Qed.

End denavit_hartenberg_convention.

(* TODO: in progress, [angeles] p.141-142 *)
Module Joint.
Section joint.
Variable R : rcfType.
Let vector := 'rV[R]_3.
Record t := mk {
  vaxis : vector ;
  norm_vaxis : norm vaxis = 1 ;
  angle : angle R (* between to successive X axes *) }.
End joint.
End Joint.

Module Link.
Section link.
Variable R : rcfType.
Record t := mk {
  length : R ; (* nonnegative, distance between to successive joint axes *)
  offset : R ; (* between to successive X axes *)
  twist : angle R (* or twist angle, between two successive Z axes *) }.
End link.
End Link.
(* NB: Link.offset, Joint.angle, Link.length, Link.twist are called
   Denavit-Hartenberg parameters *)

Section open_chain.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := TFrame.t R.
Let joint := Joint.t R.
Let link := Link.t R.

(* u is directed from p1 to p2 *)
Definition directed_from_to (u : vector) (p1 p2 : point) : bool :=
  0 <= cos (vec_angle u (p2 - p1)).

Axiom angle_between_lines : 'rV[R]_3 -> 'rV[R]_3 -> 'rV[R]_3 -> angle R.

Variable n' : nat.
Let n := n'.+1.

(* 1. Zi is the axis of the ith joint *)
Definition joint_axis (frames : frame ^ n.+1) (joints : joint ^ n) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in 
  (Joint.vaxis (joints i) == Frame.k (frames i')) ||
  (Joint.vaxis (joints i) == - Frame.k (frames i')).

(* 2. Xi is the common perpendicular to Zi-1 and Zi *)
Definition X_Z (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in 
  let predi : 'I_n.+1 := inord i.-1 in 
  let: (o_predi, z_predi) := let f := frames predi in (TFrame.o f, Frame.k f) in
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, Frame.i f, Frame.k f) in
  if intersects (zaxis (frames predi)) (zaxis (frames i')) then
    x_i == z_predi *v z_i 
  else if colinear z_predi z_i then
    o_predi \in (xaxis (frames i') : pred _)
  else
    (x_i _|_ z_predi, z_i) && (* Xi is the common perpendicular to Zi-1 and Zi *)
    directed_from_to x_i o_predi o_i (* directed from Zi-1 to Zi *).

(*Definition common_normal_xz (i : 'I_n) :=
  (framej (frames i.-1)) _|_ (framek (frames i)), (framei (frames i.-1)).*)
(* x_vec (frames i.-1) _|_ plane (z_vec (frames i.-1)),(z_vec (frames i)) *)

(* 3. distance Zi-1<->Zi = link length *)
Definition link_length (frames : frame ^ n.+1) (links : link ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  Link.length (links i') = distance_between_lines (zaxis (frames i')) (zaxis (frames succi)).

Definition link_offset (frames : frame ^ n.+1) (links : link ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (o_succi, x_succi) := let f := frames succi in (TFrame.o f, Frame.i f) in 
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, Frame.i f, Frame.k f) in 
  if intersection (zaxis (frames i')) (xaxis (frames succi)) is some o'_i then
    (norm (o'_i - o_i)(*the Zi-coordiante of o'_i*) == Link.offset (links i')) &&
    (`| Link.offset (links i') | == distance_between_lines (xaxis (frames i')) (xaxis (frames succi)))
  else
    false (* should not happen since Zi always intersects Xi.+1 (see condidion 2.) *).

Definition link_twist (frames : frame ^ n.+1) (links : link ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (x_succi, z_succi) := let f := frames succi in (Frame.i f, Frame.k f) in 
  let z_i := Frame.k (frames i') in 
  Link.twist (links i') == angle_between_lines z_i z_succi x_succi.
  (*angle measured about the positive direction of Xi+1*)

Definition joint_angle (frames : frame ^ n.+1) (joints : joint ^ n) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: x_succi := Frame.i (frames succi) in 
  let: (x_i, z_i) := let f := frames i' in (Frame.i f, Frame.i f) in 
  Joint.angle (joints i) = angle_between_lines x_i x_succi z_i.
  (*angle measured about the positive direction of Zi*)

(* n + 1 links numbered 0,..., n (at least two links: the manipulator base and the end-effector)
   n joints
     the ith joint couples the i-1th and the ith link
   n + 1 frames numbered F_1, F_2, ..., F_n+1 (F_i attached to link i-1)
   *)
Record chain := mkChain {
  links : {ffun 'I_n.+1 -> link} ;
  frames : {ffun 'I_n.+1 -> frame} ;
  joints : {ffun 'I_n -> joint} ; (* joint i located between links i and i+1 *)
  (* the six conditions [angeles] p.141-142 *)
  _ : forall i, joint_axis frames joints i ;
  _ : forall i, X_Z frames i ;
  _ : forall i, link_length frames links i ;
  _ : forall i, link_offset frames links i ;
  _ : forall i, link_twist frames links i ;
  _ : forall i, joint_angle frames joints i
  (* this leaves the n.+1th frame unspecified (on purpose) *)
  }.

(*
Variables chain : {ffun 'I_n -> frame * link * joint}.
Definition frames := fun i => (chain (insubd ord0 i)).1.1.
Definition links := fun i => (chain (insubd ord0 i)).1.2.
Definition joints := fun i => (chain (insubd ord0 i)).2.
*)

(*
Definition before_after_joint (i : 'I_n) : option (link * link):=
  match ltnP O i with
    | LtnNotGeq H (* 0 < i*) => Some (links i.-1, links i)
    | GeqNotLtn H (* i <= 0*) => None
  end.
 *)

End open_chain.

(* SCARA robot manipulator as an example *)
Section scara.

Require Import reals.

Variable R : realType.
Let vector := 'rV[R]_3.

Variable theta1 : angle R.
Variable a1 : R.
Variable theta2 : angle R.
Variable a2 : R.
Variable d3 : R.
Variable theta4 : angle R.
Variable d4 : R.

Definition A1 := hom (Rz theta1) (row3 (a1 * cos theta1) (a1 * sin theta1) 0).
Definition A2 := hom (Rz theta2) (row3 (a2 * cos theta2) (a2 * sin theta2) 0).
Definition A3 := hTz d3.
Definition A4 := hom (Rz theta4) (row3 0 0 d4).

Definition rotA := Rz (theta1 + theta2 + theta4).

Definition transA := row3
  (a2 * cos (theta2 + theta1) + a1 * cos theta1)
  (a2 * sin (theta2 + theta1) + a1 * sin theta1)
  (d4 + d3).

(* [spong] p. 81, eqn. 3.49 *)
Lemma A_compute : A4 * A3 * A2 * A1 = hom rotA transA.
Proof.
rewrite /A4 /A3.
rewrite homM mulr1 mulmx1 row3D. Simp.r.
rewrite /A2.
rewrite homM RzM mulmx_row3_col3 !scale0r !add0r e2row !row3Z row3D. Simp.r.
rewrite homM RzM addrC (addrC _ theta2) addrA; congr hom.
rewrite mulmx_row3_col3 e2row !row3Z !row3D. Simp.r.
by rewrite -!mulrA -mulrBr -cosD -mulrDr (addrC (_ * sin theta1)) -sinD.
Qed.

Require Import screw.

Section scara_screw.

Variable l0 : R.

(* initial configuration *)
Definition g0 := hom 1 (row3 (a1 + a2) 0 l0).

Definition w1 : vector := 'e_2%:R.
Definition w2 : vector := 'e_2%:R.
Definition w3 : vector := 'e_2%:R.

(* axis points *)
Definition q1 : vector := 'e_2%:R.
Definition q2 : vector := row3 a1 0 0.
Definition q3 : vector := row3 (a1 + a2) 0 0.

Definition t1 := rjoint_twist w1 q1.
Definition t2 := rjoint_twist w2 q2.
Definition t3 : Twist.t R := Twist.mk 'e_2%:R 0. (* TODO: notation for prismatic joint? *)

Goal - w1 *v q1 = 0.
by rewrite crossmulNv crossmulvv oppr0.
Abort.
Goal - w2 *v q2 = - row3 0 a1 0.
rewrite /w2 /q2 e2row crossmulNv crossmulE !mxE /=. Simp.r.
done.
Abort.

Definition t4 := rjoint_twist w3 q3.

Goal -w3 *v q3 = - row3 0 (a1 + a2) 0.
rewrite /w3 /q3 e2row crossmulNv crossmulE !mxE /=. Simp.r.
done.
Abort.

Definition g := `e$(theta4, t4) *
                `e$(Rad.angle_of d3, t3) *
                `e$(theta2, t2) *
                `e$(theta1, t1).

Definition g_old := `e$(theta1, t1) *
                `e$(theta2, t2) *
                `e$(Rad.angle_of d3, t3) *
                `e$(theta4, t4).

Lemma H1 : `e$(theta1, t1) = hRz theta1.
Proof.
rewrite /t1 /rjoint_twist crossmulNv crossmulvv oppr0 etwist_Rz; last first.
  by rewrite -norm_eq0 normeE oner_eq0.
by rewrite -Rz_eskew.
Qed.

(* TODO: generalize *)
Lemma point_axis_twist (d : R) :
  Line.point (axis \T((- 'e_2%:R *v row3 d 0 0), 'e_2%:R)) = row3 d 0 0.
Proof.
rewrite {1}/axis ang_of_twistE.
rewrite (_ : 'e_2%:R == 0 = false) /=; last first.
  apply/negP/negP; by rewrite -norm_eq0 normeE oner_eq0.
rewrite normeE expr1n invr1 scale1r lin_of_twistE crossmulNv crossmulvN.
rewrite double_crossmul dotmulvv normeE expr1n scale1r /w2 /q2 e2row.
rewrite dotmulE sum3E !mxE /=. by Simp.r.
Qed.

Lemma H2_helper th d :
  `e$(th, Twist.mk (- w2 *v row3 d 0 0) w2) = hom (Rz th) (row3 (d * (1 - cos th)) (- d * sin th) 0).
Proof.
rewrite etwistE.
rewrite (_ : w2 == 0 = false); last first.
  apply/negP/negP; by rewrite -norm_eq0 normeE oner_eq0.
rewrite pitch_perp ?normeE // mulr0 scale0r add0r.
rewrite point_axis_twist.
rewrite -Rz_eskew.
congr hom.
rewrite mulmxBr mulmx1 mulmx_row3_col3 !scale0r !addr0 row3Z row3N row3D.
Simp.r.
by rewrite mulrBr mulr1.
Qed.

Lemma H2 : `e$(theta2, t2) = hom (Rz theta2) (row3 (a1 * (1 - cos theta2)) (- a1 * sin theta2) 0).
Proof. by rewrite /t2 H2_helper. Qed.

Lemma H3 : `e$(Rad.angle_of d3, t3) = hTz d3.
Proof.
rewrite etwistE eqxx eskew_v0 Rad.angle_ofK.
  rewrite e2row row3Z. Simp.r. done.
admit.
Admitted.

Lemma H4 : `e$(theta4, t4) = hom (Rz theta4)
  (row3 ((a1 + a2) * (1 - cos theta4)) (- (a1 + a2) * sin theta4) 0).
Proof. by rewrite /t4 /q3 H2_helper. Qed.

Definition tR' := (row3 (- a1 * cos theta1 - a2 * cos (theta1 + theta2))
       (a1 * sin theta1 + a2 * sin (theta1 + theta2))
       (l0 + d3)).

Lemma H1234 : g = hom rotA transA.
Proof.
rewrite /g.
rewrite H1 H2 H3 H4.
rewrite homM mulr1 mulmx1 row3D. Simp.r.
rewrite homM RzM mulmx_row3_col3 e2row !row3Z !row3D. Simp.r.
rewrite homM RzM mulmx_row3_col3 e2row !row3Z !row3D. Simp.r.
rewrite addrC (addrC theta4) addrA; congr hom.
rewrite /transA.
congr row3.
Abort.

Lemma H1234_old : g_old = hom rotA transA.
Proof.
rewrite /g_old.
rewrite etwistE.
rewrite etwistE.
rewrite (negbTE (norm1_neq0 (@normeE _ _))).
rewrite (_ : - w1 *v q1 = 0); last first.
  by rewrite /q1 /w1 crossmulNv crossmulvv oppr0.
rewrite pitch_nolin mulr0 scale0r add0r.
rewrite point_axis_nolin; last by rewrite -norm_eq0 normeE oner_eq0.
rewrite mul0mx.
rewrite pitch_perp ?normeE // mulr0 scale0r add0r.
rewrite point_axis_twist homM mul0mx add0r.
rewrite eskewM ?normeE //.
rewrite etwistE eqxx eskew_v0 homM mulr1 mulmx1.
rewrite etwistE (negbTE (norm1_neq0 (@normeE _ _))).
rewrite pitch_perp ?normeE // mulr0 scale0r add0r.
rewrite point_axis_twist homM.
rewrite eskewM ?normeE //.
rewrite -Rz_eskew; congr hom.

rewrite !mulmxBr !mulmx1 e2row.
rewrite !row3Z mulr0 mulr1.
rewrite eskewE ?normeE // mulmx_row3_col3 !scale0r. Simp.r. simpl.
rewrite /w2 e2row !mxE /= expr0n /=. Simp.r.
rewrite row3Z row3N !row3D. Simp.r.
rewrite eskewE ?normeE // /w3 e2row !mxE /= expr0n expr1n. Simp.r.
rewrite !mulmx_row3_col3 !row3Z. Simp.r.
rewrite !opprD !row3N !row3D. Simp.r. simpl.

rewrite (addrAC 1) -(addrA 1) subrr addr0 mulr1.
Abort.

End scara_screw.

End scara.
