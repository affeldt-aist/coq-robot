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

(* wip *)
Section plucker_of_line.

Variable R : rcfType.
Implicit Types l : Line.t R.

Definition normalized_plucker_direction l :=
  let p1 := \pt( l ) in let p2 := \pt2( l ) in
  (norm (p2 - p1))^-1 *: (p2 - p1).

Lemma normalized_plucker_directionP (l : Line.t R) : \vec( l ) != 0 ->
  let e := normalized_plucker_direction l in e *d e == 1.
Proof.
move=> l0 /=.
rewrite /normalized_plucker_direction dotmulZv dotmulvZ dotmulvv.
rewrite -Line.vectorE.
rewrite mulrA mulrAC expr2 mulrA mulVr ?unitfE ?norm_eq0 // mul1r.
by rewrite divrr // unitfE norm_eq0.
Qed.

Definition normalized_plucker_position l :=
  \pt( l ) *v normalized_plucker_direction l.

Lemma normalized_plucker_positionP l :
  normalized_plucker_position l *d normalized_plucker_direction l == 0.
Proof.
rewrite /normalized_plucker_position /normalized_plucker_direction -Line.vectorE crossmulvZ.
by rewrite dotmulvZ dotmulZv -dot_crossmulC crossmulvv dotmulv0 2!mulr0.
Qed.

Definition normalized_plucker l : 'rV[R]_6 :=
  row_mx (normalized_plucker_direction l) (normalized_plucker_position l).

Definition plucker_of_line l : 'rV[R]_6 :=
  let p1 := \pt( l ) in let p2 := \pt2( l ) in
  row_mx (p2 - p1) (p1 *v (p2 - p1)).

Lemma normalized_pluckerP l :
  let p1 := \pt( l ) in
  let p2 := \pt2( l ) in
  \vec( l ) != 0 ->
  plucker_of_line l = norm (p2 - p1) *: normalized_plucker l.
Proof.
move=> p1 p2 l0.
rewrite /normalized_plucker /normalized_plucker_direction /normalized_plucker_position.
rewrite -/p1 -/p2 crossmulvZ -scale_row_mx scalerA.
by rewrite divrr ?scale1r // unitfE norm_eq0 /p2 -Line.vectorE.
Qed.

Lemma plucker_of_lineE l (l0 : \vec( l ) != 0) :
  plucker_of_line l = norm (\pt2( l ) - \pt( l )) *:
  (Plucker.mkArray (normalized_plucker_directionP l0) (normalized_plucker_positionP l) : 'M__).
Proof.
rewrite /plucker_of_line /plucker_array_mx /=.
rewrite /normalized_plucker_direction /normalized_plucker_position crossmulvZ -scale_row_mx.
by rewrite scalerA divrr ?scale1r // unitfE norm_eq0 -Line.vectorE.
Qed.

Definition plucker_eqn p l :=
  let p1 := \pt( l ) in let p2 := \pt2( l ) in
  p *m (\S( p2 ) - \S( p1 )) + p1 *v (p2 - p1).

Lemma plucker_eqn0 p l : \vec( l ) = 0 -> plucker_eqn p l = 0.
Proof.
move => l0; rewrite /plucker_eqn -skew_mxN -skew_mxD -Line.vectorE.
by rewrite skew_mxE l0 crossmul0v crossmulv0 addr0.
Qed.

Lemma plucker_eqn_self l : plucker_eqn \pt( l ) l = 0.
Proof.
rewrite /plucker_eqn -skew_mxN -skew_mxD skew_mxE crossmulC addrC.
by rewrite -crossmulBl subrr crossmul0v.
Qed.

Lemma in_plucker p l : p \in (l : pred _) -> plucker_eqn p l = 0.
Proof.
rewrite inE => /orP[/eqP ->|/andP[l0 H]]; first by rewrite plucker_eqn_self.
rewrite /plucker_eqn -skew_mxN -skew_mxD skew_mxE crossmulC addrC -crossmulBl.
apply/eqP.
rewrite -/(colinear _ _) -colinearNv opprB colinear_sym.
apply: (colinear_trans l0 _ H).
by rewrite -Line.vectorE colinear_refl.
Qed.

Definition homogeneous_plucker_eqn l :=
  let p1 := \pt( l ) in let p2 := \pt2( l ) in
  col_mx (\S( p2 ) - \S( p1 )) (p1 *v (p2 - p1)).

Require Import rigid.

Lemma homogeneous_in_plucker p (l : Line.t R) : p \is 'hP[R] ->
  from_h p \in (l : pred _) ->
  p *m homogeneous_plucker_eqn l = 0.
Proof.
move=> hp /in_plucker Hp /=.
rewrite /homogeneous_plucker_eqn.
move: (hp); rewrite hpoint_from_h => /eqP ->.
by rewrite (mul_row_col (from_h p) 1) mul1mx.
Qed.

End plucker_of_line.

Section denavit_hartenberg_homogeneous_matrix.

Variable R : rcfType.

Definition dh_mat (jangle : angle R) loffset llength (ltwist : angle R) : 'M[R]_4 :=
  hRx ltwist * hTx llength * hTz loffset * hRz jangle.

Definition dh_rot (jangle ltwist : angle R) := col_mx3
  (row3 (cos jangle) (sin jangle) 0)
  (row3 (cos ltwist * - sin jangle) (cos ltwist * cos jangle) (sin ltwist))
  (row3 (sin ltwist * sin jangle) (- sin ltwist * cos jangle) (cos ltwist)).

Lemma dh_rot_i (f1 f0 : Frame.t R) t a : f1 _R^ f0 = dh_rot t a ->
  f1|,0 *m f0^T = row3 (cos t) (sin t) 0.
Proof.
rewrite (rowE 0 f1) -mulmxA FromToE noframe_inv => ->.
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

Hypothesis dh1 : perpendicular (xaxis F1) (zaxis F0).
Hypothesis dh2 : intersects (xaxis F1) (zaxis F0).

(* [spong] an homogeneous transformation that satisfies dh1 and dh2 
   can be represented by means of only four parameters *)
Lemma dh_mat_correct : exists alpha theta d a,
  hom From1To0 p1_in_0 = dh_mat theta d a alpha.
Proof.
have H1 : From1To0 0 2%:R = 0.
  rewrite /From1To0 -lock /FromTo mxE; by move/eqP: dh1 => /=.
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
  TFrame.o F1 = TFrame.o F0 + d *: (F0|,2%:R) + a *: (F1|,0).
  case/intersects_interpoint : dh2 => p [].
  rewrite /is_interpoint => /andP[/lineP[k1 /= Hk1] /lineP[k2 /= Hk2]] _.
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
rewrite [in X in _ = X -> _]mulmxDl -scalemxAl.
rewrite (rowE 2%:R F0) -mulmxA mulmxE -{2}noframe_inv divrr ?mulmx1 ?noframe_is_unit //.
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
  (Joint.vaxis (joints i) == (frames i')|,2%:R) ||
  (Joint.vaxis (joints i) == - (frames i')|,2%:R).

(* 2. Xi is the common perpendicular to Zi-1 and Zi *)
Definition X_Z (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in 
  let predi : 'I_n.+1 := inord i.-1 in 
  let: (o_predi, z_predi) := let f := frames predi in (TFrame.o f, f|,2%:R) in
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, f|,0, f|,2%:R) in
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
  let: (o_succi, x_succi) := let f := frames succi in (TFrame.o f, f|,0) in 
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, f|,0, f|,2%:R) in 
  if intersection (zaxis (frames i')) (xaxis (frames succi)) is some o'_i then
    (norm (o'_i - o_i)(*the Zi-coordiante of o'_i*) == Link.offset (links i')) &&
    (`| Link.offset (links i') | == distance_between_lines (xaxis (frames i')) (xaxis (frames succi)))
  else
    false (* should not happen since Zi always intersects Xi.+1 (see condidion 2.) *).

Definition link_twist (frames : frame ^ n.+1) (links : link ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (x_succi, z_succi) := let f := frames succi in (f|,0, f|,2%:R) in 
  let z_i := (frames i')|,2%:R in 
  Link.twist (links i') == angle_between_lines z_i z_succi x_succi.
  (*angle measured about the positive direction of Xi+1*)

Definition joint_angle (frames : frame ^ n.+1) (joints : joint ^ n) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: x_succi := (frames succi)|,0 in 
  let: (x_i, z_i) := let f := frames i' in (f|,0, f|,2%:R) in 
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
