(* coq-robot (c) 2017 AIST and INRIA. License: LGPL v3. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg ssrint div.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import  mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

(*From mathcomp.analysis Require Import reals.*)

Require Import ssr_ext euclidean3.
Require vec_angle.

(*
 OUTLINE:
 1. sections on symmetric and antisymmetry matrices.
 2. section skew
    properties of skew matrices
    sample lemma: eigenvalues of skew matrices
 3. section cayley_transform
 4. wip
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Section keyed_qualifiers_for_symmetric_matrices.

Variables (n : nat) (R : rcfType (*realType*)).

Definition anti := [qualify M : 'M[R]_n | M == - M^T].
Fact anti_key : pred_key anti. Proof. by []. Qed.
Canonical anti_keyed := KeyedQualifier anti_key.

Definition sym := [qualify M : 'M[R]_n | M == M^T].
Fact sym_key : pred_key sym. Proof. by []. Qed.
Canonical sym_keyed := KeyedQualifier sym_key.

End keyed_qualifiers_for_symmetric_matrices.

Notation "''so[' R ]_ n" := (anti n R)
  (at level 8, n at level 2, format "''so[' R ]_ n").

Section symmetric_matrices.

Variable R : rcfType (*realType*).
Variable n : nat.
Implicit Types M A B : 'M[R]_n.

Lemma symE M : (M \is sym n R) = (M == M^T). Proof. by []. Qed.

Lemma sym_cst a : a%:M \is sym n R. Proof. by rewrite symE tr_scalar_mx. Qed.

Lemma sym0 : 0 \is sym n R. Proof. by rewrite symE trmx0. Qed.

Lemma mul_tr_vec_sym (u : 'rV[R]_n) : u^T *m u \is sym n R.
Proof. apply/eqP; by rewrite trmx_mul trmxK. Qed.

Lemma symP A B : A \in sym n R -> B \in sym n R ->
  (forall i j : 'I_n, (i <= j)%N -> A i j = B i j) -> A = B.
Proof.
move=> sA sB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite AB.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (sA) (sB) => /eqP -> /eqP ->; by rewrite 2!mxE AB // leq_eqVlt ij orbC.
by move=> {ij}ij; rewrite AB // leq_eqVlt ij orbC.
Qed.

Lemma sym_oppr_closed : oppr_closed (sym n R).
Proof. move=> /= M /eqP HM; apply/eqP; by rewrite linearN /= -HM. Qed.

Lemma sym_addr_closed : addr_closed (sym n R).
Proof.
split; first by rewrite symE trmx0.
move=> /= A B; rewrite 2!symE => /eqP sA /eqP sB.
by rewrite symE linearD /= -sA -sB.
Qed.

Canonical SymOpprPred := OpprPred sym_oppr_closed.
Canonical SymAddrPred := AddrPred sym_addr_closed.

Lemma sym_scaler_closed : GRing.scaler_closed (sym n R).
Proof. move=> ? ?; rewrite 2!symE => /eqP H; by rewrite linearZ /= -H. Qed.
(* TODO: Canonical? *)

Lemma antiE M : (M \is 'so[R]_n) = (M == - M^T). Proof. by []. Qed.

Lemma antiN M : (- M \is 'so[R]_n) = (M \is 'so[R]_n).
Proof. apply/idP/idP; by rewrite !antiE linearN /= opprK eqr_oppLR. Qed.

Lemma anti_diag M i : M \is 'so[R]_n -> M i i = 0.
Proof.
rewrite antiE -addr_eq0 => /eqP/matrixP/(_ i i); rewrite !mxE.
by rewrite -mulr2n -mulr_natr => /eqP; rewrite mulf_eq0 pnatr_eq0 orbF => /eqP.
Qed.

Lemma trace_anti M : M \is 'so[R]_n -> \tr M = 0.
Proof.
move/anti_diag => HM.
by rewrite /mxtrace (eq_bigr (fun=> 0)) // sumr_const mul0rn.
Qed.

Lemma conj_so P M : M \is 'so[R]_n -> P^T *m M *m P \is 'so[R]_n.
Proof.
rewrite !antiE -eqr_oppLR => /eqP HM.
by rewrite !trmx_mul trmxK -HM !(mulNmx,mulmxN) opprK mulmxA.
Qed.

Lemma antiP A B : A \is 'so[R]_n -> B \is 'so[R]_n ->
  (forall i j : 'I_n, (i < j)%N -> A i j = - B j i) -> A = B.
Proof.
move=> soA soB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by do 2 rewrite anti_diag //.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (soA); by rewrite antiE => /eqP ->; rewrite 2!mxE AB // opprK.
move=> {ij}ij; rewrite AB //.
move: (soB); rewrite antiE -eqr_oppLR => /eqP/matrixP/(_ i j).
rewrite !mxE => <-; by rewrite opprK.
Qed.

Lemma anti_scaler_closed : GRing.scaler_closed 'so[R]_n.
Proof.
move=> ? ?; rewrite antiE => /eqP H; by rewrite antiE linearZ /= -scalerN -H.
Qed.
(* TODO: Canonical? *)

(* (anti)symmetric parts of a matrix *)
Definition symp A := 1/2%:R *: (A + A^T).
Definition antip A := 1/2%:R *: (A - A^T).

Lemma symp_antip A : A = symp A + antip A.
Proof.
rewrite /symp /antip -scalerDr addrCA addrK -mulr2n- scaler_nat.
by rewrite scalerA div1r mulVr ?pnatf_unit // scale1r.
Qed.

Lemma antip_is_so M : antip M \is 'so[R]_n.
Proof.
rewrite antiE /antip; apply/eqP; rewrite [in RHS]linearZ -scalerN /=.
by rewrite [in RHS]linearD /= opprD linearN /= opprK trmxK addrC.
Qed.

Lemma sym_symp M : symp M \in sym n R.
Proof.
by apply/eqP; rewrite /symp linearZ /= [in RHS]linearD /= trmxK addrC.
Qed.

End symmetric_matrices.

Lemma sqr_antip (R : rcfType (*realType*)) (M : 'M[R]_3) : M \is 'so[R]_3 ->
  M ^+ 2 = col_mx3
  (row3 (- M 0 1 ^+ 2 - M 0 2%:R ^+ 2) (- M 1 2%:R * M 0 2%:R) (M 0 1 * M 1 2%:R))
  (row3 (- M 1 2%:R * M 0 2%:R) (- M 0 1 ^+ 2 - M 1 2%:R ^+ 2) (- M 0 1 * M 0 2%:R))
  (row3 (M 1 2%:R * M 0 1) (- M 0 2%:R * M 0 1) (- M 0 2%:R ^+ 2 - M 1 2%:R ^+ 2)).
Proof.
move=> a; apply/matrix3P; rewrite !mxE /= !sum3E /a !anti_diag //.
apply/and9P; split; Simp.r => //=; apply/eqP.
- rewrite {2}(eqP a) 2!mxE mulrN -expr2; congr (_ + _).
  by rewrite {2}(eqP a) !mxE mulrN -expr2.
- by rewrite {2}(eqP a) 2!mxE mulrN mulrC.
- by rewrite {2}(eqP a) 2!mxE mulrN.
- rewrite {1}(eqP a) 2!mxE mulNr -expr2; congr (_ + _); by rewrite {2}(eqP a) 2!mxE mulrN -expr2.
- by rewrite {1}(eqP a) 2!mxE mulNr.
- by rewrite {1}(eqP a) 2!mxE {2}(eqP a) 2!mxE mulrN mulNr opprK.
- by rewrite {1}(eqP a) 2!mxE mulNr.
- rewrite {1}(eqP a) 2!mxE mulNr -expr2; congr (_ + _); by rewrite {1}(eqP a) 2!mxE mulNr -expr2.
Qed.

Section skew.

Variable R : rcfType (*realType*).
Let vector := 'rV[R]_3.
Implicit Types u : vector.
Implicit Types M : 'M[R]_3.

Definition skew_mx u : 'M[R]_3 := \matrix_i (u *v 'e_i).

Local Notation "'\S(' u ')'" := (skew_mx u) (at level 3, format "'\S(' u ')'").

Lemma skew_mxE u v : u *m \S( v ) = v *v u.
Proof.
rewrite crossmulC -crossmulNv [RHS]crossmulC -crossmulvN [u]row_sum_delta.
rewrite -/(mulmxr _ _) !linear_sum /=; apply: eq_bigr=> i _.
by rewrite !linearZ /= -scalemxAl -rowE linearN /= rowK crossmulvN opprK.
Qed.

Lemma skew_mx0 : \S( 0 ) = 0.
Proof. by apply/matrixP => i j; rewrite /skew_mx mxE crossmul0v 2!mxE. Qed.

Lemma skew_mxD u v : \S(u + v) = \S(u) + \S(v).
Proof. apply/eqP/mulmxP => w; by rewrite mulmxDr !skew_mxE crossmulDl. Qed.

Lemma skew_mxZ k u : \S( k *: u ) = k *: \S( u ).
Proof.
apply/matrixP => i j.
by rewrite mxE crossmulC linearZ /= -scalerN crossmulC opprK mxE 2![in RHS]mxE.
Qed.

Lemma skew_mxN u : \S( - u ) = - \S( u ).
Proof. by rewrite -scaleN1r skew_mxZ scaleN1r. Qed.

Lemma skew_mx_is_so u : \S( u ) \is 'so[R]_3.
Proof.
rewrite antiE; apply/eqP/matrixP => i j; rewrite !mxE -col_mx3_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma tr_skew u : \S( u )^T = - \S( u ).
Proof. by move: (skew_mx_is_so u); rewrite antiE -eqr_oppLR => /eqP <-. Qed.

Lemma mul_skew_mx (r : 'M[R]_3) (w : vector) :
  r * \S( w ) = col_mx3 (w *v row 0 r) (w *v row 1 r) (w *v row 2%:R r).
Proof. by rewrite {1}(col_mx3_rowE r) -mulmxE mulmx_col3 !skew_mxE. Qed.

Lemma skew01 u : \S( u ) 0 1 = u``_2%:R.
Proof. by rewrite /skew_mx mxE crossmulE !mxE /= !(mulr0,mulr1,addr0,subr0). Qed.

Lemma skew02 u : \S( u ) 0 2%:R = - u``_1%:R.
Proof. by rewrite /skew_mx mxE crossmulE !mxE /= !(mulr0,mulr1,add0r,opprK). Qed.

Lemma skew10 u : \S( u ) 1 0 = - u``_2%:R.
Proof. by move/eqP: (skew_mx_is_so u) => ->; rewrite 2!mxE skew01. Qed.

Lemma skew12 u : \S( u ) 1 2%:R = u``_0.
Proof. by rewrite /skew_mx mxE crossmulE !mxE /= !(mulr0, mulr1, subr0). Qed.

Lemma skew20 u : \S( u ) 2%:R 0 = u``_1%:R.
Proof. move/eqP: (skew_mx_is_so u) => ->; by rewrite 2!mxE skew02 opprK. Qed.

Lemma skew21 u : \S( u ) 2%:R 1 = - u``_0.
Proof. move/eqP: (skew_mx_is_so u) => ->; by rewrite 2!mxE skew12. Qed.

Lemma skewii u i : \S( u ) i i = 0.
Proof. by rewrite anti_diag // skew_mx_is_so. Qed.

Definition skewij := (skew01, skew10, skew02, skew20, skew21, skew12, skewii).

Lemma skew_mxT u : \S( u ) *m u^T = 0.
Proof.
rewrite -(trmxK (skew_mx u)) -trmx_mul tr_skew.
by rewrite mulmxN skew_mxE crossmulvv oppr0 trmx0.
Qed.

Definition unskew M := row3
  ((M 1 2%:R - M 2%:R 1) / 2%:R)
  ((M 2%:R 0 - M 0 2%:R) / 2%:R)
  ((M 0 1 - M 1 0) / 2%:R).

Lemma unskew_sym M : M \is sym 3 R -> unskew M = 0.
Proof.
rewrite symE => /eqP MMT.
by rewrite /unskew {1 3 5}MMT !mxE !subrr !mul0r row30.
Qed.

Lemma unskew_cst a : unskew a%:M = 0 :> 'rV[R]_3.
Proof. by rewrite unskew_sym // sym_cst. Qed.

Lemma unskew0 : unskew 0 = 0 :> 'rV[R]_3.
Proof.
rewrite (_ : 0 = 0%:M) ?unskew_cst //.
by apply/matrixP => ??; rewrite !mxE mul0rn.
Qed.

Lemma skew_mxK u : unskew \S( u ) = u.
Proof.
rewrite /unskew !skewij !opprK -!mulr2n -3!(mulr_natr (u``_ _)) -!mulrA.
by rewrite divrr ?unitfE ?pnatr_eq0 // 3!mulr1 [RHS]row3E !row3D !(add0r,addr0).
Qed.

Lemma unskewK M : M \is 'so[R]_3 -> \S( unskew M ) = M.
Proof.
move=> Mso.
move: (Mso); rewrite antiE => /eqP MMT.
apply/matrix3P/and9P; split; rewrite skewij ?anti_diag // mxE /=.
- rewrite {2}MMT !mxE opprK -mulr2n -(mulr_natr (M _ _)) -mulrA divrr ?mulr1 //.
  by rewrite unitfE pnatr_eq0.
- rewrite {1}MMT !mxE -mulNr opprB opprK -mulr2n.
  rewrite -(mulr_natr (M _ _)) -mulrA divrr ?mulr1 //.
  by rewrite unitfE pnatr_eq0.
- rewrite {1}MMT !mxE -mulNr opprB opprK -mulr2n.
  rewrite -(mulr_natr (M _ _)) -mulrA divrr ?mulr1 //.
  by rewrite unitfE pnatr_eq0.
- rewrite {2}MMT !mxE opprK -mulr2n -(mulr_natr (M _ _)) -mulrA divrr ?mulr1 //.
  by rewrite unitfE pnatr_eq0.
- rewrite {2}MMT !mxE opprK -mulr2n -(mulr_natr (M _ _)) -mulrA divrr ?mulr1 //.
  by rewrite unitfE pnatr_eq0.
- rewrite {1}MMT !mxE -mulNr opprB opprK -mulr2n.
  rewrite -(mulr_natr (M _ _)) -mulrA divrr ?mulr1 //.
  by rewrite unitfE pnatr_eq0.
Qed.
(*Lemma unskewK (M : 'M[R]_3) : M \is 'so[R]_3 -> \S( unskew M ) = M.
Proof.
move=> soM.
by apply/matrix3P; rewrite skewij ?anti_diag // mxE /= ?opprK // {1}(eqP soM) !mxE opprK.
Qed.*)

Lemma unskewN M : unskew (- M) = - unskew M.
Proof.
by rewrite /unskew !mxE !opprK row3N -!mulNr !opprB 3!(addrC (- M _ _)).
Qed.

Lemma unskewZ k M : unskew (k *: M) = k *: unskew M.
Proof.  by rewrite /unskew !mxE row3Z !mulrA !mulrBr. Qed.

Lemma unskewD (A B : 'M[R]_3) : unskew (A + B) = unskew A + unskew B.
Proof.
rewrite /unskew row3D -!mulrDl !mxE !opprD -!addrA.
by rewrite (addrCA (B 1 _)) (addrCA (B 2%:R _)) (addrCA (B 0 _)).
Qed.

Lemma skew_inj u v : (\S( u ) == \S( v )) = (u == v).
Proof.
apply/idP/idP => [/eqP H|/eqP -> //]; by rewrite -(skew_mxK u) H skew_mxK.
Qed.

(* more general result for antisymmetric matrices? *)
Lemma det_skew_mx u : \det \S( u ) = 0.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite skew_mx0 det0.
apply/eqP/det0P; exists u => //; by rewrite skew_mxE crossmulvv.
Qed.

Lemma skew_mx2' u : \S( u ) ^+ 2 = col_mx3
  (row3 (- u 0 2%:R ^+ 2 - u 0 1 ^+ 2) (u 0 0 * u 0 1) (u 0 0 * u 0 2%:R))
  (row3 (u 0 0 * u 0 1) (- u 0 2%:R ^+ 2 - u 0 0 ^+ 2) (u 0 1 * u 0 2%:R))
  (row3 (u 0 0 * u 0 2%:R) (u 0 1 * u 0 2%:R) (- u 0 1%:R ^+ 2 - u 0 0 ^+ 2)).
Proof.
rewrite (sqr_antip (skew_mx_is_so u)); congr col_mx3.
by rewrite !skewij sqrrN; Simp.r; rewrite (mulrC (u 0 2%:R)).
by rewrite !skewij; Simp.r; rewrite (mulrC (u 0 2%:R)).
by rewrite !skewij sqrrN; Simp.r.
Qed.

Lemma sym_skew_mx2 u : \S( u ) ^+ 2 \is sym 3 R.
Proof.
rewrite symE skew_mx2'; by apply/eqP/matrix3P/and9P; split; rewrite !mxE.
Qed.

Lemma skew_mx2 u : \S( u ) ^+ 2 = u^T *m u - (norm u ^+ 2)%:A.
Proof.
apply (symP (sym_skew_mx2 u)); last move=> i j.
  rewrite rpredD //; last by rewrite rpredN sym_scaler_closed // sym_cst.
  by rewrite mul_tr_vec_sym.
rewrite [in X in _ -> _ = X]mxE mulmx_trE.
case/boolP : (i == 0) => [/eqP-> _|/ifnot0P/orP[]/eqP->].
- case/boolP : (j == 0) => [|/ifnot0P/orP[]]/eqP->.
  + rewrite skew_mx2' 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE
      sum3E -!expr2 -addrA addrCA addrAC -addrA.
  + by rewrite skew_mx2' 5!mxE /= mulr0 subr0.
  + by rewrite skew_mx2' 5!mxE /= mulr0 subr0.
- case/boolP : (j == 0) => [/eqP-> //|/ifnot0P/orP[]/eqP-> _].
  + rewrite skew_mx2' 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE
      sum3E -!expr2 addrAC.
  + by rewrite skew_mx2' 5!mxE /= mulr0 subr0.
- case/boolP : (j == 0) => [/eqP-> //|/ifnot0P/orP[]/eqP-> // _].
  rewrite skew_mx2' 5!mxE /= -expr2 mulr1; apply/eqP.
  by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE sum3E -!expr2.
Qed.

Lemma skew_mx3 u : \S( u ) ^+ 3 = - (norm u) ^+ 2 *: \S( u ).
Proof.
rewrite exprS skew_mx2 mulrBr -mulmxE mulmxA skew_mxT mul0mx add0r.
by rewrite scalemx1 mul_mx_scalar scaleNr.
Qed.

Lemma skew_mx4 u : \S( u ) ^+ 4 = - norm u ^+2 *: \S( u ) ^+ 2.
Proof.
by rewrite exprS skew_mx3 scaleNr mulrN -scalerCA -scalerAl -expr2 scaleNr.
Qed.

Lemma mxtrace_skew_mx2 u : \tr (\S( u ) ^+ 2) = - (2%:R * (norm u) ^+ 2).
Proof.
rewrite /mxtrace sum3E skew_mx2'.
do 6 rewrite mxE /=.
rewrite -opprB opprK !addrA addrC !addrA -2!addrA.
rewrite [in RHS]mulr2n [in RHS]mulrDl [in RHS]opprD mul1r; congr (_ + _).
  rewrite -opprB opprK; congr (- _).
  by rewrite addrC addrA -dotmulvv dotmulE sum3E -!expr2.
rewrite -opprB -opprD opprK; congr (- _).
by rewrite addrC -addrA addrCA addrA  -dotmulvv dotmulE sum3E -!expr2.
Qed.

(* TODO: useful? *)
Lemma row'0_triple_prod_mat tmp (XM : 'M[{poly R}]_3) :
  row' ord0 (col_mx3 tmp (row 1 XM) (row 2%:R XM)) = row' ord0 XM.
Proof.
rewrite row'_col_mx3 /=.
apply/matrixP => i j; rewrite !mxE.
case: ifPn => [/eqP ->|].
  by rewrite !mxE; Simp.ord.
case: i => [] [] // [] // i _ /=.
by rewrite !mxE; Simp.ord.
Qed.

Lemma char_poly_skew_mx u : char_poly \S( u ) = 'X^3 + norm u ^+2 *: 'X.
Proof.
rewrite char_poly3 det_skew_mx subr0 trace_anti ?skew_mx_is_so //.
rewrite scale0r subr0 expr0n add0r mulrN mxtrace_skew_mx2 mulrN opprK.
by rewrite mulrA div1r mulVr ?unitfE ?pnatr_eq0 // mul1r.
Qed.

Definition skew_mx_eigenvalues : seq R[i] := [:: 0; 'i; 0 -i* 1]%C.

Ltac eigenvalue_skew_mx_eval_poly :=
  rewrite /map_poly horner_poly size_addl; [ |by rewrite size_polyXn size_polyX] ;
  rewrite size_polyXn sum4E !coefD !coefXn !coefX !add0r !mul0r !mul1r !add0r !addr0 mul1r.

Lemma eigenvalue_skew_mx u : norm u = 1 ->
  eigenvalue (map_mx (fun x => x%:C%C) \S( u)) =1 [pred k | k \in skew_mx_eigenvalues].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly char_poly_skew_mx u1 expr1n scale1r.
apply/rootP.
case: ifPn => [|Hk].
  rewrite inE => /orP [/eqP ->|]; first by rewrite /= horner_map !hornerE.
  rewrite inE => /orP [/eqP ->|].
    eigenvalue_skew_mx_eval_poly.
    by rewrite expr1 exprS sqr_i mulrN1 subrr.
  rewrite inE => /eqP ->.
  eigenvalue_skew_mx_eval_poly.
  apply/eqP. simpc. by rewrite addrC subrr eq_complex /= eqxx.
apply/eqP; apply: contra Hk.
eigenvalue_skew_mx_eval_poly.
rewrite (exprS _ 2) -{1}(mulr1 k) -mulrDr mulf_eq0 => /orP [/eqP ->|].
  by rewrite inE eqxx.
rewrite eq_sym addrC -subr_eq add0r -sqr_i eqf_sqr => /orP [/eqP <-|].
  by rewrite !inE eqxx orbC.
rewrite -eqr_oppLR => /eqP <-.
rewrite !inE orbA; apply/orP; right.
by rewrite eq_complex /= oppr0 !eqxx.
Qed.

End skew.

Notation "'\S(' w ')'" := (skew_mx w) (at level 3, format "'\S(' w ')'").

Section cayley_transform.

Variable R : rcfType (*realType*).
Let vector := 'rV[R]_3.
Implicit Types u : vector.

(* TODO: move? *)
Lemma ortho_addr1 n M : M \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue M -> M + 1 \is a GRing.unit.
Proof.
move=> MO N1.
rewrite unitmxE unitfE.
apply: contra N1 => /det0P[x x0 /eqP].
rewrite mulmxDr mulmx1 addr_eq0 eq_sym eqr_oppLR => /eqP Hx.
apply/eigenvalueP; exists x => //; by rewrite scaleN1r {2}Hx opprK.
Qed.

(* given an orthogonal matrix (-1 not eigenvalue), builds a skew-symmetric matrix *)
Definition skew_of_ortho n (M : 'M[R]_n.+1) := (M + 1)^-1 * (M - 1).

Lemma trmx_skew_of_orth n (M : 'M[R]_n.+1) : M \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue M -> (skew_of_ortho M)^T = - skew_of_ortho M.
Proof.
move=> MO N1.
rewrite /skew_of_ortho trmx_mul trmxV linearD /= [in X in _ *m X]linearD.
rewrite linearN /= trmx1 -(orthogonal_inv MO) -(mul1mx (_ + _)^-1).
rewrite -[X in _ *m (X *m _) = _](orthogonal_mul_tr MO).
rewrite !mulmxA mulmxBl mul1mx mulVmx // ?orthogonal_unit //.
rewrite -mulmxA -(orthogonal_inv MO) mulmxE -invrM; last 2 first.
  suff : M + 1 \is a GRing.unit.
    by rewrite !unitmxE !unitfE -det_tr linearD /= trmx1 orthogonal_inv.
  by rewrite ortho_addr1.
  by rewrite orthogonal_unit.
rewrite (mulrDl _ _ M) mul1r mulVr ?orthogonal_unit // -opprB.
have Htmp : M * (1 + M)^-1 = (1 + M)^-1 * M.
  rewrite -{1}(invrK M) -invrM; last 2 first.
    by rewrite addrC ortho_addr1.
    by rewrite orthogonal_inv // unitr_trmx ?orthogonal_unit.
  rewrite mulrDl divrr ?orthogonal_unit // div1r (orthogonal_inv MO).
  rewrite -{1}(orthogonal_tr_mul MO) -{1}(mulr1 M^T) -mulrDr invrM; last 2 first.
    by rewrite unitr_trmx orthogonal_unit.
    by rewrite addrC ortho_addr1.
  by rewrite -trmxV (orthogonal_inv MO) trmxK.
by rewrite mulNr mulrBl Htmp mul1r -{2}(mulr1 (1 + M)^-1) -mulrBr addrC.
Qed.

Lemma skew_of_ortho_is_so n Q : Q \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue Q -> skew_of_ortho Q \is 'so[R]_n.+1.
Proof. move=> HQ N1; by rewrite antiE trmx_skew_of_orth // ?opprK. Qed.

(* TODO: move? *)
Lemma sub1radd1r_comm n (M : 'M[R]_n.+1) : (1 - M) * (1 + M) = (1 + M) * (1 - M).
Proof. by rewrite mulrDr mulr1 mulrBl mul1r mulrDl mul1r mulrBr mulr1. Qed.

(* TODO: move? *)
Lemma det_sub1skew_mx u : \det (1 - \S( u )) = 1 + norm u ^+ 2.
Proof.
set a := skew_mx u.
rewrite det_mx33 [a]lock !mxE /=. Simp.r.
rewrite -lock /a !skewij subr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
by rewrite mulrBr opprB addrA mulrDr addrA mulrCA subrK addrAC sqr_norm sum3E.
Qed.

(* TODO: move? *)
Lemma skew_mx_inv u : 1 - \S( u ) \is a GRing.unit.
Proof.
set a := skew_mx u.
by rewrite unitmxE unitfE det_sub1skew_mx paddr_eq0 // ?ler01 // ?sqr_ge0 // negb_and oner_neq0.
Qed.

(* TODO: move? *)
Lemma det_add1skew_mx u : \det (1 + \S( u )) = 1 + norm u ^+ 2.
Proof.
set a := skew_mx u.
rewrite det_mx33 [a]lock !mxE /=. Simp.r.
rewrite -lock /a !skewij addr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
rewrite sqr_norm sum3E -!expr2 -!addrA; congr (_ + _).
rewrite mulrDr -expr2 (addrC _ (_^+2)) -!addrA addrC; congr (_ + _).
by rewrite mulrBr opprB -expr2 addrCA mulrCA subrr addr0.
Qed.

(* TODO: move? *)
Lemma sym_add1r M : M \is 'so[R]_3 -> \det (1 + M) != 0.
Proof.
move/unskewK => <-.
by rewrite det_add1skew_mx paddr_eq0 // ?sqr_ge0 // oner_eq0.
Qed.

(* TODO: move? *)
Lemma sym_sub1r M : M \is 'so[R]_3 -> \det (1 - M) != 0.
Proof.
move/unskewK => <-.
by rewrite det_sub1skew_mx paddr_eq0 // ?sqr_ge0 // oner_eq0.
Qed.

(* given a skew-symmetric matrix, builds an orthogonal matrix *)
Definition ortho_of_skew n (M : 'M[R]_n.+1) := (1 + M) * (1 - M)^-1.

Lemma trmx_ortho_of_skew n M : M \is 'so[R]_n.+1 ->
  (ortho_of_skew M)^T = (1 + M)^-1 * (1 - M).
Proof.
move=> Mso.
rewrite /ortho_of_skew trmx_mul trmxV linearB /= trmx1 linearD /= trmx1.
move: (Mso); rewrite antiE => /eqP {1}<-.
move: Mso; rewrite antiE => /eqP {2}->; by rewrite linearN /= trmxK.
Qed.

Lemma ortho_of_skew_is_O M : M \is 'so[R]_3 -> ortho_of_skew M \is 'O[R]_3.
Proof.
move=> Mso.
rewrite orthogonalEC trmx_ortho_of_skew // /ortho_of_skew.
rewrite -mulrA (mulrA (1 - M)) sub1radd1r_comm !mulrA.
rewrite mulVr ?mul1r ?unitmxE ?unitfE ?sym_add1r //.
by rewrite mulrV // unitmxE unitfE sym_sub1r.
Qed.

Lemma det_ortho_of_skew M : M \is 'so[R]_3 -> \det (ortho_of_skew M) = 1.
Proof.
move/unskewK => <-.
rewrite /ortho_of_skew det_mulmx det_inv det_add1skew_mx det_sub1skew_mx.
by rewrite divrr // unitfE paddr_eq0 ?oner_eq0 /= // sqr_ge0.
Qed.

(* [murray] exercise 5.(a), p.73 *)
Lemma ortho_of_skew_is_SO M : M \is 'so[R]_3 -> ortho_of_skew M \is 'SO[R]_3.
Proof.
move=> Mso; by rewrite rotationE ortho_of_skew_is_O //= det_ortho_of_skew.
Qed.

End cayley_transform.

Section wip.

Variable R : rcfType (*realType*).

Definition lie_bracket (w1 w2 : 'rV[R]_3) := \S( w1 ) * \S( w2) - \S( w2 ) * \S( w1 ).

Local Notation "[ w1 , w2 ]" := (lie_bracket w1 w2).

Lemma lie_bracketE w1 w2 : [ w1 , w2 ] = \S( w1 *v w2 ).
Proof.
Abort.

(* [murray] second half of exercise 9(a), p. 75 *)
Lemma kernel_skew_mx (w : 'rV[R]_3) (w0 : w != 0) : (kermx \S( w ) == w)%MS.
Proof.
apply/andP; split; last by apply/sub_kermxP; rewrite skew_mxE crossmulvv.
apply/rV_subP => v /sub_kermxP.
rewrite skew_mxE => /eqP/vec_angle.colinearP[|[_[k [Hk1 Hk2]]]].
  move/eqP => ->.
  by rewrite sub0mx.
apply/sub_rVP; exists (k^-1).
rewrite Hk2 scalerA mulVr ?scale1r // unitfE; apply: contra w0.
rewrite Hk2 => /eqP ->; by rewrite scale0r.
Qed.

End wip.
