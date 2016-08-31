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

Require Import aux euclidean3 vec_angle.

(*
 OUTLINE:
 1. section on symmetric and antisymmetry matrices.
 2. section skew
     (properties of skew matrices)
     (sample lemma: eigenvalues of skew matrices)
     Cayley transformation
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Section anti_sym_def.

Variables (n : nat) (R : rcfType).

Definition anti := [qualify M : 'M[R]_n | M == - M^T].
Fact anti_key : pred_key anti. Proof. by []. Qed.
Canonical anti_keyed := KeyedQualifier anti_key.

Definition sym := [qualify M : 'M[R]_n | M == M^T].
Fact sym_key : pred_key sym. Proof. by []. Qed.
Canonical sym_keyed := KeyedQualifier sym_key.

End anti_sym_def.

Notation "''so[' R ]_ n" := (anti n R)
  (at level 8, n at level 2, format "''so[' R ]_ n").

Section symmetric_and_antisymmetric_matrices.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Lemma antiE n M : (M \is 'so[R]_n) = (M == - M^T). Proof. by []. Qed.

Lemma symE n M : (M \is sym n R) = (M == M^T). Proof. by []. Qed.

Lemma antiN n M : (- M \is 'so[R]_n) = (M \is 'so[R]_n).
Proof. apply/idP/idP; by rewrite !antiE linearN /= opprK eqr_oppLR. Qed.

Lemma anti_diag n M (i : 'I_n) : M \is 'so[R]_n -> M i i = 0.
Proof.
rewrite antiE -addr_eq0 => /eqP/matrixP/(_ i i); rewrite !mxE.
by rewrite -mulr2n -mulr_natr => /eqP; rewrite mulf_eq0 pnatr_eq0 orbF => /eqP.
Qed.

Lemma antiP n (A B : 'M[R]_n) : A \is 'so[R]_n -> B \is 'so[R]_n ->
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

Lemma symP n (A B : 'M[R]_n) : A \in sym n R -> B \in sym n R ->
  (forall i j : 'I_n, (i <= j)%N -> A i j = B i j) -> A = B.
Proof.
move=> symA symB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite AB.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (symA) (symB) => /eqP -> /eqP ->; by rewrite 2!mxE AB // leq_eqVlt ij orbC.
by move=> {ij}ij; rewrite AB // leq_eqVlt ij orbC.
Qed.

(* (anti)symmetric parts of a matrix *)
Definition symp n (A : 'M[R]_n) := 1/2%:R *: (A + A^T).
Definition antip n (A : 'M[R]_n) := 1/2%:R *: (A - A^T).

Lemma symp_antip n (A : 'M[R]_n) : A = symp A + antip A.
Proof.
rewrite /symp /antip -scalerDr addrCA addrK -mulr2n- scaler_nat.
by rewrite scalerA div1r mulVr ?pnatf_unit // scale1r.
Qed.

Lemma antip_is_so n (M : 'M[R]_n) : antip M \is 'so[R]_n.
Proof.
rewrite antiE /antip; apply/eqP; rewrite [in RHS]linearZ -scalerN /=.
by rewrite [in RHS]linearD /= opprD linearN /= opprK trmxK addrC.
Qed.

Lemma antip_scaler_closed n : GRing.scaler_closed 'so[R]_n.
Proof.
move=> ? ?; rewrite antiE => /eqP H; by rewrite antiE linearZ /= -scalerN -H.
Qed.

Lemma sym_symp n (M : 'M[R]_n) : symp M \in sym n R.
Proof.
by apply/eqP; rewrite /symp linearZ /= [in RHS]linearD /= trmxK addrC.
Qed.

Lemma sym_oppr_closed n : oppr_closed (sym n R).
Proof. move=> /= M /eqP HM; apply/eqP; by rewrite linearN /= -HM. Qed.

Lemma sym_addr_closed n : addr_closed (sym n R).
Proof.
split; first by rewrite symE trmx0.
move=> /= A B; rewrite 2!symE => /eqP sA /eqP sB.
by rewrite symE linearD /= -sA -sB.
Qed.

Canonical SymOpprPred n := OpprPred (@sym_oppr_closed n).
Canonical SymAddrPred n := AddrPred (@sym_addr_closed n).

Lemma sym_scaler_closed n : GRing.scaler_closed (sym n R).
Proof. move=> ? ?; rewrite 2!symE => /eqP H; by rewrite linearZ /= -H. Qed.

Lemma sym_cst n a : a%:M \is sym n R.
Proof. by rewrite symE tr_scalar_mx. Qed.

Lemma sym0 n : 0 \is sym n R.
Proof. by rewrite symE trmx0. Qed.

Lemma mul_tr_vec_sym n (u : 'rV[R]_n) : u^T *m u \is sym n R.
Proof. apply/eqP; by rewrite trmx_mul trmxK. Qed.

(* TODO: Canonical? *)

Lemma trace_anti n (M : 'M[R]_n) : M \is 'so[R]_n -> \tr M = 0.
Proof.
move/anti_diag => m; by rewrite /mxtrace (eq_bigr (fun=> 0)) // sumr_const mul0rn.
Qed.

Lemma sqr_antip (M : 'M[R]_3) : M \is 'so[R]_3 ->
  M ^+ 2 = col_mx3
  (row3 (- M 0 1 ^+ 2 - M 0 2%:R ^+ 2) (- M 1 2%:R * M 0 2%:R) (M 0 1 * M 1 2%:R))
  (row3 (- M 1 2%:R * M 0 2%:R) (- M 0 1 ^+ 2 - M 1 2%:R ^+ 2) (- M 0 1 * M 0 2%:R))
  (row3 (M 1 2%:R * M 0 1) (- M 0 2%:R * M 0 1) (- M 0 2%:R ^+ 2 - M 1 2%:R ^+ 2)).
Proof.
move=> a; apply/matrix3P; rewrite !mxE /= sum3E /a !anti_diag //; Simp.r => //.
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

End symmetric_and_antisymmetric_matrices.

Section skew.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Type u : vector.

Definition skew_mx u : 'M[R]_3 := \matrix_i (u *v 'e_i).

Local Notation "'\S(' u ')'" := (skew_mx u) (at level 3, format "'\S(' u ')'").

Lemma skew_mx0 : \S( 0 ) = 0.
Proof.
by apply/matrixP => i j; rewrite /skew_mx mxE crossmul0v 2!mxE.
Qed.

Lemma skew_mxZ k u : \S( k *: u ) = k *: \S( u ).
Proof.
rewrite /skew_mx; apply/matrixP => i j.
by rewrite mxE crossmulC linearZ /= -scalerN crossmulC opprK mxE 2![in RHS]mxE.
Qed.

Lemma skew_mxN u : \S( - u ) = - \S( u ).
Proof. by rewrite -scaleN1r skew_mxZ scaleN1r. Qed.

Lemma anti_skew u : \S( u ) \is 'so[R]_3.
Proof.
rewrite antiE; apply/eqP/matrixP => i j; rewrite !mxE -col_mx3_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma tr_skew u : \S( u )^T = - \S( u ).
Proof. by move: (anti_skew u); rewrite antiE -eqr_oppLR => /eqP <-. Qed.

Lemma skew01 u : \S( u ) 0 1 = u``_2%:R.
Proof. by rewrite /skew_mx mxE crossmulE !mxE /= !(mulr0, mulr1, addr0, subr0). Qed.

Lemma skew02 u : \S( u ) 0 2%:R = - u``_1%:R.
Proof. by rewrite /skew_mx mxE crossmulE !mxE /= !(mulr0, mulr1, add0r, opprK). Qed.

Lemma skew10 u : \S( u ) 1 0 = - u``_2%:R.
Proof. by move/eqP: (anti_skew u) => ->; rewrite 2!mxE skew01. Qed.

Lemma skew12 u : \S( u ) 1 2%:R = u``_0.
Proof. by rewrite /skew_mx mxE crossmulE !mxE /= !(mulr0, mulr1, subr0). Qed.

Lemma skew20 u : \S( u ) 2%:R 0 = u``_1%:R.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew02 opprK. Qed.

Lemma skew21 u : \S( u ) 2%:R 1 = - u``_0.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew12. Qed.

Lemma skewii u i : \S( u ) i i = 0.
Proof. by rewrite anti_diag // anti_skew. Qed.

Definition skewij := (skew01, skew10, skew02, skew20, skew21, skew12, skewii).

Lemma skew_mxE u v : u *m \S( v ) = v *v u.
Proof.
rewrite crossmulC -crossmulNv.
  rewrite [RHS]crossmulC -crossmulvN [u]row_sum_delta -/(mulmxr _ _) !linear_sum /=.
by apply: eq_bigr=> i _; rewrite !linearZ /= -scalemxAl -rowE linearN /= rowK crossmulvN opprK.
Qed.

Lemma skew_mxT u : \S( u ) *m u^T = 0.
Proof.
rewrite -(trmxK (skew_mx u)) -trmx_mul tr_skew.
by rewrite mulmxN skew_mxE crossmulvv oppr0 trmx0.
Qed.

Definition unskew (M : 'M[R]_3) :=
  row3 ((M 1 2%:R - M 2%:R 1)/2%:R) ((M 2%:R 0 - M 0 2%:R)/2%:R) ((M 0 1 - M 1 0)/2%:R).
(*old, less general definition:
Definition unskew (M : 'M[R]_3) := row3 (M 1 2%:R) (- M 0 2%:R) (M 0 1).*)

Lemma unskew_sym (M : 'M[R]_3) : M \is sym 3 R -> unskew M = 0.
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
(*Lemma skew_mxK u : unskew \S( u ) = u.
Proof.
apply/rowP => i; rewrite 2!mxE /=.
case: ifPn => [/eqP ->|]; first by rewrite crossmulE /= !mxE /=; Simp.r.
by rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !skewij // opprK.
Qed.*)

Lemma unskewK (M : 'M[R]_3) : M \is 'so[R]_3 -> \S( unskew M ) = M.
Proof.
move=> Mso.
move: (Mso); rewrite antiE => /eqP MMT.
apply/matrix3P; rewrite skewij ?anti_diag // mxE /=.
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

Lemma unskewN (M : 'M[R]_3) : unskew (- M) = - unskew M.
Proof.
by rewrite /unskew !mxE !opprK row3N -!mulNr !opprB 3!(addrC (- M _ _)).
Qed.
(*by rewrite /unskew !mxE -row3N. Qed.*)

Lemma unskewZ k (M : 'M[R]_3) : unskew (k *: M) = k *: unskew M.
Proof.  by rewrite /unskew !mxE row3Z !mulrA !mulrBr. Qed.
(*by rewrite /unskew !mxE -mulrN row3Z. Qed.*)

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
rewrite (sqr_antip (anti_skew u)); congr col_mx3.
by rewrite !skewij sqrrN; Simp.r; rewrite (mulrC (u 0 2%:R)).
by rewrite !skewij; Simp.r; rewrite (mulrC (u 0 2%:R)).
by rewrite !skewij sqrrN; Simp.r.
Qed.

Lemma sym_skew_mx2 u : \S( u ) ^+ 2 \is sym 3 R.
Proof. rewrite symE skew_mx2'; by apply/eqP/matrix3P; rewrite !mxE. Qed.

Lemma mulmx_trE {n} (v : 'rV[R]_n) i j : (v^T *m v) i j = v 0 i * v 0 j.
Proof.
by rewrite mxE (bigD1 ord0) //= big1 ?mxE ?addr0 // => i0; rewrite (ord1 i0).
Qed.

Lemma skew_mx2 u : \S( u ) ^+ 2 = u^T *m u - (norm u ^+ 2)%:A.
Proof.
apply (symP (sym_skew_mx2 u)); last move=> i j.
  rewrite rpredD //; last by rewrite rpredN sym_scaler_closed // sym_cst.
  by rewrite mul_tr_vec_sym.
rewrite [in X in _ -> _ = X]mxE mulmx_trE.
case/boolP : (i == 0) => [/eqP -> _|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite skew_mx2' 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE
      sum3E -!expr2 -addrA addrCA addrAC -addrA.
  rewrite ifnot0 => /orP [] /eqP ->; by rewrite skew_mx2' 5!mxE /= mulr0 subr0.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP -> //|].
  rewrite ifnot0 => /orP [] /eqP -> _.
    rewrite skew_mx2' 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE
      sum3E -!expr2 addrAC.
    by rewrite skew_mx2' 5!mxE /= mulr0 subr0.
case/boolP : (j == 0) => [/eqP -> //|].
rewrite ifnot0 => /orP [] /eqP -> // _.
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

(* TODO: move to aux? *)
Lemma char_poly3_coef1 (M : 'M[R]_3) :
  let Z := 1 / 2%:R * (\tr M ^+ 2 - \tr (M ^+ 2)) in
  (char_poly M)`_1 = Z.
Proof.
move=> Z.
rewrite /char_poly /char_poly_mx det_mx33 !mxE mulr1n mulr0n !add0r.
rewrite !mulNr !mulrN !opprK.
rewrite !coefD.
(* 1 *)
rewrite [X in X + _ + _](_ : _ = M 0 0 * (M 2%:R 2%:R + M 1 1) +
   (M 1 1 * M 2%:R 2%:R - M 2%:R 1 * M 1 2%:R)); last first.
  rewrite coefM sum2E coefD coefX add0r coefN coefC [- _]/=.
  rewrite subn0 coefD.
  rewrite coefM sum2E subn0 coefD coefX add0r coefN (_ : _`_0 = M 1 1); last by rewrite coefC.
  rewrite coefD coefX coefN coefC subr0 mulr1.
  rewrite coefD coefN coefX coefN coefC subr0 mul1r.
  rewrite subnn coefD coefX add0r coefN coefC [in X in - M 1 1 - X]/=.
  rewrite coefM sum2E coefC coefC mulr0 add0r coefC mul0r subr0.
  rewrite coefD coefX coefN coefC subr0 mul1r.
  rewrite coefD coefM sum1E coefD coefX add0r coefN coefC [in X in - X * _`_ _]/=.
  rewrite coefD coefX add0r coefN coefC mulrN !mulNr opprK.
  rewrite coefN coefM sum1E coefC coefC [in X in M 1 1 * _ - X]/=.
  by rewrite -opprB mulrN 2!opprK.
rewrite [X in _ + X + _](_ : _ = - M 0 1 * M 1 0); last first.
  rewrite coefN coefM sum2E coefC [in X in X * _]/= subnn.
  rewrite coefD subn0 coefM sum2E.
  rewrite subn0 subnn coefC coefC mulr0 add0r.
  rewrite coefC mul0r add0r.
  rewrite coefM sum2E subn0 subnn coefC coefD coefX coefN coefC subr0 mulr1.
  rewrite coefC mul0r addr0 coefC mul0r addr0.
  by rewrite mulNr.
rewrite [X in _ + _ + X](_ : _ = - M 0 2%:R * M 2%:R 0); last first.
  rewrite coefN coefM sum2E subn0 subnn coefC.
  rewrite [in X in X * _]/=.
  rewrite coefD coefM sum2E subn0 coefC coefC mulr0 add0r.
  rewrite coefC mul0r add0r coefM sum2E subn0 subnn coefC [in X in X * _`_1]/=.
  by rewrite coefD coefX coefN coefC subr0 mulr1 coefC mul0r addr0 coefC mul0r addr0 mulNr.
rewrite /Z.
apply/(@mulrI _ 2%:R); first exact: pnatf_unit.
rewrite mulrA div1r divrr ?pnatf_unit // mul1r.
rewrite sqr_mxtrace.
rewrite mxtrace_sqr.
rewrite 3!opprD -[in RHS]addrAC [in RHS](addrC (\sum_ _ _)) 3![in RHS]addrA addrK.
rewrite mulrDr addrC mulNr mulrN (mulrC 2%:R) mulr_natr.
rewrite -2![in RHS]addrA [in RHS]addrC -[in RHS]addrA; congr (_ + _).
rewrite mulrDr addrC mulNr mulrN (mulrC 2%:R) mulr_natr.
rewrite [in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite addrA mulrDr addrC mulrN (mulrC 2%:R) mulr_natr mulrC -addrA; congr (_ + _).
rewrite (mulrC 2%:R) mulr_natr.
rewrite mulrDr.
rewrite mulrDl.
rewrite mulr2n.
rewrite [in RHS]mulr2n.
rewrite [in X in _ = _ + X]mulr2n.
rewrite -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + (_ + _)).
by rewrite addrCA.
Qed.

(* TODO: move to aux? *)
Lemma char_poly3 (M : 'M[R]_3) :
  let Z := 1 / 2%:R * ((\tr M) ^+ 2 - \tr (M ^+ 2)) in
  char_poly M = 'X^3 - (\tr M) *: 'X^2 + Z *: 'X - (\det M)%:P.
Proof.
move=> Z.
rewrite -(coefK (char_poly M)) (size_char_poly M).
apply/polyP.
case. (* coef0 *)
  rewrite coef_poly char_poly_det !coef_add_poly !coef_opp_poly !coefZ.
  rewrite !coefX !coefXn add0r mulr0 oppr0 mulr0 add0r add0r coefC /=.
  by rewrite exprS sqrrN expr1n mulr1 mulN1r.
case; last first.
  case. (* coef2 *)
    rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
    by rewrite add0r mulr0 mulr1 addr0 coefC subr0 char_poly_trace.
  case; last first. (* coef n >= 4 *)
    move=> n.
    rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
    by rewrite add0r mulr0 mulr0 coefC subr0 addr0 oppr0.
  (* coef3 *)
  rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
  rewrite mulr0 subr0 mulr0 addr0 coefC subr0; apply/eqP.
  rewrite (_ : _`_3 = lead_coef (char_poly M)); last first.
    by rewrite lead_coefE size_char_poly.
  by rewrite -monicE char_poly_monic.
(* coef1 *)
rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
rewrite add0r mulr1 mulr0 oppr0 add0r coefC subr0.
suff : (char_poly M)`_1 = Z by move=> ->.
by rewrite char_poly3_coef1.
Qed.

Lemma char_poly_skew_mx u : char_poly \S( u ) = 'X^3 + norm u ^+2 *: 'X.
Proof.
rewrite char_poly3 det_skew_mx subr0 trace_anti ?anti_skew //.
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

Lemma skew_mxC u : let a := \S( u ) in (1 + a) * (1 - a) = (1 - a) * (1 + a).
Proof.
move=> a.
rewrite mulrDl mul1r mulrDr mulr1 mulrN addrA subrK.
by rewrite mulrDr mulr1 mulrBl mul1r addrA subrK.
Qed.

Lemma det_skew_mx1 u : \det (1 - \S( u )) = 1 + norm u ^+ 2.
Proof.
set a := skew_mx u.
rewrite det_mx33 [a]lock !mxE /=. Simp.r.
rewrite -lock /a !skewij subr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
by rewrite mulrBr opprB addrA mulrDr addrA mulrCA subrK addrAC sqr_norm sum3E.
Qed.

Lemma skew_mx_inv u : 1 - \S( u ) \is a GRing.unit.
Proof.
set a := skew_mx u.
by rewrite unitmxE unitfE det_skew_mx1 paddr_eq0 // ?ler01 // ?sqr_ge0 // negb_and oner_neq0.
Qed.

Definition cayley_of_skew u := (1 - \S( u ))^-1 * (1 + \S( u )).

Lemma cayley_of_skew_is_O u : cayley_of_skew u \is 'O[R]_3.
Proof.
rewrite orthogonalE /cayley_of_skew.
set a := skew_mx u.
rewrite trmx_mul trmxV.
do 2 rewrite linearD /= trmx1.
rewrite [in X in _ * _ * (_ * X) == _]linearN /= tr_skew.
rewrite (opprK (skew_mx u)) -/a -mulrA (mulrA (1 + a)) skew_mxC -/a.
rewrite !mulrA mulVr ?skew_mx_inv // mul1r divrr //.
by rewrite -(opprK a) -skew_mxN skew_mx_inv.
Qed.

Lemma det_caley u : \det (cayley_of_skew u) = 1.
Proof.
rewrite /cayley_of_skew det_mulmx det_inv det_skew_mx1.
rewrite -(opprK (skew_mx u)) -skew_mxN det_skew_mx1 normN.
by rewrite mulVr // unitfE paddr_eq0 ?ler01 // ?sqr_ge0 // oner_eq0.
Qed.

Lemma cayley_of_skew_is_SO u : cayley_of_skew u \is 'SO[R]_3.
Proof. by rewrite rotationE cayley_of_skew_is_O det_caley eqxx. Qed.

Definition skew_of_ortho (M : 'M[R]_3) := (M - 1) * (M + 1)^-1.

Lemma skew_of_ortho_is_skew Q : Q \is 'O[R]_3 -> skew_of_ortho Q \is 'so[R]_3.
Proof.
move=> HQ.
rewrite antiE /skew_of_ortho.
rewrite trmx_mul trmxV.
rewrite linearD /= trmx1.
rewrite linearD /= linearN /= trmx1.
move: (HQ).
rewrite orthogonalEinv => /andP[Qinv] /eqP <-.
rewrite mulmxE -mulrN opprB idmxE; apply/eqP.
rewrite -[in RHS](mul1r (1 - Q^-1)).
rewrite -unitrV in Qinv.
rewrite -{4}(divrr Qinv).
rewrite -mulrA invrK (mulrBr Q) mulr1 divrr; last by rewrite -unitrV.
rewrite mulrA.
Abort.

Definition lie_bracket w1 w2 := \S( w1 ) * \S( w2) - \S( w2 ) * \S( w1 ).

Local Notation "[ w1 , w2 ]" := (lie_bracket w1 w2).

Lemma lie_bracketE w1 w2 : [ w1 , w2 ] = \S( w1 *v w2 ).
Proof.
Abort.

(* [murray] second half of exercise 9(a), p. 75 *)
Lemma kernel_skew_mx (w : 'rV[R]_3) (w0 : w != 0) : (kermx \S( w ) == w)%MS.
Proof.
apply/andP; split; last by apply/sub_kermxP; rewrite skew_mxE crossmulvv.
apply/rV_subP => v /sub_kermxP.
rewrite skew_mxE => /eqP/colinearP[|[_[k [Hk1 Hk2]]]].
  move/eqP => ->.
  by rewrite sub0mx.
apply/sub_rVP; exists (k^-1).
rewrite Hk2 scalerA mulVr ?scale1r // unitfE; apply: contra w0.
rewrite Hk2 => /eqP ->; by rewrite scale0r.
Qed.

End skew.

Notation "'\S(' w ')'" := (skew_mx w) (at level 3, format "'\S(' w ')'").
