(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop ssralg ssrint div.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import  mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.

Require Import ssr_ext euclidean3 vec_angle.
Require vec_angle.

(*
 OUTLINE:
 1. Section sym_anti
    Section anti_rcfType.
    Section anti_rcfType_dim3.
    Section sym_anti_numFieldType.
      sections on symmetric and antisymmetry matrices.
 2. Section axial_vector.
 3. Section spin_matrix
    Section spin_matrix_axial_vector_rcfType.
      properties of spin matrices and axial vectors
 4. Section spectral_properties.
      sample lemma: eigenvalues of spin matrices
 5. Section cayley_transform
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.

Reserved Notation "'\S(' w ')'" (at level 3, format "'\S(' w ')'").
Reserved Notation "''so[' R ]_ n" (at level 8, n at level 2, format "''so[' R ]_ n").

Local Open Scope ring_scope.

Section keyed_qualifiers_anti_sym.

Variables (n : nat) (R : ringType).

Definition anti := [qualify M : 'M[R]_n | M == - M^T].
Fact anti_key : pred_key anti. Proof. by []. Qed.
Canonical anti_keyed := KeyedQualifier anti_key.

Definition sym := [qualify M : 'M[R]_n | M == M^T].
Fact sym_key : pred_key sym. Proof. by []. Qed.
Canonical sym_keyed := KeyedQualifier sym_key.

End keyed_qualifiers_anti_sym.

Notation "''so[' R ]_ n" := (anti n R).

Section sym_anti.

Variables (R : ringType) (n : nat).
Implicit Types M A B : 'M[R]_n.
Implicit Types v : 'rV[R]_n.

Section sym.

Lemma symE M : (M \is sym n R) = (M == M^T). Proof. by []. Qed.

Lemma sym_cst a : a%:M \is sym n R. Proof. by rewrite symE tr_scalar_mx. Qed.

Lemma sym0 : 0 \is sym n R. Proof. by rewrite symE trmx0. Qed.

Lemma symP A B : A \in sym n R -> B \in sym n R ->
  (forall i j : 'I_n, (i <= j)%N -> A i j = B i j) -> A = B.
Proof.
move=> sA sB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite AB.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (sA) (sB) => /eqP -> /eqP ->; by rewrite 2!mxE AB // leq_eqVlt ij orbC.
by move=> {}ij; rewrite AB // leq_eqVlt ij orbC.
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

End sym.

Section anti.

Lemma antiE M : (M \is 'so[R]_n) = (M == - M^T). Proof. by []. Qed.

Lemma antiN M : (- M \is 'so[R]_n) = (M \is 'so[R]_n).
Proof. apply/idP/idP; by rewrite !antiE linearN /= opprK eqr_oppLR. Qed.

Lemma trmx_anti M : (M \is 'so[R]_n) = (M^T \is 'so[R]_n).
Proof.
apply/idP/idP => H; move: (H).
by rewrite antiE -eqr_oppLR => /eqP <-; rewrite antiN.
by rewrite antiE trmxK -eqr_oppLR => /eqP <-; rewrite antiN.
Qed.

Lemma anti_scaler_closed : GRing.scaler_closed 'so[R]_n.
Proof.
move=> ? ?; rewrite antiE => /eqP H; by rewrite antiE linearZ /= -scalerN -H.
Qed.
(* TODO: Canonical? *)

End anti.

End sym_anti.

Lemma mul_tr_vec_sym (R : comRingType) m (v : 'rV[R]_m) : v^T *m v \is sym m R.
Proof. apply/eqP; by rewrite trmx_mul trmxK. Qed.

Lemma conj_so (R : comRingType) n P M :
  M \is 'so[R]_n -> P^T *m M *m P \is 'so[R]_n.
Proof.
rewrite !antiE -eqr_oppLR => /eqP HM.
by rewrite !trmx_mul trmxK -HM !(mulNmx,mulmxN) opprK mulmxA.
Qed.

Section anti_rcfType.

Variables (R : numDomainType) (n : nat).
Implicit Types M A B : 'M[R]_n.

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

Lemma antiP A B : A \is 'so[R]_n -> B \is 'so[R]_n ->
  (forall i j : 'I_n, (i < j)%N -> A i j = - B j i) -> A = B.
Proof.
move=> soA soB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by do 2 rewrite anti_diag //.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (soA); by rewrite antiE => /eqP ->; rewrite 2!mxE AB // opprK.
move=> {}ij; rewrite AB //.
move: (soB); rewrite antiE -eqr_oppLR => /eqP/matrixP/(_ i j).
rewrite !mxE => <-; by rewrite opprK.
Qed.

End anti_rcfType.

Section anti_rcfType_dim3.

Lemma sqr_anti (R : numDomainType) (M : 'M[R]_3) : M \is 'so[R]_3 ->
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

End anti_rcfType_dim3.

Section sym_anti_numFieldType.

Variables (R : numFieldType) (n : nat).
Implicit Types M A B : 'M[R]_n.

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

End sym_anti_numFieldType.

Section axial_vector.

Variable R : ringType.
Implicit Types M : 'M[R]_3.

Definition axial M :=
  row3 (M 1 2%:R - M 2%:R 1) (M 2%:R 0 - M 0 2%:R) (M 0 1 - M 1 0).

Lemma axial_sym' M : M \is sym 3 R -> axial M = 0.
Proof.
rewrite symE => /eqP MMT; by rewrite /axial {1 3 5}MMT !mxE !subrr row30.
Qed.

Lemma axial_cst a : axial a%:M = 0 :> 'rV[R]_3.
Proof. by rewrite axial_sym' // sym_cst. Qed.

Lemma axial0 : axial 0 = 0 :> 'rV[R]_3.
Proof.
rewrite (_ : 0 = 0%:M) ?axial_cst //.
by apply/matrixP => ? ?; rewrite !mxE mul0rn.
Qed.

Lemma axialN M : axial (- M) = - axial M.
Proof. by rewrite /axial !mxE !opprK row3N !opprB 3!(addrC (- M _ _)). Qed.

Lemma axialZ k M : axial (k *: M) = k *: axial M.
Proof. by rewrite {2}/axial row3Z /axial !mulrBr !mxE. Qed.

Lemma axialD (A B : 'M[R]_3) : axial (A + B) = axial A + axial B.
Proof.
rewrite /axial !row3D !mxE -!addrA; congr (row3 (_ + _) (_ + _) (_ + _));
  rewrite addrC opprD -!addrA; congr (_ + _); by rewrite addrC.
Qed.

Lemma tr_axial M : axial M^T = - axial M.
Proof. by rewrite /axial !mxE row3N 3!opprB. Qed.

End axial_vector.

Section spin_matrix.

Variable R : comRingType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.
Implicit Types M : 'M[R]_3.

Definition spin u : 'M[R]_3 := \matrix_i (u *v 'e_i).

Local Notation "'\S(' u ')'" := (spin u).

Lemma spinE u v : u *m \S( v ) = v *v u.
Proof.
rewrite crossmulC -crossmulNv [RHS]crossmulC -crossmulvN [u]row_sum_delta.
rewrite -/(mulmxr _ _) !linear_sum /=; apply: eq_bigr=> i _.
by rewrite !linearZ /= -scalemxAl -rowE linearN /= rowK crossmulvN opprK.
Qed.

Lemma spin0 : \S( 0 ) = 0.
Proof. by apply/matrixP => i j; rewrite /spin mxE crossmul0v 2!mxE. Qed.

(* this should generalize mulmxP *)
Lemma mulmatP M N : reflect (forall u, u *m M = u *m N) (M == N).
Proof.
apply: (iffP idP) => [/eqP->|MeN] //.
by apply/eqP/row_matrixP => i; rewrite !rowE.
Qed.

Lemma spinD u v : \S(u + v) = \S(u) + \S(v).
Proof. apply/eqP/mulmatP => w; by rewrite mulmxDr !spinE crossmulDl. Qed.

Lemma spinZ k u : \S( k *: u ) = k *: \S( u ).
Proof.
apply/matrixP => i j.
by rewrite mxE crossmulC linearZ /= -scalerN crossmulC opprK mxE 2![in RHS]mxE.
Qed.

Lemma spinN u : \S( - u ) = - \S( u ).
Proof. by rewrite -scaleN1r spinZ scaleN1r. Qed.

Lemma spin_is_so u : \S( u ) \is 'so[R]_3.
Proof.
rewrite antiE; apply/eqP/matrixP => i j; rewrite !mxE -col_mx3_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma tr_spin u : \S( u )^T = - \S( u ).
Proof. by move: (spin_is_so u); rewrite antiE -eqr_oppLR => /eqP <-. Qed.

Lemma mul_spin M u :
  M * \S( u ) = col_mx3 (u *v row 0 M) (u *v row 1 M) (u *v row 2%:R M).
Proof. by rewrite {1}(col_mx3_rowE M) -mulmxE mulmx_col3 !spinE. Qed.

Lemma spin01 u : \S( u ) 0 1 = u``_2%:R.
Proof. by rewrite /spin mxE crossmulE !mxE /= !(mulr0,mulr1,addr0,subr0). Qed.

Lemma spin02 u : \S( u ) 0 2%:R = - u``_1%:R.
Proof. by rewrite /spin mxE crossmulE !mxE /= !(mulr0,mulr1,add0r,opprK). Qed.

Lemma spin10 u : \S( u ) 1 0 = - u``_2%:R.
Proof. by move/eqP: (spin_is_so u) => ->; rewrite 2!mxE spin01. Qed.

Lemma spin12 u : \S( u ) 1 2%:R = u``_0.
Proof. by rewrite /spin mxE crossmulE !mxE /= !(mulr0, mulr1, subr0). Qed.

Lemma spin20 u : \S( u ) 2%:R 0 = u``_1%:R.
Proof. move/eqP: (spin_is_so u) => ->; by rewrite 2!mxE spin02 opprK. Qed.

Lemma spin21 u : \S( u ) 2%:R 1 = - u``_0.
Proof. move/eqP: (spin_is_so u) => ->; by rewrite 2!mxE spin12. Qed.

Lemma spin_mul_tr u : \S( u ) *m u^T = 0.
Proof.
rewrite -(trmxK (spin u)) -trmx_mul tr_spin.
by rewrite mulmxN spinE crossmulvv oppr0 trmx0.
Qed.

End spin_matrix.

Notation "'\S(' w ')'" := (spin w).

Section unspin_matrix.

Variable R : comUnitRingType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.
Implicit Types M : 'M[R]_3.

(* normalized axial vector *)
Definition unspin M := 2%:R^-1 *: axial M.

Lemma unspin_sym M : M \is sym 3 R -> unspin M = 0.
Proof. by move=> HM; rewrite /unspin axial_sym' // scaler0. Qed.

Lemma unspin_cst a : unspin a%:M = 0 :> 'rV[R]_3.
Proof. by rewrite unspin_sym // sym_cst. Qed.

Lemma unspin0 : unspin 0 = 0 :> 'rV[R]_3.
Proof. by rewrite /unspin axial0 ?scaler0. Qed.

Lemma unspinN M : unspin (- M) = - unspin M.
Proof. by rewrite /unspin axialN scalerN. Qed.

Lemma unspinZ k M : unspin (k *: M) = k *: unspin M.
Proof. by rewrite /unspin axialZ scalerA mulrC -scalerA. Qed.

Lemma unspinD (A B : 'M[R]_3) : unspin (A + B) = unspin A + unspin B.
Proof. by rewrite /unspin axialD scalerDr. Qed.

End unspin_matrix.

(* skew-symmetric matrices are always singular *)
Lemma det_spin (R : idomainType) (u : 'rV[R]_3) : \det \S( u ) = 0.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite spin0 det0.
apply/eqP/det0P; exists u => //; by rewrite spinE crossmulvv.
Qed.

Section spin_matrix_axial_vector_rfType.

Variable R : realFieldType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.
Implicit Types M : 'M[R]_3.

(* [sciavicco] eqn 3.9 *)
Lemma spin_similarity (M : 'M[R]_3) (w : 'rV[R]_3) :
  M \is 'SO[R]_3 -> M^T * \S(w) * M = \S(w *m M).
Proof.
move=> MSO; apply/eqP/complex.mulmxP => u.
rewrite -mulmxE !mulmxA spinE (mulmxr_crossmulr_SO _ _ MSO).
by rewrite -mulmxA orthogonal_tr_mul ?rotation_sub // mulmx1 spinE.
Qed.

Lemma spin_crossmul u v : \S(v *v u) = \S(u) *m \S(v) - \S(v) *m \S(u).
Proof.
apply/eqP/mulmxP => w.
rewrite [in LHS]spinE mulmxBr !mulmxA ![in RHS]spinE.
rewrite (crossmulC v w) crossmulvN opprK.
move/eqP: (jacobi_crossmul v u w); rewrite eq_sym -subr_eq eq_sym => /eqP ->.
by rewrite add0r (crossmulC w) opprK.
Qed.

Lemma spinii u i : \S( u ) i i = 0.
Proof. by rewrite anti_diag // spin_is_so. Qed.

Definition spinij := (spin01, spin10, spin02, spin20, spin21, spin12, spinii).

Lemma axial_spin u : axial \S( u ) = 2%:R *: u.
Proof.
rewrite /axial !spinij !opprK -!mulr2n -3!(mulr_natr (u``_ _)).
rewrite !(mulrC _ 2%:R) -row3Z; congr (_ *: _).
by rewrite [RHS](row3_proj u) !row3D !(addr0,add0r).
Qed.

Lemma spin_axial_so M : M \is 'so[R]_3 -> \S( axial M ) = 2%:R *: M.
Proof.
move=> Mso.
move: (Mso); rewrite antiE => /eqP MMT.
apply/matrix3P/and9P; split; rewrite spinij ?anti_diag // ?mxE /= ?anti_scaler_closed //.
- by rewrite {2}MMT !mxE opprK -mulr2n -(mulr_natr (M _ _)) mulrC.
- by rewrite {1}MMT !mxE opprB opprK -mulr2n -(mulr_natr (M _ _)) mulrC.
- by rewrite {1}MMT !mxE opprB opprK -mulr2n -(mulr_natr (M _ _)) mulrC.
- by rewrite {2}MMT !mxE opprK -mulr2n -(mulr_natr (M _ _)) mulrC.
- by rewrite {2}MMT !mxE opprK -mulr2n -(mulr_natr (M _ _)) mulrC.
- by rewrite {1}MMT !mxE opprB opprK -mulr2n -(mulr_natr (M _ _)) mulrC.
Qed.

Lemma spinK u : unspin \S( u ) = u.
Proof.
by rewrite /unspin axial_spin scalerA mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Lemma unspinK M : M \is 'so[R]_3 -> \S( unspin M ) = M.
Proof.
move=> Mso.
rewrite /unspin spinZ spin_axial_so // scalerA mulVr ?scale1r //.
by rewrite unitfE pnatr_eq0.
Qed.

Lemma spin_inj u v : (\S( u ) == \S( v )) = (u == v).
Proof.
apply/idP/idP => [/eqP H|/eqP -> //]; by rewrite -(spinK u) H spinK.
Qed.

Lemma spin_axial M : \S( axial M ) = M - M^T.
Proof.
have /unspinK : M - M^T \is 'so[R]_3 by rewrite antiE linearB /= trmxK opprB.
rewrite /unspin spinZ axialD spinD axialN spinN tr_axial spinN.
by rewrite opprK -mulr2n -scaler_nat scalerA mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Lemma axial_sym M : (M \is sym 3 R) = (axial M == 0).
Proof.
apply/idP/idP => [|/eqP H]; [by move/axial_sym' => -> |rewrite symE].
by rewrite -subr_eq0 -spin_axial H spin0.
Qed.

Lemma axialE M : axial M = unspin (M - M^T).
Proof. by rewrite -(spin_axial M) spinK. Qed.

Lemma axial_vecP (M : 'M[R]_3) u : u *v axial M = u *m antip M.
Proof.
rewrite /antip.
rewrite crossmulC.
rewrite -spinE.
rewrite axialE.
rewrite unspinK.
Abort.

Lemma sqr_spin' u : \S( u ) ^+ 2 = col_mx3
  (row3 (- u 0 2%:R ^+ 2 - u 0 1 ^+ 2) (u 0 0 * u 0 1) (u 0 0 * u 0 2%:R))
  (row3 (u 0 0 * u 0 1) (- u 0 2%:R ^+ 2 - u 0 0 ^+ 2) (u 0 1 * u 0 2%:R))
  (row3 (u 0 0 * u 0 2%:R) (u 0 1 * u 0 2%:R) (- u 0 1%:R ^+ 2 - u 0 0 ^+ 2)).
Proof.
rewrite (sqr_anti (spin_is_so u)); congr col_mx3.
by rewrite !spinij sqrrN; Simp.r; rewrite (mulrC (u 0 2%:R)).
by rewrite !spinij; Simp.r; rewrite (mulrC (u 0 2%:R)).
by rewrite !spinij sqrrN; Simp.r.
Qed.

Lemma sqr_spin_is_sym u : \S( u ) ^+ 2 \is sym 3 R.
Proof.
rewrite symE sqr_spin'; by apply/eqP/matrix3P/and9P; split; rewrite !mxE.
Qed.

(* [murray] second half of exercise 9(a), p. 75 *)
Lemma kernel_spin (w : 'rV[R]_3) (w0 : w != 0) : (kermx \S( w ) == w)%MS.
Proof.
apply/andP; split; last by apply/sub_kermxP; rewrite spinE crossmulvv.
apply/rV_subP => v /sub_kermxP.
rewrite spinE => /eqP/vec_angle.colinearP[|[_[k Hk]]].
  move/eqP => ->.
  by rewrite sub0mx.
apply/sub_rVP; exists (k^-1).
rewrite Hk scalerA mulVr ?scale1r // unitfE; apply: contra w0.
rewrite Hk => /eqP ->; by rewrite scale0r.
Qed.

End spin_matrix_axial_vector_rfType.

Section spin_matrix_axial_vector_rcfType.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.
Implicit Types M : 'M[R]_3.

Lemma sqr_spin u : \S( u ) ^+ 2 = u^T *m u - (norm u ^+ 2)%:A.
Proof.
apply (symP (sqr_spin_is_sym u)); last move=> i j.
  rewrite rpredD //; last by rewrite rpredN sym_scaler_closed // sym_cst.
  by rewrite mul_tr_vec_sym.
rewrite [in X in _ -> _ = X]mxE mulmx_trE.
case/boolP : (i == 0) => [/eqP-> _|/ifnot0P/orP[]/eqP->].
- case/boolP : (j == 0) => [|/ifnot0P/orP[]]/eqP->.
  + rewrite sqr_spin' 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE
      sum3E -!expr2 -addrA addrCA addrAC -addrA.
  + by rewrite sqr_spin' 5!mxE /= mulr0 subr0.
  + by rewrite sqr_spin' 5!mxE /= mulr0 subr0.
- case/boolP : (j == 0) => [/eqP-> //|/ifnot0P/orP[]/eqP-> _].
  + rewrite sqr_spin' 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE
      sum3E -!expr2 addrAC.
  + by rewrite sqr_spin' 5!mxE /= mulr0 subr0.
- case/boolP : (j == 0) => [/eqP-> //|/ifnot0P/orP[]/eqP-> // _].
  rewrite sqr_spin' 5!mxE /= -expr2 mulr1; apply/eqP.
  by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE sum3E -!expr2.
Qed.

Lemma spin3 u : \S( u ) ^+ 3 = - (norm u) ^+ 2 *: \S( u ).
Proof.
rewrite exprS sqr_spin mulrBr -mulmxE mulmxA spin_mul_tr mul0mx add0r.
by rewrite scalemx1 mul_mx_scalar scaleNr.
Qed.

Lemma exp_spin u n : \S( u ) ^+ n.+3 = - (norm u) ^+ 2 *: \S( u ) ^+ n.+1.
Proof.
elim: n => [|n IH]; by [rewrite expr1 spin3|rewrite exprS IH -scalerAr -exprS].
Qed.

Lemma mxtrace_sqr_spin u : \tr (\S( u ) ^+ 2) = - (2%:R * (norm u) ^+ 2).
Proof.
rewrite sqr_spin linearD /= mxtrace_tr_mul linearN /= linearZ /=; apply/eqP.
by rewrite !mxtrace_scalar subr_eq addrC mulrC -mulrBl -natrB // mul1r.
Qed.

End spin_matrix_axial_vector_rcfType.

Section spectral_properties.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.

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

Lemma char_poly_spin u : char_poly \S( u ) = 'X^3 + norm u ^+2 *: 'X.
Proof.
rewrite char_poly3 det_spin subr0 trace_anti ?spin_is_so //.
rewrite scale0r subr0 expr0n add0r mulrN mxtrace_sqr_spin mulrN opprK.
by rewrite mulrA div1r mulVr ?unitfE ?pnatr_eq0 // mul1r.
Qed.

Definition spin_eigenvalues u : seq R[i] := [:: 0; 0 +i* norm u ; 0 -i* norm u]%C.

Ltac eigenvalue_spin_eval_poly :=
  rewrite /map_poly horner_poly size_addl; [ |
    by rewrite size_polyXn size_scale ?size_polyX // sqrf_eq0 norm_eq0];
  rewrite size_polyXn sum4E !(coefD,coefXn,coefZ,coefX,expr0,expr1)
                            !(mulr0,mul0r,mul1r,add0r,addr0,mul1r).

Lemma eigenvalue_spin u : u != 0 ->
  eigenvalue (map_mx (fun x => x%:C%C) \S( u) ) =1 [pred k | k \in spin_eigenvalues u].
Proof.
move=> u0 /= k.
rewrite inE eigenvalue_root_char -map_char_poly char_poly_spin.
apply/rootP.
case: ifPn => [|Hk].
- rewrite inE => /orP [/eqP ->|]; first by rewrite /= horner_map !hornerE.
  rewrite inE => /orP [/eqP ->|].
    eigenvalue_spin_eval_poly.
    simpc.
    apply/eqP; by rewrite expr2 mulrA subrr eq_complex /= eqxx.
  rewrite inE => /eqP ->.
  eigenvalue_spin_eval_poly.
  simpc.
  apply/eqP; by rewrite expr2 mulrA addrC subrr eq_complex /= eqxx.
- apply/eqP; apply: contra Hk.
  eigenvalue_spin_eval_poly.
  rewrite eqxx mulr1 mulrC (exprS _ 2) -mulrDr mulf_eq0 => /orP [/eqP ->|].
    by rewrite inE eqxx.
  rewrite eq_sym addrC -subr_eq add0r -mulN1r -sqr_i => H.
  have {H}: (norm u)*i%C ^+2 == k ^+2.
    rewrite -(eqP H) eq_complex. simpc. by rewrite /= !(mulr0,add0r,mul0r,eqxx).
  rewrite eqf_sqr => /orP [/eqP <-|].
    by rewrite !inE eqxx orbC.
  rewrite -eqr_oppLR => /eqP <-.
  rewrite !inE orbA; apply/orP; right.
  by rewrite eq_complex /= oppr0 !eqxx.
Qed.

Lemma is_eigenvector1_colinear r (Hr : r \is 'SO[R]_3) n :
  (n <= eigenspace r 1)%MS -> colinear n (axial r).
Proof.
move=> Hn.
have HnT : n *m r^T = n.
  move/eigenspace_trmx : Hn => /(_ (rotation_sub Hr))/eigenspaceP.
  by rewrite scale1r.
set Q := r^T - r.
have nrrT : n *m Q = 0.
 rewrite mulmxDr [in LHS]mulmxN HnT.
 move/eigenspaceP : Hn; rewrite scale1r => ->.
 by rewrite subrr.
have skewrrT : \S( - axial r ) = Q.
  rewrite axialE // -scaleN1r spinZ scaleN1r unspinK ?opprB //.
  by rewrite antiE linearD /= linearN /= trmxK opprB.
move/eqP: nrrT.
by rewrite -skewrrT spinE crossmulC crossmulvN opprK.
Qed.

Lemma axial_vec_eigenspace M : M \is 'SO[R]_3 ->
  (axial M <= eigenspace M 1)%MS.
Proof.
move=> MSO; apply/eigenspaceP; rewrite scale1r.
case: (euler MSO) => u /andP[u0 /eqP uMu].
have /is_eigenvector1_colinear : (u <= eigenspace M 1)%MS.
  by apply/eigenspaceP; rewrite scale1r.
move/(_ MSO) => uax.
suff [k Hk] : exists k, axial M = k *: u by rewrite Hk -scalemxAl uMu.
case/colinearP : uax => [/eqP ->| [_ [k ukv]]].
  exists 0; by rewrite scale0r.
exists (1 / k); rewrite ukv scalerA div1r mulVr ?scale1r // unitfE.
apply: contra u0; rewrite ukv => /eqP ->; by rewrite scale0r.
Qed.

End spectral_properties.

Section cayley_transform.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.

(* TODO: move? *)
Lemma sub1radd1r_comm n (M : 'M[R]_n.+1) : (1 - M) * (1 + M) = (1 + M) * (1 - M).
Proof. by rewrite mulrDr mulr1 mulrBl mul1r mulrDl mul1r mulrBr mulr1. Qed.

Lemma det_sub1spin u : \det (1 - \S( u )) = 1 + norm u ^+ 2.
Proof.
set a := \S( u ).
rewrite det_mx33 [a]lock !mxE /=. Simp.r.
rewrite -lock /a !spinij subr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
by rewrite mulrBr opprB addrA mulrDr addrA mulrCA subrK addrAC sqr_norm sum3E.
Qed.

Lemma det_add1spin u : \det (1 + \S( u )) = 1 + norm u ^+ 2.
Proof.
set a := \S( u ).
rewrite det_mx33 [a]lock !mxE /=. Simp.r.
rewrite -lock /a !spinij addr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
rewrite sqr_norm sum3E -!expr2 -!addrA; congr (_ + _).
rewrite mulrDr -expr2 (addrC _ (_^+2)) -!addrA addrC; congr (_ + _).
by rewrite mulrBr opprB -expr2 addrCA mulrCA subrr addr0.
Qed.

Lemma sym_add1r M : M \is 'so[R]_3 -> \det (1 + M) != 0.
Proof.
move/unspinK => <-; by rewrite det_add1spin paddr_eq0 // ?sqr_ge0 // oner_eq0.
Qed.

Lemma sym_sub1r M : M \is 'so[R]_3 -> \det (1 - M) != 0.
Proof.
move/unspinK => <-; by rewrite det_sub1spin paddr_eq0 // ?sqr_ge0 // oner_eq0.
Qed.

Lemma sub1spin_inv u : 1 - \S( u ) \is a GRing.unit.
Proof. by rewrite unitmxE unitfE sym_sub1r // spin_is_so. Qed.

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
move/unspinK => <-.
rewrite /ortho_of_skew det_mulmx det_inv det_add1spin det_sub1spin.
by rewrite divrr // unitfE paddr_eq0 ?oner_eq0 /= // sqr_ge0.
Qed.

(* [murray] exercise 5.(a), p.73 *)
Lemma ortho_of_skew_is_SO M : M \is 'so[R]_3 -> ortho_of_skew M \is 'SO[R]_3.
Proof.
move=> Mso; by rewrite rotationE ortho_of_skew_is_O //= det_ortho_of_skew.
Qed.

End cayley_transform.
