(* coq-robot (c) 2025 AIST and INRIA. License: LGPL-2.1-or-later. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat poly.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import realalg complex finset fingroup perm ring.
Require Import ssr_ext euclidean vec_angle.
From mathcomp Require Import reals.

(**md**************************************************************************)
(* # Skew-symmetric matrices                                                  *)
(*                                                                            *)
(* This file develops the theory of skew-symmetric matrices to be used in     *)
(* particular to represent the exponential coordinates of rotation matrices.  *)
(*                                                                            *)
(* ```                                                                        *)
(* 'so[R]_n == the type of skew-symmetric matrices, i.e., matrices M such     *)
(*              that M = -M^T                                                 *)
(*    \S(w) == the spin of vector w, i.e., the (row-vector convention)        *)
(*             skew-symmetric matrix corresponding to the vector w            *)
(*   symp A == symmetric part of matrix A                                     *)
(*  antip A == antisymmetric part of matrix A                                 *)
(*  spin_eigenvalues u == eigenvalues of \S(u)                                *)
(* ```                                                                        *)
(*                                                                            *)
(* Cayley transform:                                                          *)
(* ```                                                                        *)
(*    cayley M == (1 - M)^-1 * (1 + M)                                        *)
(*  uncayley M == (M - 1) * (M + 1)^-1                                        *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.

Reserved Notation "'\S(' w ')'" (at level 3, format "'\S(' w ')'").
Reserved Notation "''so[' R ]_ n" (at level 8, n at level 2, format "''so[' R ]_ n").

Local Open Scope ring_scope.

Section keyed_qualifiers_anti_sym.

Variables (n : nat) (R : pzRingType).

Definition anti := [qualify M : 'M[R]_n | M == - M^T].
Fact anti_key : pred_key anti. Proof. by []. Qed.
Canonical anti_keyed := KeyedQualifier anti_key.

Definition sym := [qualify M : 'M[R]_n | M == M^T].
Fact sym_key : pred_key sym. Proof. by []. Qed.
Canonical sym_keyed := KeyedQualifier sym_key.

End keyed_qualifiers_anti_sym.

Notation "''so[' R ]_ n" := (anti n R).

Section sym_anti.

Variables (R : pzRingType) (n : nat).
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

HB.instance Definition _ := GRing.isAddClosed.Build _ _ sym_addr_closed.
HB.instance Definition _ := GRing.isOppClosed.Build _ _ sym_oppr_closed.

Lemma sym_scaler_closed : GRing.scaler_closed (sym n R).
Proof. move=> ? ?; rewrite 2!symE => /eqP H; by rewrite linearZ /= -H. Qed.
(* TODO: Canonical? *)

HB.instance Definition _ := GRing.isScaleClosed.Build _ _ _ sym_scaler_closed.

End sym.

Section anti.

Lemma antiE M : (M \is 'so[R]_n) = (M == - M^T). Proof. by []. Qed.

Lemma antiP M : M \is 'so[R]_n -> M^T = - M.
Proof. by rewrite antiE -eqr_oppLR => /eqP <-. Qed.

Lemma antiN M : (- M \is 'so[R]_n) = (M \is 'so[R]_n).
Proof. by apply/idP/idP; rewrite !antiE linearN /= opprK eqr_oppLR. Qed.

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

Lemma mul_tr_vec_sym (R : comPzRingType) m (v : 'rV[R]_m) : v^T *m v \is sym m R.
Proof. apply/eqP; by rewrite trmx_mul trmxK. Qed.

Lemma conj_so (R : comPzRingType) n P M :
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

Lemma anti_ext A B : A \is 'so[R]_n -> B \is 'so[R]_n ->
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

Variable R : pzRingType.
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

Variable R : comNzRingType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.
Implicit Types M : 'M[R]_3.

Definition spin u : 'M[R]_3 := locked (\matrix_i (u *v 'e_i)).

Local Notation "'\S(' u ')'" := (spin u).

Lemma spinE u v : u *m \S( v ) = v *v u.
Proof.
rewrite (@lieC _ (vec3 R)) -linearNr [RHS]lieC/= -linearNr [u]row_sum_delta/=.
rewrite -/(mulmxr _ _) !linear_sum /=; apply: eq_bigr=> i _.
rewrite /spin; unlock.
rewrite 2!linearZ/=.
rewrite -scalemxAl -rowE.
rewrite (linearNr _ (- v))/=.
rewrite (@lieC _ (vec3 R)) opprK/=.
rewrite rowK.
rewrite (@lieC _ (vec3 R))/=.
by rewrite [in RHS]linearN/=.
Qed.

Lemma spin0 : \S( 0 ) = 0.
Proof.
apply/matrixP => i j; rewrite /spin; unlock.
by rewrite mxE linear0l 2!mxE.
Qed.

(* this should generalize mulmxP *)
Lemma mulmatP M N : reflect (forall u, u *m M = u *m N) (M == N).
Proof.
apply: (iffP idP) => [/eqP->|MeN] //.
by apply/eqP/row_matrixP => i; rewrite !rowE.
Qed.

Lemma spinD u v : \S(u + v) = \S(u) + \S(v).
Proof. apply/eqP/mulmatP => w; by rewrite mulmxDr !spinE linearDl. Qed.

Lemma spinZ k u : \S( k *: u ) = k *: \S( u ).
Proof.
apply/matrixP => i j.
rewrite /spin; unlock.
by rewrite mxE (@lieC _ (vec3 R)) /= linearZ /= -scalerN (@lieC _ (vec3 R)) opprK mxE 2![in RHS]mxE.
Qed.

Lemma spinN u : \S( - u ) = - \S( u ).
Proof. by rewrite -scaleN1r spinZ scaleN1r. Qed.

Lemma spin_is_so u : \S( u ) \is 'so[R]_3.
Proof.
rewrite antiE; apply/eqP/matrixP => i j.
rewrite mxE.
rewrite /spin; unlock.
rewrite !mxE.
rewrite /crossmul; unlock.
rewrite !mxE -col_mx3_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma tr_spin u : \S( u )^T = - \S( u ).
Proof. by move: (spin_is_so u); rewrite antiE -eqr_oppLR => /eqP <-. Qed.

Lemma mul_spin M u :
  M * \S( u ) = col_mx3 (u *v row 0 M) (u *v row 1 M) (u *v row 2%:R M).
Proof. by rewrite -3!spinE col_mx3_mul col_mx3_row. Qed.

Lemma spin01 u : \S( u ) 0 1 = u``_2%:R.
Proof.
rewrite /spin; unlock.
by rewrite /spin mxE crossmulE !mxE /= !(mulr0,mulr1,addr0,subr0).
Qed.

Lemma spin02 u : \S( u ) 0 2%:R = - u``_1%:R.
Proof.
rewrite /spin; unlock.
by rewrite /spin mxE crossmulE !mxE /= !(mulr0,mulr1,add0r,opprK).
Qed.

Lemma spin10 u : \S( u ) 1 0 = - u``_2%:R.
Proof.
by move/eqP: (spin_is_so u) => ->; rewrite 2!mxE spin01.
Qed.

Lemma spin12 u : \S( u ) 1 2%:R = u``_0.
Proof.
rewrite /spin; unlock.
by rewrite /spin mxE crossmulE !mxE /= !(mulr0, mulr1, subr0).
Qed.

Lemma spin20 u : \S( u ) 2%:R 0 = u``_1%:R.
Proof. by move/eqP: (spin_is_so u) => ->; rewrite 2!mxE spin02 opprK. Qed.

Lemma spin21 u : \S( u ) 2%:R 1 = - u``_0.
Proof. by move/eqP: (spin_is_so u) => ->; rewrite 2!mxE spin12. Qed.

Lemma spin_mul_tr u : \S( u ) *m u^T = 0.
Proof.
rewrite -(trmxK (spin u)) -trmx_mul tr_spin.
by rewrite mulmxN spinE (@liexx _ (vec3 R)) oppr0 trmx0.
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
apply/eqP/det0P; exists u => //.
by rewrite spinE (@liexx _ (vec3 R)).
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
rewrite (@lieC _ (vec3 R) v w)/=.
rewrite linearN/= opprK.
move/eqP: (@jacobi _ (vec3 R) v u w); rewrite eq_sym -subr_eq eq_sym => /eqP -> /=.
by rewrite add0r (@lieC _ (vec3 R) w) opprK.
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

Lemma axial_vecP (M : 'M[R]_3) u : axial M *v u  = u *m (2%:R *: antip M).
Proof.
rewrite axialE -spinE (_ : _ - _ = 2%:R *: antip M); last first.
  by rewrite scalerA mulrC divfK ?scale1r // (eqr_nat _ 2 0).
by rewrite unspinZ spinZ unspinK ?antip_is_so.
Qed.

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
apply/andP; split; last by apply/sub_kermxP; rewrite spinE (@liexx _ (vec3 R)).
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
  rewrite rpredD//= ?mul_tr_vec_sym//.
  by rewrite sym_oppr_closed (*TODO: why can't we use rpredN*)// sym_scaler_closed// sym_cst.
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
  rewrite /map_poly horner_poly size_polyDl; [ |
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
- rewrite inE => /orP [/eqP ->|]; first by rewrite /= horner_map/= !hornerE/= expr0n.
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
by rewrite -skewrrT spinE (@lieC _ (vec3 R) (- (axial r))) /= linearNr opprK.
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

Lemma skew_anti (R : rcfType) n (M : 'M[R]_n.+1) : M \is 'so[R]_n.+1 -> M = - M^T.
Proof. by move=> Mso; apply/eqP; rewrite -antiE. Qed.

(* NB: wip *)
Section cayley_transform.

Variable R : realType.
Let vector := 'rV[R]_3.
Implicit Types u : vector.

(* TODO: move? *)
Lemma skew_dotmulmx n (M : 'M[R]_n.+1) v : M \is 'so[R]_n.+1 ->
  v *d (v *m M) = - v *d (v *m M).
Proof.
move=> Mso; rewrite dotmul_trmx dotmulC [in RHS](skew_anti Mso).
by rewrite mulmxN dotmulvN dotmulNv opprK.
Qed.

(* TODO: move? *)
Lemma skew_det1BM n (M : 'M[R]_n.+1) : M \is 'so[R]_n.+1 -> \det (1 - M) != 0.
Proof.
move=> Mso; apply/det0P => -[v v0]; apply/eqP; rewrite mulmxBr mulmx1 subr_eq0.
apply: contra v0 => /eqP v1M; rewrite -norm_eq0 -sqrf_eq0 -dotmulvv {2}v1M.
  by have /eqP := skew_dotmulmx v Mso; rewrite -eq_sym dotmulNv eqrNxx.
Qed.

(* TODO: move? *)
Lemma skew_det1DM n (M : 'M[R]_n.+1) : M \is 'so[R]_n.+1 -> \det (1 + M) != 0.
Proof.
move=> Mso; apply/det0P => -[v v0]; apply/eqP; rewrite mulmxDr mulmx1 addr_eq0.
apply: contra v0 => /eqP v1M; rewrite -norm_eq0 -sqrf_eq0 -dotmulvv {2}v1M.
have /eqP := skew_dotmulmx v Mso.
by rewrite -eq_sym dotmulNv eqrNxx dotmulvN eqr_oppLR oppr0.
Qed.

Lemma inv1BM u : (1 - \S(u)) *
  (1 + (1 + (norm u)^+2)^-1 *: \S(u) + (1 + (norm u)^+2)^-1 *: \S(u)^+2) = 1.
Proof.
rewrite mulrDr 2!mulrBl 2!mul1r.
apply/eqP; rewrite eq_sym addrC -subr_eq; apply/eqP.
rewrite opprD addrA opprD addrA subrr add0r opprK addrC.
rewrite mulrDr mulr1 (addrC \S(u)) scalerAr -addrA; congr (_ + _).
rewrite mulrA -expr2 -scalerAr -exprSr spin3 -{1}(scale1r \S(u)).
rewrite -{1}(@divff _ (1 + norm u ^+ 2)) ?paddr_eq0 ?oner_eq0 ?sqr_ge0//.
rewrite mulrC -scalerA -scalerBr -scalerN scaleNr opprK; congr (_ *: _).
by rewrite scalerDl scale1r addrAC subrr add0r.
Qed.

Lemma inv1BME u : (1 - \S(u))^-1 =
  1 + (1 + (norm u)^+2)^-1 *: \S(u) + (1 + (norm u)^+2)^-1 *: \S(u)^+2.
Proof.
rewrite -[LHS]mulmx1 -[X in _ *m X = _](inv1BM u) mulmxA mulVmx ?mul1mx//.
by rewrite unitmxE unitfE skew_det1BM // spin_is_so.
Qed.

(* TODO: move? *)
Lemma det_sub1spin3E M : M \is 'so[R]_3 -> \det (1 - M) = 1 + norm (unspin M) ^+ 2.
Proof.
move=> Mso; rewrite -{1}(unspinK Mso); set v := \S( _ ).
rewrite det_mx33 [v]lock !mxE /=. Simp.r.
rewrite -lock /v !spinij subr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
by rewrite mulrBr opprB addrA mulrDr addrA mulrCA subrK addrAC sqr_norm sum3E.
Qed.

(* TODO: move? *)
Lemma det_add1spin3E M : M \is 'so[R]_3 -> \det (1 + M) = 1 + norm (unspin M) ^+ 2.
Proof.
move=> Mso; rewrite -{1}(unspinK Mso); set v := \S( _ ).
rewrite det_mx33 [v]lock !mxE /=. Simp.r.
rewrite -lock /v !spinij addr0. Simp.r.
rewrite -!addrA; congr (_ + _); rewrite !addrA.
rewrite sqr_norm sum3E -!expr2 -!addrA; congr (_ + _).
rewrite mulrDr -expr2 (addrC _ (_^+2)) -!addrA addrC; congr (_ + _).
by rewrite mulrBr opprB -expr2 addrCA mulrCA subrr addr0.
Qed.

(* TODO: move? *)
Lemma mul1B1D_comm n (M : 'M[R]_n.+1) : (1 - M) *m (1 + M) = (1 + M) *m (1 - M).
Proof.
by rewrite mulmxDr mulmx1 mulmxBl mul1mx mulmxDl mul1mx mulmxBr mulmx1.
Qed.

(* skew matrix -> orthogonal matrix *)
Definition cayley n (M : 'M[R]_n.+1) := (1 - M)^-1 * (1 + M).

Lemma cayley_is_O n (M : 'M[R]_n.+1) : M \is 'so[R]_n.+1 -> cayley M \is 'O[R]_n.+1.
Proof.
move=> Mso; rewrite orthogonalE /cayley trmx_mul linearD /= trmx1.
rewrite {3}(skew_anti Mso) linearN /= trmxK.
rewrite trmxV linearD /= trmx1 linearN /=.
rewrite {4}(skew_anti Mso) !linearN /= trmxK opprK.
rewrite -!mulmxE.
rewrite mulmxA -(mulmxA _^-1) -mul1B1D_comm mulmxA mulVmx ?mul1mx; last first.
  by rewrite unitmxE unitfE skew_det1BM.
by rewrite mulmxV // unitmxE unitfE skew_det1DM.
Qed.

(* TODO: move? *)
Lemma ortho_N1eigen_invertible n M : M \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue M -> M + 1 \is a GRing.unit.
Proof.
move=> MO N1; rewrite unitmxE unitfE; apply: contra N1 => /det0P[x x0 /eqP].
rewrite mulmxDr mulmx1 addr_eq0 eq_sym eqr_oppLR => /eqP Hx.
by apply/eigenvalueP; exists x => //; rewrite scaleN1r {2}Hx opprK.
Qed.

(* orthogonal matrix -> skew matrix *)
Definition uncayley n (M : 'M[R]_n.+1) := (M - 1) * (M + 1)^-1.

(* TODO: move? *)
Lemma ortho_N1eigen_comm n (M : 'M[R]_n.+1) : M \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue M -> M * (M + 1)^-1 = (M + 1)^-1 * M.
Proof.
move=> MO MN1; rewrite -{1}(invrK M) -invrM; last 2 first.
  by rewrite ortho_N1eigen_invertible.
  by rewrite orthogonal_inv // unitr_trmx ?orthogonal_unit.
rewrite mulrDl divrr ?orthogonal_unit // div1r (orthogonal_inv MO).
rewrite -{1}(orthogonal_tr_mul MO) -{2}(mulr1 M^T) -mulrDr invrM; last 2 first.
  by rewrite unitr_trmx orthogonal_unit.
  by rewrite ortho_N1eigen_invertible.
by rewrite -trmxV (orthogonal_inv MO) trmxK.
Qed.

Lemma uncayley_is_so n (M : 'M[R]_n.+1) : M \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue M -> uncayley M \is 'so[R]_n.+1.
Proof.
move=> MO MN1; rewrite antiE; apply/eqP.
rewrite {2}/uncayley.
rewrite {1}mulrBl mul1r ortho_N1eigen_comm // -[X in _ - X]mulr1 -mulrBr.
rewrite trmx_mul mulmxE trmxV !linearD /= linearN /= trmx1.
rewrite /uncayley -(mulr1 (M - 1)) -[X in _ * X / _](orthogonal_tr_mul MO).
rewrite mulrA mulrDl mulNr mul1r -(orthogonal_inv MO) divrr ?orthogonal_unit//.
rewrite -mulrA -[X in _ * (X * _)](invrK M) -invrM; last 2 first.
  by rewrite ortho_N1eigen_invertible.
  by rewrite unitrV orthogonal_unit.
rewrite (mulrDl _ _ M^-1) divrr ?orthogonal_unit// mul1r (addrC 1 M^-1).
by rewrite -mulNr opprB.
Qed.

Lemma trmx_uncayley n (M : 'M[R]_n.+1) : M \is 'O[R]_n.+1 ->
  -1 \notin eigenvalue M -> (uncayley M)^T = - uncayley M.
Proof.
by move=> MO N1; apply/esym/eqP; rewrite eqr_oppLR -antiE uncayley_is_so.
Qed.

(* [murray] exercise 5.(a), p.73 *)
Lemma cayley_is_SO3 Q : Q \is 'so[R]_3 -> cayley Q \is 'SO[R]_3.
Proof.
move=> Qso; rewrite rotationE cayley_is_O //= /cayley.
rewrite det_mulmx det_inv det_sub1spin3E// det_add1spin3E //.
by rewrite mulVr // unitfE paddr_eq0 ?sqr_ge0 // oner_eq0.
Qed.

Lemma uncayleyK n M : M \is 'O[R]_n.+1 -> -1 \notin eigenvalue M ->
  \det (1 - uncayley M) != 0 -> cayley (uncayley M) = M.
Proof.
move=> MO MN1 ?; rewrite /cayley.
suff <- : (1 - uncayley M) * M = 1 + uncayley M.
  by rewrite mulrA mulVr ?mul1r// unitmxE unitfE.
rewrite mulrBl ?mul1r; apply/eqP.
rewrite subr_eq -addrA addrC -subr_eq.
suff -> : (M - 1) = (uncayley M) * (M + 1) by rewrite mulrDr mulr1 addrC.
by rewrite /uncayley -mulrA mulVr ?mulr1// ortho_N1eigen_invertible.
Qed.

Lemma uncayleyK3 M : M \is 'O[R]_3 -> -1 \notin eigenvalue M ->
  cayley (uncayley M) = M.
Proof. by move=> ? ?; rewrite uncayleyK // skew_det1BM // uncayley_is_so. Qed.

(* [bottema] p.148 (1.4) *)
Definition cayley00 (a b c : R) := 1 + a ^+ 2 - b ^+ 2 - c ^+ 2.
Definition cayley01 (a b c : R) := (a * b - c) *+ 2.
Definition cayley02 (a b c : R) := (a * c + b) *+ 2.
Definition cayley10 (a b c : R) := (a * b + c) *+ 2.
Definition cayley11 (a b c : R) := 1 - a ^+ 2 + b ^+ 2 - c ^+ 2.
Definition cayley12 (a b c : R) := (b * c - a) *+ 2.
Definition cayley20 (a b c : R) := (a * c - b) *+ 2.
Definition cayley21 (a b c : R) := (b * c + a) *+ 2.
Definition cayley22 (a b c : R) := 1 - a ^+ 2 - b ^+ 2 + c ^+ 2.

Lemma sqr_norm_row3 (a b c : R) :
  (norm (row3 a b c)) ^+ 2 = a ^+ 2 + b ^+ 2 + c ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum3E !mxE/= -!expr2. Qed.

(* result of the Cayley transform expressed with Rodrigues' parameters *)
Lemma cayleyE (a b c : R) : let r := euclidean.norm (row3 a b c) in
  cayley \S((row3 a b c)) = (1 + r ^+ 2)^-1 *: (col_mx3
  (row3 (cayley00 a b c) (cayley01 a b c) (cayley02 a b c))
  (row3 (cayley10 a b c) (cayley11 a b c) (cayley12 a b c))
  (row3 (cayley20 a b c) (cayley21 a b c) (cayley22 a b c)))^T.
Proof.
move=> r.
have r12 : 1 + r ^+ 2 != 0 by rewrite paddr_eq0//= ?sqr_ge0// ?ler01// oner_eq0.
rewrite trmx_col_mx3_row3.
rewrite /cayley inv1BME; apply/matrix3P/and9P; split.
- rewrite -/r.
  rewrite !(mxE,sum3E); Simp.r.
  rewrite !spinij; Simp.r => /=.
  rewrite !mxE /=.
  rewrite /cayley00.
  apply/eqP/(mulfI r12).
  rewrite !mulrDr !mulr1 !mulrA !divff//; Simp.r => /=.
  rewrite mulrDr !mulrA !divff//; Simp.r => /=.
  rewrite mulrDr mulrN !mulrA !divff//; Simp.r => /=.
  rewrite sqr_norm_row3.
  rewrite !expr2.
  by field.
- rewrite -/r.
  rewrite !(mxE,sum3E); Simp.r.
  rewrite !spinij; Simp.r => /=.
  rewrite !mxE/=.
  rewrite /cayley10.
  apply/eqP/(mulfI r12).
  rewrite !mulrDr !mulrA !divff//.
  rewrite !mulrDr mulr1 !mulrA !divff//; Simp.r => /=.
  rewrite mulrDr mulrN !mulrA !divff//; Simp.r => /=.
  rewrite sqr_norm_row3 !expr2.
  by field.
- rewrite -/r.
  rewrite !(mxE,sum3E); Simp.r.
  rewrite !spinij; Simp.r => /=.
  rewrite !mxE/=.
  rewrite /cayley20.
  apply/eqP/(mulfI r12).
  rewrite !mulrDr !mulrA !divff//.
  rewrite 2!mulrN !mulrA !mulrDr mulr1.
  rewrite !mulrN !mulrA !divff//; Simp.r => /=.
  rewrite -mulrA divff//; Simp.r => /=.
  rewrite sqr_norm_row3 !expr2.
  by field.
(* TODO: complete *)
Abort.

End cayley_transform.
