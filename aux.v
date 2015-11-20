Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

Local Open Scope ring_scope.

Section extra.

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat)
 (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (M : zmodType) (m1 m2 n : nat)
 (A1 : 'M[M]_(m1, n)) (A2 : 'M_(m2, n)):
 (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
by rewrite -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx0 tr_col_mx row_mx_eq0.
Qed.

Lemma mxdirect_delta (F : fieldType) (T : finType)
  (n : nat) (P : pred T) (f : T -> 'I_n) :
  {in P & , injective f} ->
  mxdirect (\sum_(i | P i) <<delta_mx 0 (f i) : 'rV[F]_n>>)%MS.
Proof.
move=> f_inj; apply/mxdirectP => /=.
transitivity (\rank (\sum_(j | P j) (delta_mx (f j) (f j) : 'M[F]_n))).
  apply: eqmx_rank; apply/genmxP; rewrite !genmx_sums.
  apply/eq_bigr => i Pi; rewrite genmx_id.
  apply/genmxP/andP; split; apply/submxP.
    by exists (delta_mx 0 (f i)); rewrite mul_delta_mx.
  by exists (delta_mx (f i) 0); rewrite mul_delta_mx.
rewrite (mxdirectP _) /=.
  by apply: eq_bigr => i _; rewrite /= mxrank_gen !mxrank_delta.
apply/mxdirect_sumsP => /= s Ps.
apply/eqP; rewrite -submx0; apply/rV_subP => u.
rewrite sub_capmx => /andP [/submxP [x ->]].
move=> /(submxMr (delta_mx (f s) (f s))).
rewrite sumsmxMr_gen big1; first by rewrite -mulmxA mul_delta_mx.
move=> i /andP [Pi neq_is]; rewrite mul_delta_mx_0 ?genmx0 //.
by apply: contraNneq neq_is => /f_inj ->.
Qed.

End extra.
