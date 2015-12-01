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

(* courtesy of GG *)
Lemma mxdirect_delta (F : fieldType) (T : finType) (n : nat) (P : pred T) f :
  {in P & , injective f} ->
  mxdirect (\sum_(i | P i) <<delta_mx 0 (f i) : 'rV[F]_n>>)%MS.
Proof.
pose fP := image f P => Uf; have UfP: uniq fP by apply/dinjectiveP.
suffices /mxdirectP: mxdirect (\sum_i <<delta_mx 0 i : 'rV[F]_n>>).
  rewrite /= !(bigID [mem fP] predT) -!big_uniq //= !big_map !big_filter.
  by move/mxdirectP; rewrite mxdirect_addsE => /andP[].
apply/mxdirectP=> /=; transitivity (mxrank (1%:M : 'M[F]_n)).
  apply/eqmx_rank; rewrite submx1 mx1_sum_delta summx_sub_sums // => i _.
  by rewrite -(mul_delta_mx (0 : 'I_1)) genmxE submxMl.
rewrite mxrank1 -[LHS]card_ord -sum1_card.
by apply/eq_bigr=> i _; rewrite /= mxrank_gen mxrank_delta.
Qed.


End extra.
