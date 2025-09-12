From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun landau.
From HB Require Import structures.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

Global Instance is_derive1_sqrt {K : realType} (x : K) : 0 < x ->
  is_derive x 1 Num.sqrt (2 * Num.sqrt x)^-1.
Proof.
move=> x_gt0.
have sqrtK : {in Num.pos, cancel (@Num.sqrt K) (fun x => x ^+ 2)}.
  by move=> a a0; rewrite sqr_sqrtr// ltW.
rewrite -[x]sqrtK//.
apply: (@is_derive_inverse K (fun x => x ^+ 2)).
- near=> z.
  rewrite sqrtr_sqr gtr0_norm//.
  have [xz|zx|->] := ltgtP z (Num.sqrt x); last first.
  + by rewrite sqrtr_gt0.
  + by rewrite (lt_trans _ zx)// sqrtr_gt0.
  + move: xz.
    near: z.
    exists (Num.sqrt x / 2).
      rewrite /=.
      rewrite mulr_gt0 //.
      by rewrite sqrtr_gt0 x_gt0.
      rewrite invr_gt0.
      by [].
    move=> r/=.
    move=> /[swap] rx.
    rewrite gtr0_norm ?subr_gt0//.
    rewrite ltrBlDl.
    rewrite -ltrBlDr.
    apply: le_lt_trans.
    rewrite subr_ge0.
    rewrite ger_pMr.
    rewrite invf_le1.
    by rewrite ler1n.
    by [].
    by rewrite sqrtr_gt0.
- near=> z.
  exact: exprn_continuous.
- rewrite !sqrtK//; split.
    exact: exprn_derivable (* TODO: renaming, see https://github.com/math-comp/analysis/issues/1677 *).
  by rewrite exp_derive (* TODO: renaming -> issue *) expr1 scaler1.
- by rewrite mulf_neq0 ?pnatr_eq0// gt_eqF// sqrtr_gt0 exprn_gt0// sqrtr_gt0.
Unshelve. all: by end_near. Qed.

Lemma derive_sqrt {K : realType} (r : K) : 0 < r ->
   (Num.sqrt^`())%classic r = (2 * Num.sqrt r)^-1 :> K.
Proof.
move=> r0.
rewrite derive1E.
apply: derive_val.
exact: is_derive1_sqrt.
Qed.

Lemma differentiable_scalar_mx {R : realFieldType} n (r : R) :
  differentiable (@scalar_mx _ n.+1) r.
Proof.
apply/derivable1_diffP/cvg_ex => /=.
exists 1; apply/cvgrPdist_le => /= e e0.
near=> t.
rewrite scaler1 -raddfB/= addrK (scale_scalar_mx _ t^-1) mulVf.
  by rewrite subrr normr0 ltW.
by near: t; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

Lemma derive_norm {K : realType} n (u : K^o -> 'rV[K^o]_n.+1) (t : K) :
  u t != 0 ->
  derivable u t 1 ->
  (1 \*o (@GRing.exp K ^~ 2) \o @norm K n.+1 \o u)^`()%classic t =
  2 * (fun t => ('D_1 u t *m  (u t)^T)``_0) t :> K.
Proof.
move=> u0 ut1.
rewrite [LHS]derive1E deriveMl/=; last first.
  apply/derivable1_diffP.
  apply/(@differentiable_comp _ _ _ _ (fun x => norm (u x)) (fun x => x ^+ 2)) => //=.
  rewrite /norm.
  apply/(@differentiable_comp _ _ _ _ _ (fun x => Num.sqrt x)) => //=.
    apply/derivable1_diffP.
    exact/derivable_dotmul.
  apply/derivable1_diffP.
  apply/ex_derive.
  apply: is_derive1_sqrt.
  rewrite dotmulvv.
  by rewrite exprn_gt0// norm_gt0.
rewrite -derive1E mul1r.
under eq_fun do rewrite -dotmulvv.
rewrite dotmulP mxE /= mulr1n.
rewrite derive1E.
rewrite derive_dotmul ; last 2 first.
  exact: ut1.
  exact: ut1.
rewrite dotmulC.
by field.
Qed.

Lemma derivable_norm_squared  {K : rcfType} n (f : K -> 'rV[K]_n.+1) (x0 : K) :
  derivable f x0 1 ->
  derivable (fun x => norm (f x) ^+ 2) x0 1.
Proof.
move => dif1.
apply/diff_derivable.
rewrite /=.
under eq_fun do rewrite -dotmulvv dotmulE.
have -> : (fun x : K => \sum_k (f x)``_k * (f x)``_k) = 
        \sum_k (fun x => (f x)``_k * (f x)``_k ).
  apply/funext => x => //=.
  by rewrite fct_sumE.
apply/differentiable_sum => k => //=.
apply/differentiableM => //=.
  apply/derivable1_diffP.
  by apply/derivable_coord => //.
apply/derivable1_diffP.
by apply/derivable_coord => //.
Qed.

Lemma derive_norm_squared {K : realType} n (u : K^o -> 'rV[K^o]_n.+1) (t : K) :
  derivable u t 1 ->
  (1 \*o (@GRing.exp K ^~ 2) \o @norm K n.+1 \o u)^`()%classic t =
  2 * (fun t => ('D_1 u t *m  (u t)^T)``_0) t :> K.
Proof.
move=> ut1.
rewrite [LHS]derive1E deriveMl/=; last first.
  by apply/derivable_norm_squared => //.
rewrite -derive1E mul1r.
under eq_fun do rewrite -dotmulvv.
rewrite dotmulP mxE /= mulr1n.
rewrite derive1E.
rewrite derive_dotmul ; last 2 first.
  exact: ut1.
  exact: ut1.
rewrite dotmulC.
by field.
Qed.

Lemma derivable_sqrt {K: realType} (u : K) : u > 0 -> derivable Num.sqrt (u) 1.
Proof.
move => gt0.
apply: ex_derive.
by apply: (is_derive1_sqrt gt0).
Qed.

Lemma differentiable_norm {K : realType} n m (f : 'rV[K]_n.+1 -> 'rV_m.+1)
  (x : K -> 'rV[K]_n.+1) (t : K) :
  differentiable f (x t) -> f (x t) != 0 ->
  differentiable (fun x0 => norm (f x0)) (x t) .
Proof.
move => fx0 dif1.
rewrite /norm -fctE.
apply: differentiable_comp; last first.
  apply/derivable1_diffP.
  apply/derivable_sqrt.
  by rewrite dotmulvv expr2 mulr_gt0 //= !norm_gt0 //.
by apply: differentiable_dotmul => //.
Qed.

Lemma differentiable_norm_squared {R : rcfType} m n (V := 'rV[R]_m.+1)
    (u v : V -> 'rV[R]_n.+1) (t : V) :
  differentiable u t ->
  differentiable (fun x => norm (u x)^+2 ) t .
Proof.
move => dif1.
under eq_fun do rewrite -dotmulvv.
rewrite /=.
by apply: differentiable_dotmul => //.
Qed.


