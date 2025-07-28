From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun.

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

Lemma differentiable_scalar_mx {R : realType} n (r : R) :
  differentiable (@scalar_mx _ n.+1) r.
Proof.
apply/derivable1_diffP/cvg_ex => /=.
exists 1; apply/cvgrPdist_le => /= e e0.
near=> t.
rewrite scaler1 -raddfB/= addrK (scale_scalar_mx _ t^-1) mulVf.
  by rewrite subrr normr0 ltW.
by near: t; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.
