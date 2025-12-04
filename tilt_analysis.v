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
 (* is already in realfun.v*)
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
  differentiable (@scalar_mx _ n) r.
Proof.
apply/derivable1_diffP/cvg_ex => /=.
exists 1; apply/cvgrPdist_le => /= e e0.
near=> t.
Search (_%:A). 
rewrite scaler1 -raddfB/= addrK (scale_scalar_mx _ t^-1) mulVf.
  by rewrite subrr normr0 ltW.
by near: t; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

Lemma derivable_enorm_squared  {K : rcfType} n (f : K -> 'rV[K]_n) (x0 : K) :
  derivable f x0 1 ->
  derivable (fun x => `|f x|_e ^+ 2) x0 1.
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

Lemma derive_enorm_squared {K : realType} n (u : K -> 'rV[K]_n) (t : K) :
  derivable u t 1 ->
  'D_1 (fun x => `|u x|_e ^+ 2) t =
  2 * ('D_1 u t *m (u t)^T)``_0.
Proof.
move=> ut1.
under eq_fun do rewrite -dotmulvv.
rewrite dotmulP mxE /= mulr1n derive_dotmul// dotmulC.
by field.
Qed.

Lemma derivable_sqrt {K: realType} (u : K) : u > 0 -> derivable Num.sqrt (u) 1.
Proof.
move => gt0.
apply: ex_derive.
by apply: (is_derive1_sqrt gt0).
Qed.
(* should go to tilt_robot*)
Lemma differentiable_enorm {K : realType} m n (f : 'rV[K]_m -> 'rV_n)
  (g : K -> 'rV[K]_m) t :
  differentiable f (g t) -> f (g t) != 0 ->
  differentiable (fun x => `|f x|_e) (g t) .
Proof.
move=> fgt fgt0; rewrite /enorm -fctE.
apply: differentiable_comp.
  exact: differentiable_dotmul.
apply/derivable1_diffP/derivable_sqrt.
by rewrite dotmulvv expr2 mulr_gt0 //= !enorm_gt0.
Qed.

(*Lemma differentiable_norm_squared {R : rcfType} m n
    (f : 'rV[R]_m -> 'rV[R]_n) (v : 'rV[R]_m)  :
  differentiable f v ->
  differentiable (fun x => `|f x|_e ^+ 2) v.
Proof.
move=> dif1.
under eq_fun do rewrite -dotmulvv.
exact: differentiable_dotmul.
Qed.*)
(* this one too *)
(*Lemma derivable_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  (forall x, derivable f x v) -> derivable (fun x => rsubmx (f x)) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= r Hr]:= df1 t.
apply/cvg_ex => /=; exists (r``_(rshift n1 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hr => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, rshift n1 j)).
by rewrite !mxE.
Qed.*)

(*Lemma derive_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  (forall x, derivable f x v) ->
  'D_v (fun x => rsubmx (f x)) t = @rsubmx _ _ n1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE//=; last exact: derivable_rsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.*)
(*DONE*)
Lemma differentiable_rsubmx0 {R : realFieldType} {V : normedModType R} {n1 n2} t :
  differentiable (@rsubmx R 1 n1 n2) t.
Proof.
have lin_rsubmx : linear (@rsubmx R 1 n1 n2).
  move=> a b c.
  by rewrite linearD//= linearZ.
pose build_lin_rsubmx := GRing.isLinear.Build _ _ _ _ _ lin_rsubmx.
pose Rsubmx : {linear 'rV[R^o]_(n1 + n2) -> 'rV[R^o]_n2} := HB.pack (@rsubmx R _ _ _) build_lin_rsubmx.
apply: (@linear_differentiable _ _ _ Rsubmx).
move=> /= u A /=.
move/nbhs_ballP=> [e /= e0 eA].
apply/nbhs_ballP; exists e => //= v [? uv].
apply: eA; split => //.
(* TODO: lemma *)
move: uv; rewrite /ball/= /mx_ball/ball /= => uv i j.
apply: (le_lt_trans _ (uv i (rshift n1 j))).
by rewrite !mxE.
Qed.
(*DONE*)
Lemma differentiable_rsubmx {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => rsubmx (f x)) t.
Proof.
move=> /= => df1.
apply: differentiable_comp => //.
exact: differentiable_rsubmx0.
Qed.
(*TODO*)
Lemma derivable_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  (forall x, derivable f x v) -> derivable (fun x => lsubmx (f x)) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= l Hl]:= df1 t.
apply/cvg_ex => /=; exists (l``_(lshift n2 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, lshift n2 j)).
by rewrite !mxE.
Qed.

Lemma derive_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  (forall x, derivable f x v) ->
  'D_v (fun x => lsubmx (f x)) t = @lsubmx _ _ n1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE//=; last exact: derivable_lsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.
(*DONE*)
Lemma differentiable_lsubmx0 {R : realFieldType} {V : normedModType R} {n1 n2} t :
  differentiable (@lsubmx R 1 n1 n2) t.
Proof.
have lin_lsubmx : linear (@lsubmx R 1 n1 n2).
  move=> a b c.
  by rewrite linearD//= linearZ.
pose build_lin_lsubmx := GRing.isLinear.Build _ _ _ _ _ lin_lsubmx.
pose Lsubmx : {linear 'rV[R^o]_(n1 + n2) -> 'rV[R^o]_n1} :=
  HB.pack (@lsubmx R _ _ _) build_lin_lsubmx.
apply: (@linear_differentiable _ _ _ Lsubmx).
move=> /= u A /=.
move/nbhs_ballP=> [e /= e0 eA].
apply/nbhs_ballP; exists e => //= v [? uv].
apply: eA; split => //.
(* TODO: lemma *)
move: uv; rewrite /ball/= /mx_ball/ball /= => uv i j.
apply: (le_lt_trans _ (uv i (lshift n2 j))).
by rewrite !mxE.
Qed.

(*Global Instance is_diff_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f df : V -> 'rV[R]_(n1 + n2)) t :
  is_diff t f df ->
  is_diff t (fun x => lsubmx (f x)) (fun x => lsubmx (df x)).
Proof.
case=> diff_f dfE.
apply: DiffDef.
  by apply: differentiable_comp => //; exact: differentiable_lsubmx0.
apply/funext => v.
rewrite -dfE.
rewrite -[LHS]deriveE; last first.
  by apply: differentiable_comp => //; exact: differentiable_lsubmx0.
rewrite -[in RHS]deriveE; last first.
  by [].
rewrite derive_lsubmx//.
Abort.*)
(*DONE*)
Lemma differentiable_lsubmx {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => lsubmx (f x)) t.
Proof.
move=> /= => df1.
apply: differentiable_comp => //.
exact: differentiable_lsubmx0.
Qed.

(*Lemma derivable_row_mx {R : realFieldType} {n1 n2 : nat}
    (f : R -> 'rV[R]_n1) (g : R -> 'rV[R]_n2) t v :
  (forall x, derivable f x v) -> (forall x, derivable g x v) ->
  derivable (fun x : R => row_mx (f x) (g x)) t v.
Proof.
move=> /= fv gv; apply/derivable_mxP => i j.
rewrite (ord1 i)/=.
have /cvg_ex[/= l Hl]:= fv t.
have /cvg_ex[/= k Hk]:= gv t.
apply/cvg_ex => /=; exists (row_mx l k)``_j.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0) Hl.
move/cvgrPdist_le : Hk => /(_ _ e0) Hk.
move: Hl Hk; apply: filterS2 => x Hl Hk.
rewrite !mxE.
case: fintype.splitP => j1 jj1.
  apply: le_trans Hl.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
  apply: le_trans; last first.
    exact: (le_bigmax _ _ (ord0, j1)).
  by rewrite !mxE/=.
apply: le_trans Hk.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, j1)).
by rewrite !mxE/=.
Qed.*)

(* used in derive_along_derive*)
(*TODO*)
Lemma derivable_scalar_mx {R : realFieldType} n (f : 'rV[R]_n -> R)
    (a : 'rV[R]_n) v :
  derivable f a v ->
  derivable (@scalar_mx _ 1 \o f) a v.
Proof.
move=> /cvg_ex[/= l fav].
apply/cvg_ex => /=.
exists (\col_(i < 1) l).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : fav => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leLHS]/Num.Def.normr/= !mx_normrE/=.
apply: bigmax_le => //= -[i j] _.
rewrite !mxE/=.
by rewrite !ord1 eqxx !mulr1n.
Qed.

(* not used? *)
(*Lemma derive_row_mx {R : realFieldType} {n1 n2 : nat}
     (f : R -> 'rV[R]_n1) (g : R -> 'rV[R]_n2) t v :
  (forall x : R, derivable f x v) ->
  (forall x : R, derivable g x v) ->
  'D_v (fun x => row_mx (f x) (g x)) t = row_mx ('D_v f t) ('D_v g t).
Proof.
move=> fv gv.
apply/matrixP => i j.
rewrite derive_mx ?mxE//=; last first.
  by apply: derivable_row_mx; [exact: fv|exact: gv].
do 2 rewrite derive_mx ?mxE//=.
case: fintype.split_ordP => /= j1 jj1; rewrite !mxE; congr ('D_v _ t).
  apply/funext => x; rewrite !mxE.
  case: fintype.split_ordP => k jE.
    congr (f x i _).
    move: jE.
    by rewrite jj1 => /(congr1 val) => /= /val_inj.
  move: jE.
  rewrite jj1 => /(congr1 val)/=.
  have /[swap] -> := ltn_ord j1.
  by rewrite ltnNge/= leq_addr.
apply/funext => x; rewrite !mxE.
case: fintype.split_ordP => k jE.
  move: jE.
  rewrite jj1 => /(congr1 val)/=.
  have /[swap] <- := ltn_ord k.
  by rewrite ltnNge/= leq_addr.
congr (g x i _).
move: jE.
rewrite jj1 => /(congr1 val) => /= /eqP.
by rewrite eqn_add2l => /eqP /val_inj.
Qed.*)
