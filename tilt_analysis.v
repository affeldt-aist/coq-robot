From mathcomp Require Import all_boot all_order all_algebra ring.
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

(* Todo: Maybe useful generally? (PR) *)
Lemma norm_rowmx {K : rcfType} {m n1 n2 : nat}
    (A1 : 'M[K]_(m.+1, n1.+1)) (A2 : 'M[K]_(m.+1, n2.+1)) :
  `|row_mx A1 A2| = Num.max `|A1| `|A2|.
Proof.
rewrite /Num.norm/= !mx_normrE.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: bigmax_le => /=.
    rewrite le_max;apply /orP;left.
    exact/le_trans/(le_bigmax _ _ (ord0,ord0)).
  move=> [i j] _ /=.
  rewrite le_max; apply/orP.
  rewrite mxE.
  case: (splitP  j) => j1 h1.
    by left; exact: (le_bigmax _ _ (i, j1)).
  by right;exact: (le_bigmax _ _ (i, j1)).
rewrite ge_max; apply/andP; split.
  apply: bigmax_le => /=.
    apply: le_trans; last first.
      exact: (le_bigmax _ _ (ord0, ord0)).
    exact: normr_ge0.
   move=> [i j] _.
   rewrite -(row_mxEl _ A2).
   exact: (le_bigmax _ _ (i, lshift n2.+1 j)).
apply: bigmax_le => /=.
  apply: le_trans; last first.
    exact: (le_bigmax _ _ (ord0, ord0)).
  exact: normr_ge0.
move=> [i j] _.
rewrite -(row_mxEr A1).
exact: (le_bigmax _ _ (i, rshift n1.+1 j)).
Qed.

(*Todo: This also seems useful in general (PR) *)
Lemma mx_norm_mul {K : rcfType} {m n p} (A : 'M[K]_(m.+1, n.+1)) (B : 'M_(n.+1, p.+1)) :
 `|A *m B| <= n.+1%:R * `| A| * `|B|.
Proof.
rewrite /Num.norm/= !mx_normrE.
apply: bigmax_le.
  rewrite -mulrA mulr_ge0//.
  by apply mulr_ge0; apply/le_trans/(le_bigmax _ _ (ord0, ord0)).
move=> /= [i j] _/=.
rewrite mxE.
rewrite (le_trans (ler_norm_sum _ _ _))//=.
have le_inside k : `|A i k * B k j| <= `|A| * `|B|.
  rewrite normrM /Num.norm/= !mx_normrE/= ler_pM//=.
  - exact: normr_ge0.
  - exact: normr_ge0.
  - exact: (le_bigmax _ _ (i, k)).
  - exact: (le_bigmax _ _ (k, j)).
rewrite -mulrA.
rewrite (@le_trans _ _ (\sum_(k < n.+1) `|A| * `|B|))//.
  by apply: ler_sum => k _; apply le_inside.
rewrite mulr_natl.
rewrite big_const_ord.
rewrite iter_addr_0.
by rewrite /Num.norm/= !mx_normrE.
Qed.

Lemma differentiable_scalar_mx {R : realType} n (r : R) :
  differentiable (@scalar_mx _ n) r.
Proof.
apply/derivable1_diffP/cvg_ex => /=.
exists 1; apply/cvgrPdist_le => /= e e0.
near=> t.
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

Lemma derivable_sqrt {K: realType} (u : K) : u > 0 -> derivable Num.sqrt u 1.
Proof.
move=> u0.
apply: ex_derive.
exact: (is_derive1_sqrt u0).
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

Lemma differentiable_rsubmx_comp {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => rsubmx (f x)) t.
Proof.
move=> /= df1.
apply: differentiable_comp => //.
exact: differentiable_rsubmx.
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

Lemma differentiable_lsubmx_comp {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => lsubmx (f x)) t.
Proof.
move=> /= df1.
apply: differentiable_comp => //.
exact: differentiable_lsubmx.
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

Local Open Scope classical_set_scope.

Lemma within_continuous_comp {R : realType} {K : numDomainType}
  {U : pseudoMetricNormedZmodType K} a y (g : U -> R) (f : R -> U) :
  a <= y ->
  {in f @` `[a, y], continuous g} ->
  {within `[a, y], continuous (fun x => f x)} ->
  {within `[a, y], continuous fun x => (g \o f) x}.
Proof.
rewrite le_eqVlt => /predU1P[<- _ _|ay cg].
  by rewrite set_itv1; exact: continuous_subspace1.
move/(continuous_within_itvP f ay) => -[cf fa fy].
apply/continuous_within_itvP => //; split => //.
- move=> z zay; apply: continuous_comp => //.
    exact: cf.
  apply/cg/image_f.
  by rewrite inE/=; apply: subset_itv_oo_cc zay.
- apply/(cvg_comp f g fa)/cg/image_f.
  by rewrite inE/= in_itv/= lexx/= ltW.
- apply/(cvg_comp f g fy)/cg/image_f.
  by rewrite inE/= in_itv/= lexx/= ltW.
Qed.

Local Notation Left := (@lsubmx _ 1 _ _).
Local Notation Right := (@rsubmx _ 1 _ _).

Lemma left_norm_le {K : rcfType} n1 n2 (x : 'rV[K]_(n1.+1 + n2.+1)) :
  `|Left x| <= `|x|.
Proof.
rewrite /Num.norm/= !mx_normrE; apply: bigmax_le.
  exact/le_trans/(le_bigmax _ _ (ord0, ord0)).
move=> /= [i j] _ /=.
rewrite mxE.
exact: (le_bigmax _ _ (i, lshift n2.+1 j)).
Qed.

Lemma right_norm_le {K : rcfType} n1 n2 (x : 'rV[K]_(n1.+1 + n2.+1)) :
  `|Right x| <= `|x|.
Proof.
rewrite /Num.norm/= !mx_normrE; apply: bigmax_le.
  exact/le_trans/(le_bigmax _ _ (ord0,ord0)).
move=> /= [i j] _ /=.
rewrite mxE.
exact: (le_bigmax _ _ (i, rshift n1.+1 j)).
Qed.

Lemma mx_norm1 {K : rcfType} {n} : `|1 : 'M[K]_n.+1| = 1.
Proof.
rewrite /Num.norm/= !mx_normrE.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: bigmax_le => //= i _.
  rewrite mxE/=.
  by case: eqP => /= _; rewrite ?(normr1, normr0).
- rewrite -normr1.
  have -> : (1 : K) = ((1 : 'M[K]_n.+1) ord0 ord0) by rewrite mxE.
  exact: (le_bigmax _ _ (ord0, ord0)).
Qed.

Lemma mx_norm_delta_mx {K : rcfType} n (i : 'I_n.+1) : `| 'e_i : 'rV[K]__ | <= 1.
Proof.
rewrite /Num.norm /= mx_normrE; apply: bigmax_le => //= -[/= a b] _.
rewrite mxE /=.
case: eqP => /= _; last by rewrite normr0.
case: eqP => /= _; last by rewrite normr0.
by rewrite normr1.
Qed.

Lemma enorm_mxnorm {K : rcfType} {n} (x : 'rV[K]_n.+1) :
  `|x|_e ^+ 2 <= n.+1%:R * `|x| ^ 2.
Proof.
rewrite sqr_enorm /=.
apply : (@le_trans _ _ (\sum_(i0 < n.+1) `|x| ^+ 2)).
  apply: ler_sum => k _.
  rewrite -sqr_normr.
  suff h : `|x ord0 k| <= `|x| by exact: ler_pM.
  rewrite {2}/Num.norm/= !mx_normrE /=.
  exact: (le_bigmax _ _ (ord0, k)).
by rewrite big_const_ord mulr_natl iter_addr_0.
Qed.

Lemma mx_norm_sq_le {K : rcfType} {n} (A : 'M[K]_n.+1) :
  `|A ^+ 2| <= n.+1%:R * `|A| ^+ 2.
Proof. by rewrite !expr2 mulrA; exact: mx_norm_mul. Qed.
