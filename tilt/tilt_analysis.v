From HB Require Import structures.
From mathcomp Require Import boot order algebra ring_tactic
  interval_inference.
From mathcomp Require Import boolp classical_sets functions filter reals
  topology ereal prodnormedzmodule normedtype sequences derive realfun
  landau measure lebesgue_integral.
Require Import ssr_ext derive_matrix.

(**md**************************************************************************)
(* # Additions to the MathComp-Analysis library                               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(* TODO: PR to MCA in progress *)
Lemma within_continuous_continuous_new {R : realFieldType} {K : numDomainType}
    {U : pseudoMetricNormedZmodType K} a b (f : R -> U) x : (a <= b)%R ->
  {within `[a, b], continuous f} -> x \in `]a, b[%R -> {for x, continuous f}.
Proof.
rewrite le_eqVlt => /predU1P[<- _|ab].
  by rewrite in_itv/= => /andP[] /lt_trans /[apply]; rewrite ltxx.
by move=> /continuous_within_itvP-/(_ ab)[+ _ _]; exact.
Qed.

(* TODO: PR to MCA *)
Lemma closure_neitv_oy {R : realType} (a : R) :
  closure `]a, +oo[%classic = `[a, +oo[%classic.
Proof.
set x := a + 1.
have -> : (`]a, +oo[ = `]a, x[ `|` `[x, +oo[)%classic.
  by apply: itv_bndbnd_setU => //; rewrite bnd_simp ltrDl.
rewrite closureU -((closure_id _).1 (@rray_closed _ _ _)).
rewrite closure_itvoo; first by rewrite ltrDl.
rewrite -(setUitv1 true) ?bnd_simp; first by rewrite lerDl.
rewrite -setUA [[set x] `|` _]setUidr.
  by rewrite -set_itv1; apply: subset_itvl.
apply/esym.
by apply: itv_bndbnd_setU => //; rewrite bnd_simp lerDl.
Qed.

(* TODO: PR to MCA *)
Section continuous_patch.
Context {R : realType} {n : nat} {U : normedModType R}.
Variables (a b c : R) (f : R -> U) (g : R -> U).
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous f}.
Hypothesis cont2 : {within `[b, c], continuous g}.
Hypothesis matchb : f b = g b.

Lemma within_continuous_patch : {within `[a, c], continuous (patch g `[a, b] f)}.
Proof.
have -> : `[a, c] = `[a, b] `|` `[b, c].
  rewrite (@itv_bndbnd_setU _ _ _ (BRight b)) // ?bnd_simp//=; [exact: ltW..|].
  apply/seteqP; split => [x []|x []].
  by left.
  by right; exact: subset_itv_oc_cc b0.
  by left.
  rewrite -(setU1itv false) ?bnd_simp//; first exact: ltW.
  case; last by right.
  move=> ->; left => /=.
  by rewrite bound_itvE ltW.
apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b c)).
  apply: subspace_eq_continuous cont1.
  by move=> /=r rab; rewrite /from_subspace /patch rab.
have eq2 : {in `[b, c], g =1 patch g `[a, b] f }.
  move=> r rab.
  rewrite /patch; case: ifPn => [xab | xabnot] => //.
  suff -> : r = b by rewrite matchb.
  apply: le_anti.
  move: rab xab.
  by rewrite !inE/=!in_itv/= => /andP [-> _] /andP [_ ->].
exact: (subspace_eq_continuous eq2).
Qed.

End continuous_patch.

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

Lemma differentiable_scalar_mx {R : numFieldType} n (r : R) :
  differentiable (@scalar_mx _ n) r.
Proof.
apply/derivable1_diffP/cvg_ex => /=.
exists 1; apply/cvgrPdist_le => /= e e0.
near=> t.
rewrite scaler1 -raddfB/= addrK (scale_scalar_mx _ t^-1) mulVf.
  by near: t; exact: nbhs_dnbhs_neq.
by rewrite subrr normr0 ltW.
Unshelve. all: by end_near. Qed.

Lemma differentiable_rsubmx_comp {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => rsubmx (f x)) t.
Proof.
move=> /= df1.
apply: differentiable_comp => //.
exact: differentiable_rsubmx.
Qed.

Lemma differentiable_lsubmx_comp {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => lsubmx (f x)) t.
Proof.
move=> /= df1.
apply: differentiable_comp => //.
exact: differentiable_lsubmx.
Qed.

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

Local Open Scope classical_set_scope.

(* TODO: rename, generalize to the subset relation *)
Lemma in_switch {R : numDomainType} (I : interval R) P :
  {in [set` I], forall x, P x} <-> {in I, forall x, P x}.
Proof.
split => [h x xI| h x xI]; apply h.
  by rewrite inE.
by rewrite inE in xI.
Qed.

Lemma lsubmx_norm_le {K : rcfType} n1 n2 (x : 'rV[K]_(n1.+1 + n2.+1)) :
  `|lsubmx x| <= `|x|.
Proof.
rewrite /Num.norm/= !mx_normrE; apply: bigmax_le.
  exact/le_trans/(le_bigmax _ _ (ord0, ord0)).
move=> /= [i j] _ /=.
rewrite mxE.
exact: (le_bigmax _ _ (i, lshift n2.+1 j)).
Qed.

Lemma rsubmx_norm_le {K : rcfType} n1 n2 (x : 'rV[K]_(n1.+1 + n2.+1)) :
  `|rsubmx x| <= `|x|.
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

Lemma mx_norm_sq_le {K : rcfType} {n} (A : 'M[K]_n.+1) :
  `|A ^+ 2| <= n.+1%:R * `|A| ^+ 2.
Proof. by rewrite !expr2 mulrA; exact: mx_norm_mul. Qed.

Local Open Scope classical_set_scope.

(* TODO: move *)
Lemma open_disjoint_separated (X : topologicalType) (A B : set X) :
  open A -> open B -> A `&` B = set0 -> separated A B.
Proof.
move=>Ao Bo ABdisj.
split.
  apply /disjoints_subset.
  rewrite (closure_id (~` B)).1; first exact: open_closedC.
  exact/closureS/disjoints_subset.
rewrite setIC; apply/disjoints_subset.
rewrite (closure_id (~` A)).1; first exact: open_closedC.
apply/closureS/disjoints_subset.
by rewrite setIC.
Qed.

(* TODO: move *)
Lemma separated_closedUP {T : topologicalType} (A B : set T) : separated A B ->
  closed (A `|` B) <-> closed A /\ closed B.
Proof.
move => ABsep.
split => [/closure_id h | [h1 h2]]; last  by apply closedU.
rewrite closureU in h.
split;apply /closure_id/seteqP;split => [|x cx]; try by apply subset_closure.
have /orP[] : (x \in A) || (x \in B).
  by rewrite -in_setU h inE/=;left.
by rewrite inE.
rewrite inE => xB.
have [/seteqP[+ _] _] := ABsep.
case /(_ x).
by split.
have /orP[] : (x \in A) || (x \in B).
  by rewrite -in_setU h inE/=;right.
rewrite inE => xB.
have [_ /seteqP[+ _]] := ABsep.
case /(_ x).
by split.
by rewrite inE.
Qed.

Lemma cst_oo_cc {R : realType} (f : R -> R) y (a b : R) :
  y \in `[a, b]%R ->
  {within `[a, b], continuous f} ->
  {in `]a, b[%R, f =1 cst (f y)} ->
  {in `[a, b]%R, f =1 cst (f y)}.
Proof.
have [ab|ba] := ltP a b; last first.
  move=> yab _ H x.
  rewrite in_itv/= => /andP[ax xb].
  have /eqP ? : a == x by rewrite eq_le ax (le_trans xb _).
  subst x.
  move: yab; rewrite in_itv/= => /andP[ay yb].
  have /eqP ? : a == y by rewrite eq_le ay (le_trans yb _).
  by subst.
move=> yab cf H x.
rewrite in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<-{x} _|].
  move: yab; rewrite in_itv/= => /andP[].
  rewrite le_eqVlt => /predU1P[->//|ay yb].
  move/continuous_within_itvP : cf => /(_ ab)[_ fafa _].
  move/cvgrPdist_le in fafa.
  rewrite /= in fafa.
  apply/eqP.
  rewrite -subr_eq0.
  rewrite -normr_le0.
  apply/ler_addgt0Pr => /= e e0.
  rewrite add0r.
  have := fafa _ e0 => -[d /= d0] H'.
  near a^'+ => a0.
  rewrite (_ : f y = f a0)//.
    apply/esym/H.
    rewrite in_itv/=.
    by apply/andP.
  apply: H' => //=.
  rewrite ltr0_norm ?subr_lt0// opprB.
  rewrite ltrBlDl.
  near: a0; apply: nbhs_right_lt.
  by rewrite ltrDl.
move=> ax.
rewrite le_eqVlt => /predU1P[->|]; last first.
  move=> xb.
  apply: H => //.
  by rewrite in_itv/= ax.
clear x ax.
move: yab.
rewrite in_itv/= => /andP[ay].
rewrite le_eqVlt => /predU1P[<-//|yb].
move/continuous_within_itvP : cf => /(_ ab)[_ _ fbfb].
move/cvgrPdist_le in fbfb.
rewrite /= in fbfb.
apply/eqP.
rewrite -subr_eq0.
rewrite -normr_le0.
apply/ler_addgt0Pr => /= e e0.
rewrite add0r.
have := fbfb _ e0 => -[d /= d0] H'.
near b^'- => b0.
rewrite (_ : f y = f b0)//.
  apply/esym/H.
  rewrite in_itv/=.
  by apply/andP; split.
apply: H' => //=.
rewrite distrC.
rewrite ltr0_norm ?subr_lt0// opprB.
rewrite ltrBlDr.
rewrite -ltrBlDl.
near: b0; apply: nbhs_left_gt.
by rewrite ltrBlDl ltrDr.
Unshelve. all: by end_near. Qed.

Lemma oo_is_derive_0_is_cst {R : realType} (f : R -> R) y (a b : R) :
  y \in `]a, b[%R ->
  {within `[a, b], continuous f} ->
  (forall x, x \in `]a, b[%R -> is_derive x (1 : R) f 0) ->
  {in `[a, b]%R, f =1 cst (f y)}.
Proof.
move=> yab cf Hd.
apply: cst_oo_cc => //.
  exact: subset_itv_oo_cc yab.
move=> x xab.
wlog xLy : x y xab yab/ x <= y.
  move=> H; case: (leP x y) => [/H |/ltW xy].
  exact.
  by apply/esym/H => //.
rewrite -(subKr (f y) (f x)).
have : forall x0, x0 \in `]x, y[%R -> is_derive x0 1 f (0 x0).
  move=> z zxy.
  apply: Hd.
  move: zxy.
  apply: subset_itvSoo; rewrite bnd_simp.
  by rewrite ltW// (itvP xab).
  by rewrite ltW// (itvP yab).
move/MVT_segment => /(_ xLy)[].
  apply: continuous_subspaceW(* NB: should be , do a PRS*) cf.
  apply: subset_itvScc; rewrite bnd_simp.
  by rewrite ltW// (itvP xab).
  by rewrite ltW// (itvP yab).
move=> r rxy.
rewrite mul0r => ->.
by rewrite subr0.
Qed.

Lemma cc_is_derive_0_is_cst {R : realType} (f : R -> R) y (a b : R) :
  y \in `[a, b]%R ->
  {within `[a, b], continuous f} ->
  (forall x, x \in `]a, b[%R -> is_derive x (1 : R) f 0) ->
  {in `[a, b]%R, f =1 cst (f y)}.
Proof.
move => yab cont d x xab /=.
have : a <= b.
  move: xab.
  rewrite in_itv/= => /andP[].
  exact: le_trans.
rewrite le_eqVlt => /predU1P[ab|ab].
suff [-> ->] : b = x /\ b = y by [].
split; apply/eqP; rewrite eq_le.
by rewrite (itvP xab) -ab (itvP xab).
by rewrite (itvP yab) -ab (itvP yab).
suff [-> ->] : f x = f ((a + b) / 2) /\ f y = f ((a + b)/2) by [].
have ab2 : (a + b)/2 \in `]a, b[%R by rewrite in_itv/= !midf_lt.
by split; exact/oo_is_derive_0_is_cst.
Qed.

Lemma closed_ball_bounded {K : realType} {n} (x y : 'rV[K]_n) r :
  0 < r -> closed_ball x r y -> `|y| <= `|x| + r.
Proof.
move=> r0.
rewrite closed_ballE// /closed_ball_/= => dxy.
rewrite ler_distlCDr//.
by rewrite (le_trans (ler_dist_dist _ _)).
Qed.

Lemma closed_ballAE {K : realType} n (e : K) (x : 'rV[K]_n) :
  0 < e -> closed_ball x e = closed_ball_ (@mx_norm _ _ _) x e.
Proof.
by move=> e0; rewrite closed_ballE.
Qed.

Local Close Scope classical_set_scope.

Lemma maxE {K : realType} (x y : {nonneg K}) :
  (Num.max x%:num y%:num) = (Num.max x y)%:num.
Proof.
rewrite /Num.max /maxr; apply/esym.
case: ifPn => // xy.
  case: ifPn => //.
  rewrite -leNgt => yx.
  by apply/eqP; rewrite eq_le yx/= ltW.
case: ifPn => // yx.
apply/eqP; rewrite eq_le (ltW yx)/=.
by rewrite -leNgt in xy.
Qed.

Section gradient.

Definition jacobian1 {R : numFieldType} n (f : 'rV[R]_n -> R)
    : 'rV_n -> 'cV_n :=
  jacobian (scalar_mx \o f).

(* NB: not used *)
Definition partial {R : numFieldType} {n : nat} (f : 'rV[R]_n -> R) (a : 'rV[R]_n) i :=
  lim (h^-1 * (f (a + h *: 'e_i) - f a) @[h --> 0^'])%classic.

Lemma partial_diff {R : realFieldType} n (f : 'rV[R]_n -> R) (a : 'rV[R]_n)
    (i : 'I_n) :
  derivable f a 'e_i ->
  partial f a i = ('D_'e_i (@scalar_mx _ 1 \o f) a) 0 0.
Proof.
move=> fa1.
rewrite derive_mx ?mxE/=.
  exact: derivable_scalar_mx.
rewrite /partial.
under eq_fun do rewrite (addrC a).
by under [in RHS]eq_fun do rewrite !mxE/= !mulr1n.
Qed.

(* NB: not used *)
Definition err_vec {R : pzRingType} n (i : 'I_n) : 'rV[R]_n :=
  \row_(j < n) (i == j)%:R.

Lemma err_vecE {R : pzRingType} n (i : 'I_n) :
  err_vec i = 'e_i :> 'rV[R]_n.
Proof.
apply/rowP => j.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Definition gradient_partial {R : numFieldType} n (f : 'rV[R]_n -> R) (a : 'rV[R]_n) :=
  \row_(i < n) partial f a i.

Lemma gradient_partial_sum {R : numFieldType} n (f : 'rV[R]_n -> R) (a : 'rV[R]_n) :
  gradient_partial f a = \sum_(i < n) partial f a i *: 'e_i.
Proof.
rewrite /gradient_partial [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

Lemma gradient_partial_jacobian1 {R : realFieldType} n (f : 'rV[R]_n -> R)
    (v : 'rV[R]_n) : differentiable f v ->
  gradient_partial f v = (jacobian1 f v)^T.
Proof.
move=> fa; apply/rowP => i.
rewrite /gradient_partial mxE mxE /jacobian mxE -deriveE.
  apply: differentiable_comp => //.
  exact: differentiable_scalar_mx.
rewrite partial_diff//.
exact/diff_derivable.
Qed.

End gradient.
