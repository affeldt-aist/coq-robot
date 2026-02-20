From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra ring.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions filter reals.
From mathcomp Require Import topology ereal prodnormedzmodule normedtype.
From mathcomp Require Import sequences derive realfun landau measure.
From mathcomp Require Import lebesgue_integral.
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

(* PR to MCA *)
Section Rintegral.
Context d {T : measurableType d} {R : realType}.
Variable mu : {measure set T -> \bar R}.
Implicit Types (D : set T).

Lemma Rintegral_cst D : d.-measurable D ->
  forall r, \int[mu]_(_ in D) r = r * fine (mu D).
Proof.
move=> mD r; rewrite /Rintegral/= integral_cst//.
have := leey (mu D); rewrite le_eqVlt => /predU1P[->/=|muy]; last first.
  by rewrite fineM// ge0_fin_numE.
rewrite mulr0 mulr_infty/=; have [_|r0|r0] := sgrP r.
- by rewrite mul0e.
- by rewrite mul1e.
- by rewrite mulN1e.
Qed.

End Rintegral.

(* TODO: PR *)
Section vector_continuous.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.

Lemma within_continuous_coord (h : R -> U) D :
  {within D, continuous h} <-> forall i, {within D, continuous (fun x => h x ord0 i)}.
Proof.
split=> [Dh i|H].
- apply/subspace_continuousP => /= x Dx.
  have /subspace_continuousP/(_ x Dx) H := Dh.
  apply: ((@cvg_comp _ _ _ h (fun z => z ord0 i)) _ _ _ H).
  exact: coord_continuous.
- apply/subspace_continuousP => /= x Dx.
  apply/cvgrPdist_le => /= e e0.
  rewrite near_withinE.
  near=> t => Dt.
  rewrite /Num.norm/= mx_normrE.
  apply/(bigmax_le _ (ltW e0)) => /= -[i j] _ /=.
  rewrite {i}(ord1 i) !mxE.
  move: j Dt.
  near: t.
  apply: filter_forall => /= i.
  have /subspace_continuousP/(_ x Dx) := H i.
  move/cvgrPdist_le => /(_ _ e0).
  rewrite near_withinE.
  exact.
Unshelve. all: by end_near. Qed.

End vector_continuous.

Lemma continuous_within_ext {A B : topologicalType} (g h : A -> B) D :
  {in D, g =1 h} ->
  {within D, continuous g } -> {within D, continuous h}.
Proof.
move=> h1 h2.
apply subspace_continuousP.
move => x Dx.
apply : cvg_trans.
apply (fmap_within_eq (g := g)) => //.
apply nbhs_filter.
move => x' Dx' .
symmetry.
by apply h1.
rewrite <-h1.
move /subspace_continuousP : h2.
by apply.
by rewrite inE.
Qed.

(* PR to MCA *)
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
  rewrite (@itv_bndbnd_setU _ _ _ (BRight b)) // ?bnd_simp//=; [|exact: ltW..].
  apply/seteqP; split => [x []|x []].
  by left.
  by right; exact: subset_itv_oc_cc b0.
  by left.
  rewrite -setU1itv ?bnd_simp//; last exact: ltW.
  case; last by right.
  move=> ->; left => /=.
  by rewrite bound_itvE ltW.
apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b c)).
  have eq1 : {in `[a, b], f =1 patch g `[a, b] f }.
    by move=> r rab; rewrite /patch rab.
  apply: (continuous_within_ext eq1).
  exact: cont1.
have eq2 : {in `[b, c], g =1 patch g `[a, b] f }.
  move=> r rab.
  rewrite /patch; case: ifPn => [xab | xabnot] => //.
  suff -> : r = b by rewrite matchb.
  apply: le_anti.
  move: rab xab.
  by rewrite !inE/=!in_itv/= => /andP [-> _] /andP [_ ->].
apply/continuous_subspaceW/(continuous_within_ext eq2)/cont2.
by apply: subset_itvl; rewrite bnd_simp.
Qed.

End continuous_patch.

Lemma within_continuousB {K : realType} {V : normedModType K}
    (A : set K) (f g : _ -> V) :
  {within A, continuous f} -> {within A, continuous g} ->
  {within A, continuous (f - g)}.
Proof.
by move=> cf cg x; apply: cvgB; [exact: cf|exact: cg].
Qed.

(* TODO: PR to MCA *)
Lemma nbhs_ge {R : realFieldType} (t x : R) :
  t < x -> \forall x0 \near nbhs x, t <= x0.
Proof.
move=> tx.
exists ((x - t) / 2).
  by rewrite /= divr_gt0// subr_gt0.
move=> y/=.
have [xy|yx] := lerP x y.
  rewrite ltrBlDl => H.
  by rewrite (le_trans (ltW tx)).
rewrite ltrBlDl -ltrBlDr => /ltW; apply: le_trans.
rewrite -lerBlDr opprK.
by rewrite -lerBrDl ler_piMr ?invf_le1 ?ler1n// subr_ge0 ltW.
Qed.

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

(* NB: PR to PCA *)
Section pointwise_derivable.
Context {R : realFieldType} {V W : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

Definition derivable_mx M t v :=
  forall i j, derivable (fun x => M x i j) t v.

Lemma derivable_mxP M t v : derivable_mx M t v <-> derivable M t v.
Proof.
split; rewrite /derivable_mx /derivable.
- move=> H.
  apply/cvg_ex => /=.
  pose l := \matrix_(i < m, j < n) sval (cid ((cvg_ex _).1 (H i j))).
  exists l.
  apply/cvgrPdist_le => /= e e0.
  near=> x.
  rewrite /Num.Def.normr/= mx_normrE.
  apply: (bigmax_le _ (ltW e0)) => /= i _.
  rewrite !mxE/=.
  move: i.
  near: x.
  apply: filter_forall => /= i.
  exact: ((@cvgrPdist_le _ _ _ _ (dnbhs_filter 0) _ _).1
    (svalP (cid ((cvg_ex _).1 (H i.1 i.2)))) _ e0).
- move=> /cvg_ex[/= l Hl] i j.
  apply/cvg_ex; exists (l i j).
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0] H.
  near=> x.
  apply: le_trans; last first.
    apply: (H x).
    rewrite /ball_/=.
    rewrite sub0r normrN.
    near: x.
    exact: dnbhs0_lt.
    near: x.
    exact: nbhs_dnbhs_neq.
  rewrite [leRHS]/Num.Def.normr/= mx_normrE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite /= !mxE.
Unshelve. all: by end_near. Qed.

End pointwise_derivable.

(* NB: PR to MCA *)
Section pointwise_derive.
Local Open Scope classical_set_scope.
Context {R : realFieldType} {V W : normedModType R} .

Lemma derive_mx {m n : nat} (M : V -> 'M[R]_(m, n)) t v :
  derivable M t v ->
  'D_v M t = \matrix_(i < m, j < n) 'D_v (fun t => M t i j) t.
Proof.
move=> /cvg_ex[/= l Hl]; apply/cvg_lim => //=.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : (Hl) => /(_ (e / 2)).
rewrite divr_gt0// => /(_ isT)[d /= d0 dle].
near=> x.
rewrite [in leLHS]/Num.Def.normr/= mx_normrE.
apply/(bigmax_le _ (ltW e0)) => -[/= i j] _.
rewrite [in leLHS]mxE/= [X in _ + X]mxE -[X in X - _](subrK (l i j)).
rewrite -(addrA (_ - _)) (le_trans (ler_normD _ _))// (splitr e) lerD//.
- rewrite mxE.
  suff : (h^-1 *: (M (h *: v + t) i j - M t i j)) @[h --> 0^'] --> l i j.
    move/cvg_lim => /=; rewrite /derive /= => ->//.
    by rewrite subrr normr0 divr_ge0// ltW.
  apply/cvgrPdist_le => /= r r0.
  move/cvgrPdist_le : Hl => /(_ r r0)[/= s s0] sr.
  near=> y.
  have : `|l - y^-1 *: (M (y *: v + t) - M t)| <= r.
    rewrite sr//=; last by near: y; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: y; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
  by under eq_bigr do rewrite !mxE; exact: (le_bigmax _ _ (i, j)).
- rewrite mxE.
  have : `|l - x^-1 *: (M (x *: v + t) - M t)| <= e / 2.
    apply: dle => //=; last by near: x; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: x; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE/=.
  under eq_bigr do rewrite !mxE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite !mxE.
Unshelve. all: by end_near. Qed.

End pointwise_derive.

Lemma differentiable_scalar_mx {R : numFieldType} n (r : R) :
  differentiable (@scalar_mx _ n) r.
Proof.
apply/derivable1_diffP/cvg_ex => /=.
exists 1; apply/cvgrPdist_le => /= e e0.
near=> t.
rewrite scaler1 -raddfB/= addrK (scale_scalar_mx _ t^-1) mulVf.
  by rewrite subrr normr0 ltW.
by near: t; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

Lemma derivable_sqrt {K: realType} (u : K) : u > 0 -> derivable Num.sqrt u 1.
Proof.
move=> u0.
apply: ex_derive.
exact: (is_derive1_sqrt u0).
Qed.

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

Lemma within_continuous_minus {R : realType} {K : numDomainType}
    {U : pseudoMetricNormedZmodType K} (f : R -> U) (a b : R) :
  {within `[- b, - a], continuous f} -> {within `[a, b], continuous f \o -%R}.
Proof.
have [ab|ba _ |-> _] := ltgtP a b; last 2 first.
  by rewrite set_itv_ge ?bnd_simp -?ltNge//; exact: continuous_subspace0.
  by rewrite set_itv1; exact: continuous_subspace1.
move/continuous_within_itvP; rewrite ltrN2 => /(_ ab)[cf fb fa].
apply/(continuous_within_itvP _ ab); split.
- move=> t tab.
  apply: (@cvg_comp _ _ _ -%R f); first exact: oppr_continuous.
  by apply: cf; rewrite oppr_itvoo !opprK.
- by rewrite -{1}(opprK a); apply/cvg_at_leftNP; exact: fa.
- by rewrite -{1}(opprK b); apply/cvg_at_rightNP; exact: fb.
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
(* PR to MCA *)
Lemma EVT_max_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
  A !=set0 ->
  compact A ->
  {within A, continuous f} -> exists2 c, c \in A &
  forall t, t \in A -> f t <= f c.
Proof.
move=> A0 compactA fcont; set imf := f @` A.
have imf_sup : has_sup imf.
  split.
    case: A0 => a Aa.
    by exists (f a); apply/imageP.
  have [M [Mreal imfltM]] : bounded_set (f @` A).
    exact/compact_bounded/continuous_compact.
  exists (M + 1) => y /imfltM yleM.
  by rewrite (le_trans _ (yleM _ _)) ?ler_norm ?ltrDl.
have [|imf_ltsup] := pselect (exists2 c, c \in A & f c = sup imf).
  move=> [c cab fceqsup]; exists c => // t tab; rewrite fceqsup.
  apply/sup_upper_bound => //.
  exact/imageP/set_mem.
have {}imf_ltsup t : t \in A -> f t < sup imf.
  move=> tab; case: (ltrP (f t) (sup imf)) => // supleft.
  rewrite falseE; apply: imf_ltsup; exists t => //; apply/eqP.
  rewrite eq_le supleft andbT sup_upper_bound//.
  exact/imageP/set_mem.
pose g t : R := (sup imf - f t)^-1.
have invf_continuous : {within A, continuous g}.
  rewrite continuous_subspace_in => t tab; apply: cvgV => //=.
    by rewrite subr_eq0 gt_eqF // imf_ltsup //; rewrite inE in tab.
  by apply: cvgD; [exact: cst_continuous | apply: cvgN; exact: (fcont t)].
have /ex_strict_bound_gt0 [k k_gt0 /= imVfltk] : bounded_set (g @` A).
  by apply/compact_bounded/continuous_compact.
have [_ [t tab <-]] : exists2 y, imf y & sup imf - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
rewrite ltrBlDr -ltrBlDl.
suff : sup imf - f t > k^-1 by move=> /ltW; rewrite leNgt => /negbTE ->.
rewrite -[ltRHS]invrK ltf_pV2// ?qualifE/= ?invr_gt0 ?subr_gt0 ?imf_ltsup//; last first.
  exact/mem_set.
by rewrite (le_lt_trans (ler_norm _) _) ?imVfltk//; exact: imageP.
Qed.

(* PR to MCA *)
Lemma EVT_min_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
  A !=set0 ->
  compact A ->
  {within A, continuous f} -> exists2 c, c \in A &
  forall t, t \in A -> f c <= f t.
Proof.
move=> A0 cA fcont.
have /(EVT_max_rV A0 cA) [c clr fcmax] : {within A, continuous (- f)}.
  by move=> ?; apply: continuousN => ?; exact: fcont.
by exists c => // ? /fcmax; rewrite lerN2.
Qed.

Section closure_neitv.
Context {R : realType}.
Implicit Type a b : R.

Lemma closure_neitv_oo a b : a < b ->
  closure `]a, b[%classic = `[a, b]%classic.
Proof.
move=> ab.
set c := (a + b) / 2%:R.
set d := (b - a) / 2%:R.
rewrite (_ : a = c - d); last by rewrite /c/d !mulrDl addrKA mulNr opprK -splitr.
rewrite (_ : b = c + d); last by rewrite addrC /c/d !mulrDl mulNr subrKA -splitr.
rewrite -ball_itv -closed_ball_itv ?closure_ballE//.
apply: divr_gt0 => //.
by rewrite subr_gt0.
Qed.

End closure_neitv.

(* TODO: move *)
Lemma open_disjoint_separated (X : topologicalType) (A B : set X) :
  open A -> open B -> A `&` B = set0 -> separated A B.
Proof.
move=>Ao Bo ABdisj.
split.
apply /disjoints_subset.
rewrite (closure_id (~` B)).1; last by apply open_closedC.
by apply /closure_subset/disjoints_subset.
rewrite setIC;apply /disjoints_subset.
rewrite (closure_id (~` A)).1; last by apply open_closedC.
apply /closure_subset/disjoints_subset.
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
  rewrite (_ : f y = f a0)//; last first.
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
rewrite (_ : f y = f b0)//; last first.
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

Lemma ball0_le0 (R : realDomainType) (V : pseudoMetricNormedZmodType R) (a : V) (r : R) :
  ball a r = set0 -> r <= 0.
Proof.
rewrite -subset0 => ar0; rewrite leNgt; apply/negP => r0.
by have /(_ (ballxx _ r0)) := ar0 a.
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
rewrite derive_mx ?mxE//=; last first.
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
rewrite /gradient_partial mxE mxE /jacobian mxE -deriveE; last first.
  apply: differentiable_comp => //.
  exact: differentiable_scalar_mx.
rewrite partial_diff//.
exact/diff_derivable.
Qed.

End gradient.
