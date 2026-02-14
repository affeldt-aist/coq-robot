From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra ring.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun landau.
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
  y \in `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `]a, b[, f =1 cst (f y)} ->
  {in `[a, b], f =1 cst (f y)}.
Proof.
have [ab|ba] := ltP a b; last first.
  move=> yab _ H x.
  rewrite inE/= in_itv/= => /andP[ax xb].
  have /eqP ? : a == x by rewrite eq_le ax (le_trans xb _).
  subst x.
  move: yab; rewrite inE/= in_itv/= => /andP[ay yb].
  have /eqP ? : a == y by rewrite eq_le ay (le_trans yb _).
  by subst.
move=> yab cf H x.
rewrite inE/= in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<-{x} _|].
  move: yab; rewrite inE/= in_itv/= => /andP[].
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
    rewrite inE/= in_itv/=.
    by apply/andP; split => //.
  apply: H' => //=.
  rewrite ltr0_norm ?subr_lt0// opprB.
  rewrite ltrBlDl.
  near: a0.
  apply: nbhs_right_lt.
  by rewrite ltrDl.
move=> ax.
rewrite le_eqVlt => /predU1P[->|]; last first.
  move=> xb.
  apply: H => //.
  by rewrite inE/= in_itv/= ax.
clear x ax.
move: yab.
rewrite inE/= in_itv/= => /andP[ay].
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
  rewrite inE/= in_itv/=.
  by apply/andP; split => //.
apply: H' => //=.
rewrite distrC.
rewrite ltr0_norm ?subr_lt0// opprB.
rewrite ltrBlDr.
rewrite -ltrBlDl.
near: b0.
apply: nbhs_left_gt.
by rewrite ltrBlDl ltrDr.
Unshelve. all: by end_near. Qed.

Lemma is_derive_0_is_cst_new {R : realType} (f : R -> R) y (a b : R) :
  y \in `]a, b[ ->
  {within `[a, b], continuous f} ->
  (forall x, x \in `]a, b[ -> is_derive x (1 : R) f 0) -> {in `[a, b], f =1 cst (f y)}.
Proof.
move=> yab cf Hd.
apply: cst_oo_cc => //.
  move: yab.
  rewrite !inE/=.
  by apply: subset_itv_oo_cc.
move=> x xab.
wlog xLy : x y xab yab/ x <= y.
  move=> H; case: (leP x y) => [/H |/ltW xy].
  exact.
  by apply/esym/H => //.
rewrite -(subKr (f y) (f x)).
have [| |] := @MVT_segment R f 0 _ _ xLy.
- move=> z zxy.
  apply: Hd.
  move: zxy.
  rewrite inE/=.
  apply: subset_itvSoo; rewrite bnd_simp.
  by move: xab; rewrite inE/= in_itv/= => /andP[/ltW].
  by move: yab; rewrite inE/= in_itv/= => /andP[_ /ltW].
- apply: continuous_subspaceW(* NB: should be , do a PRS*) cf.
  apply: subset_itvScc; rewrite bnd_simp.
  by move: xab; rewrite inE/= in_itv/= => /andP[/ltW].
  by move: yab; rewrite inE/= in_itv/= => /andP[_ /ltW].
move=> r rxy.
rewrite mul0r => ->.
by rewrite subr0.
Qed.

Lemma is_derive_0_is_cst_new' {R : realType} (f : R -> R) y (a b : R) :
  y \in `[a, b] ->
  {within `[a, b], continuous f} ->
  (forall x, x \in `]a, b[ -> is_derive x (1 : R) f 0) -> {in `[a, b], f =1 cst (f y)}.
Proof.
move => yab cont d x xab /=.
have : (a <= b).
  move: xab.
  rewrite inE/=in_itv/= => /andP[].
  by apply le_trans.
rewrite le_eqVlt => /predU1P[ab|ab].
suff [-> ->] : b = x /\ b = y by [].
split;apply /eqP;rewrite eq_le.
by move : xab;rewrite !ab !inE/=!in_itv/=.
by move : yab;rewrite !ab !inE/=!in_itv/=.
suff [-> ->] : f x = f ((a + b) / 2) /\ f y = f ((a+b )/2) by [].
have ab2: (a+b)/2 \in `]a,b[.
  rewrite inE/=in_itv/=.
  apply/andP;split.
  by rewrite ltr_pdivlMr // mulrDr mulr1 ler_ltD //.
  rewrite ltr_pdivrMr // mulrDr mulr1 ltr_leD //.
by split;apply /is_derive_0_is_cst_new.
Qed.

Lemma closed_ball_bounded {K : realType} {n} (x y : 'rV[K]_n) r : 0 < r -> closed_ball x r y ->
  `|y| <= `|x| + r.
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
