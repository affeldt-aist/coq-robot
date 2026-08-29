From HB Require Import structures.
From mathcomp Require Import boot order algebra ring_tactic
  interval_inference.
From mathcomp Require Import boolp classical_sets functions filter reals
  topology ereal prodnormedzmodule normedtype sequences derive realfun
  landau measure lebesgue_integral lebesgue_measure
  lebesgue_stieltjes_measure measurable_realfun ftc.
Require Import ssr_ext derive_matrix.

(**md**************************************************************************)
(* # Additions to MathComp-Analysis                                           *)
(*                                                                            *)
(* Properties of Lipschitz functions, etc.                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma closed_ball_coord {R : realType} {n} (x0 : 'rV[R]_n) (r : R) x :
  0 < r ->
  closed_ball x0 r x <-> forall i, closed_ball (x0 ord0 i) r (x ord0 i).
Proof.
move=> r0; split.
- rewrite closed_ballE /closed_ball_ //=.
  rewrite /Num.norm/= mx_normrE => h i.
  rewrite closed_ballE// /closed_ball_/=.
  apply/le_trans/h.
  have -> : x0 ord0 i - x ord0 i = (x0 - x) ord0 i by rewrite !mxE.
  exact: (le_bigmax _ _ (ord0, i)).
- move=> h.
  rewrite closed_ballE// /closed_ball_/=.
  rewrite [in leLHS]/Num.norm/= mx_normrE.
  apply: (bigmax_le _ (ltW r0)) => /= -[i j] _ /=.
  rewrite {i}(ord1 i)/=.
  move /(_ j) : h.
  by rewrite closed_ballE// /closed_ball_ /= 2!mxE.
Qed.

Section lipschitz_coord.
Context {R : realFieldType} {n} (U := 'rV[R]_n) (f : U -> U) (k : R)
  (B : set U).
Hypothesis k0 : 0 <= k.

Lemma lipschitz_coord : k.-lipschitz_B f <->
  forall i, k.-lipschitz_B (fun y => f y ord0 i).
Proof.
split.
- move => lip i /= [x1 x2] /= Bx12.
  move /(_ (x1,x2) Bx12) : lip.
  apply le_trans => /=.
  rewrite /Num.norm/= mx_normrE.
  have -> : f x1 ord0 i - f x2 ord0 i = (f x1 - f x2) ord0 i.
    by rewrite !mxE.
  exact: (le_bigmax _ _ (ord0, i)).
- move => h /= [x1 x2] Bx12 /=.
  rewrite [in leLHS]/Num.norm/= mx_normrE.
  apply/bigmax_le.
    by rewrite mulr_ge0 //= ltW.
  move => //= -[i j] _ /=.
  rewrite {i}(ord1 i)/=.
  move /(_ j (x1,x2) Bx12) : h.
  by rewrite !mxE.
Qed.

End lipschitz_coord.

Lemma bounded_derivative_lipschitz {R : realType} {n} (a b M : R)
    (f : R -> 'rV[R]_n) :
  0 <= M ->
  {within `[a, b], continuous f} ->
  {in `]a, b[%R, forall x, derivable f x 1 /\ `| f^`() x | <= M} ->
  {in `]a, b[%R &, forall s t, `| f t - f s | <= M * `|t - s|}.
Proof.
move => M0 cont /= deri s t sab tab.
rewrite {1}/Num.norm /= mx_normrE.
apply: bigmax_le; first by rewrite mulr_ge0 // normr_ge0.
move => /=  [i0 i] _.
rewrite ord1 !mxE /=.
wlog st : s t sab tab / s <= t.
  move => H.
  have [st|ts] := leP s t.
    exact: H.
  rewrite distrC (distrC t).
  apply H => //.
  by apply ltW.
have [ | |c cst ->]:= @MVT_segment _ (fun t => f t 0 i) ('D_1 (fun t => f t 0 i)) _ _ st.
- move => x xst.
  have xab : x \in `]a, b[%R.
    by apply: subset_itv xst; rewrite bnd_simp ?(itvP sab) ?(itvP tab).
  apply /derivableP.
  have [/derivable_mxP + _] := deri x xab.
  by apply.
- move/within_continuous_coord : cont.
  move=> /(_ i).
  apply: continuous_subspaceW.
  by apply: subset_itv; rewrite bnd_simp ltW ?(itvP sab) ?(itvP tab).
rewrite -derive1E/= normrM ler_wpM2r//.
have cab: c \in `]a,b[%R.
  by apply: subset_itv cst; rewrite bnd_simp ?(itvP sab) ?(itvP tab).
have [_  + ] := deri c cab.
rewrite {1}/Num.norm /= mx_normrE.
apply: le_trans.
suff -> : (fun t0 : R => f t0 0 i)^`() c =  f^`() c 0 i.
  exact: (le_bigmax _ _ (ord0, i)).
rewrite !derive1E !derive_mx.
  by apply deri.
by rewrite mxE.
Qed.

(* only for autonomous, used for tilt *)
Definition autonomous_locally_lipschitz {R : realType} n (U := 'rV[R]_n)
   (phi : U -> U) :=
 forall x,
   exists r k : {posnum R}, k%:num.-lipschitz_(closed_ball x r%:num) phi.

Lemma autonomous_locally_lipschitzP {R : realType} n (U := 'rV[R]_n)
    (phi : U -> U) :
  autonomous_locally_lipschitz phi <->
  [locally [lipschitz phi x | x in [set: U]]].
Proof.
split.
  (* locally_lipschitz phi -> [locally lipschitz phi] *)
  move=> lip_phi /= -[/= a b _].
  rewrite /lipschitz_on.
  have [ra [ka lipa]] := lip_phi a.
  have [rb [kb lipb]] := lip_phi b.
  rewrite /dominated_by /globally /= in lipa.
  rewrite /dominated_by /globally /= in lipb.
  have [ab|ab] := eqVneq a b.
    near=> M.
    rewrite setXTT.
    rewrite /dominated_by.
    rewrite withinET.
    rewrite /autonomous_locally_lipschitz /= in lip_phi.
    apply/nbhs_closedballP.
    subst b.
    exists ra => -[u v].
    rewrite closed_ballE// /closed_ball_/= => H.
    rewrite {1}/Num.norm /ProdNormedZmodule.norm/= /ProdNormedZmodule.norm/= in H.
    rewrite (@le_trans _ _ (ka%:num * `|u - v|))//; last by rewrite ler_pM//.
    apply: (lipa (u, v)) => //=; split.
      rewrite closed_ballE// /closed_ball_/=.
      rewrite (le_trans _ H)//.
      by rewrite le_max lexx.
    rewrite closed_ballE// /closed_ball_/=.
    rewrite (le_trans _ H)//.
    by rewrite le_max lexx orbT.
  rewrite setXTT.
  rewrite withinET.
  rewrite /autonomous_locally_lipschitz /= in lip_phi.
  have ab20 : `|a - b| / 4 > 0 by rewrite divr_gt0// normr_gt0 subr_eq0.
  have ab20' : `|a - b| / 2 > 0 by rewrite divr_gt0// normr_gt0 subr_eq0.
  pose r := minr (PosNum ab20) (minr ra rb).
  near=> M.
  apply/nbhs_closedballP.
  exists r => -[/= u v].
  rewrite closed_ballE// /closed_ball_/= => H.
  have rra : r <= ra by rewrite /r !ge_min lexx !orbT.
  have rrb : r <= rb by rewrite /r !ge_min lexx !orbT.
  have rab0 : r <= PosNum ab20 by rewrite /r !ge_min lexx.
  have -> : phi u - phi v = ((phi u - phi a)(* <k *) +
                             (phi a - phi b) (* < r *) +
                             (phi b - phi v)) by rewrite -addrA !subrKA.
  rewrite (@le_trans _ _ ( ka%:num * r%:num +
                           `|phi a - phi b| +
                           kb%:num * r%:num))//.
    rewrite (le_trans (ler_normD _ _))//.
    rewrite lerD//.
    + rewrite (le_trans (ler_normD _ _))//.
      rewrite lerD//.
      rewrite (@le_trans _ _ (ka%:num * `|u - a|))//.
        move /(_ (u, a)): lipa; apply.
        rewrite closed_ballE// /closed_ball_/= subrr normr0=>[]//.
        split=>//.
        rewrite (@le_trans _ _  r%:num)//.
        by rewrite (le_trans _ H) /Num.norm//= le_max lexx.
      by rewrite distrC ler_pM// (le_trans _ H) /Num.norm//= le_max lexx.
    + rewrite (@le_trans _ _ (kb%:num * `|b - v|))//.
         move /(_ (b, v)): lipb; apply.
         rewrite closed_ballE// /closed_ball_/= subrr normr0=>[]//; split=>//.
         rewrite (@le_trans _ _  r%:num)//.
         by rewrite (le_trans _ H) /Num.norm//= le_max lexx orbT.
      by rewrite ler_pM// (le_trans _ H) /Num.norm//= le_max lexx orbT.
  have rp0 : `|a - b| <= `|a - b| / 2 + `|u-v|.
    have -> : a - b = (a - u)  + (v - b) + (u - v) by rewrite addrAC !subrKA.
    rewrite (le_trans (ler_normD _ _))// lerD2r.
    apply (@le_trans _ _ ( r%:num + r%:num)).
      rewrite (le_trans (ler_normD _ _))//lerD//.
        by rewrite (le_trans _ H) /Num.norm//= le_max lexx.
      by rewrite distrC (le_trans _ H) /Num.norm//= le_max lexx orbT.
    rewrite addrAC !subrKA.
    rewrite [leRHS]splitr lerD//.
      by rewrite -mulrA -invrM ?unitfE// -natrM.
    by rewrite -mulrA -invrM ?unitfE// -natrM.
  have rp :  r%:num  <= `|u-v|.
    rewrite (@le_trans _ _ (`|a - b|/ 4))//.
    rewrite (@le_trans _ _ (`|a - b|/ 2))//.
      by rewrite [leRHS]splitr -mulrA -invrM ?unitfE //= (natrM _ 2 2) lerDl divr_ge0//.
    move: rp0.
    by rewrite [leLHS]splitr lerD2l.
  set C :=  ka%:num * r%:num + `|phi a - phi b| + kb%:num * r%:num.
  apply: (@le_trans _ _ (C/r%:num * `|u-v|)).
    rewrite -mulrA;apply: ler_peMr; rewrite ?addr_ge0//.
    by rewrite ler_pdivlMl// mulr1.
  by rewrite ler_pM// divr_ge0// !addr_ge0.
(* [locally lipschitz phi] -> locally_lipschitz phi *)
move=> lip_phi /= a.
rewrite /locally_of /= setXTT in lip_phi.
have := lip_phi (a, a) (conj Logic.I Logic.I).
rewrite /lipschitz_on => -[M [Mreal]].
rewrite withinET => HM.
have M0 : 0 < `|M| + 1 by rewrite ltr_wpDl.
have MM0 : M < `|M| + 1 by rewrite (le_lt_trans (ler_norm _)) // ltrDl.
have /(_ MM0) := HM (`|M| + 1).
case => /= => CD [aC aD] H.
have [r1 Hr1] : exists r1 : {posnum R}, closed_ball a r1%:num `<=` CD.1.
  by move/nbhs_closedballP : aC.
have [r2 Hr2] : exists r2 : {posnum R}, closed_ball a r2%:num `<=` CD.2.
  by move/nbhs_closedballP : aD.
exists (minr r1 r2).
exists (PosNum M0).
rewrite /dominated_by /globally /=.
move=> uv [au av].
apply: H.
split.
  apply: Hr1.
  apply: le_closed_ball au.
  suff : minr r1 r2 <= r1 by [].
  by rewrite ge_min lexx.
apply: Hr2.
apply: le_closed_ball av.
suff : minr r1 r2 <= r2 by [].
by rewrite ge_min lexx orbT.
Unshelve. all: by end_near. Qed.

Section lipschitz_left_limit.
Context {R : realType} {n} (U := 'rV[R]_n) (a b k : R) (f : R -> U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Hypothesis f_lip sol :
  {in `]a, b[%R &, forall s t, `| f t - f s | <= k * `|t - s|}.

Lemma lipschitz_has_left_limit : f @ b^'- --> lim (f @ b^'-).
Proof.
apply/cauchy_cvgP; apply/cauchyP => eps eps0 /=.
have e2k0 : 0 < eps / k / 2 by rewrite divr_gt0 // divr_gt0.
near b^'- => s.
exists (f s).
near=> t.
rewrite /= -ball_normE /=.
apply: le_lt_trans; first apply f_lip.
- rewrite in_itv/=; apply/andP; split.
    near: t; apply: cvg_at_left_filter; first by apply cvg_id.
    exact: lt_nbhsr.
  by near: t; exact: nbhs_left_lt.
- rewrite in_itv/=; apply/andP; split.
    near: s; apply: cvg_at_left_filter; first by apply cvg_id.
    exact: lt_nbhsr.
  by near: s; exact: nbhs_left_lt.
rewrite mulrC -ltr_pdivlMr//.
rewrite -(subrKA b) (le_lt_trans (ler_normD _ _)) // (splitr (eps / k)) ltrD//.
  suff: ball b (eps / k / 2) s by rewrite -ball_normE /ball_ /= distrC.
  near: s; apply: cvg_at_left_filter; first by apply cvg_id.
  exact: nbhsx_ballx.
suff: ball b (eps / k / 2) t by rewrite -ball_normE /ball_ /= distrC.
near: t; apply: cvg_at_left_filter; first by apply cvg_id.
exact: nbhsx_ballx.
Unshelve. all: by end_near. Qed.

End lipschitz_left_limit.

Lemma row_mx_norm_le_sum {R : realType} {n} (x : 'rV[R]_n) :
  `| x | <=  \sum_(i < n) `|x ord0 i|.
Proof.
rewrite {1}/Num.norm/= mx_normrE.
apply: bigmax_le => /=;first by apply sumr_ge0 => i _; exact: normr_ge0.
move =>  [i0 i] _ /=.
rewrite {i0}(ord1 i0)/=.
rewrite (bigD1 i) //= lerDl.
by apply: sumr_ge0 => j _; exact: normr_ge0.
Qed.

Section measurable_fun_bigmaxr.
Import MeasurableR.

(* NB: PR in progress *)
Lemma measurable_bigmaxr d (T : measurableType d) (R : realType) (D : set T)
  def {n} (f : 'I_n -> T -> R) :
  (forall i, measurable_fun D (f i)) ->
  measurable_fun D (fun x => \big[maxr/def]_(i < n) f i x).
Proof.
elim: n f => [|n ih] f mf.
  by under eq_fun do rewrite big_ord0/=; exact: measurable_cst.
under eq_fun do rewrite big_ord_recl/=.
by apply: measurable_maxr; [exact: mf|apply: ih => i; exact: mf].
Qed.

End measurable_fun_bigmaxr.

Section integrable_row_mx_norm.
Import MeasurableR.

Lemma measurable_row_mx_norm {R : realType} {n} (D : set R) (F : R -> 'rV[R]_n):
   measurable D -> (forall i, measurable_fun D (fun t => F t ord0 i)) ->
  measurable_fun D (Num.norm \o F).
Proof.
move=> mD h.
have -> : normr \o F = (fun x => \big[maxr/0]_(i < n) `| F x ord0 i |).
  apply: funext => x.
  rewrite  {1}/Num.norm/= mx_normrE.
  rewrite (reindex (fun i : 'I_n => (ord0, i))) => //=.
  exists (@snd 'I_1 'I_n) => /=.
  + by move => i.
  + move => [i j] /= _.
    by rewrite {i}(ord1 i).
apply: measurable_bigmaxr => //= i.
by apply: measurableT_comp => //=.
Qed.

Lemma integrable_row_mx_norm {R : realType} {n} (D : set R) (F : R -> 'rV[R]_n):
  measurable D ->
  (forall i, lebesgue_measure.-integrable D (EFin \o (fun t => F t ord0 i))) ->
  lebesgue_measure.-integrable D (EFin \o (Num.norm \o F)).
Proof.
move => mD intf.
apply (le_integrable (mu:=lebesgue_measure) mD (f := EFin \o (normr \o F))
    (g := EFin \o fun x => (\sum_(i < n) `| F x ord0 i|))).
- apply/measurable_EFinP.
  apply measurable_row_mx_norm => // i.
  have /integrableP[+ _]/= := intf i.
  by move/measurable_EFinP.
- move => /= x0 Dx0.
  rewrite normr_id.
  rewrite lee_fin.
  rewrite ger0_norm ?sumr_ge0//.
  exact: row_mx_norm_le_sum.
- have -> : EFin \o (fun x => \sum_(i < n) `|F x ord0 i|) =
            fun x => (\sum_(i < n) `|F x ord0 i|%:E).
    by apply/funext => x; rewrite sumEFin.
  apply: integrable_sum => //= i _.
  exact: integrable_norm.
Qed.

End integrable_row_mx_norm.

(* NB: PR in progress *)
Lemma parameterized_integralN {R : realType}
    x b (f : R -> R) : (x <= b) ->
  {within `[x, b], continuous f} ->
  parameterized_integral lebesgue_measure x b f =
  parameterized_integral lebesgue_measure (- b) (- x) (f \o -%R).
Proof.
move=> xb cf.
rewrite /parameterized_integral /Rintegral.
rewrite -(@integration_by_substitution_oppr _ f (- b) (- x)) ?opprK//.
by rewrite lerN2.
Qed.

Section parameterized_integral_continuous.
Context {R : realType}.
Notation mu := (@lebesgue_measure R).

Let int := (parameterized_integral mu).

(* NB: PR in progress *)
Lemma parameterized_integralN_continuous a b (f : R -> R) : a <= b ->
  {within `[a, b], continuous f} ->
  {within `[a, b], continuous (fun x => int x b f)}.
Proof.
move=> ab abf; suff: {within `[a, b], continuous
    ((fun x => parameterized_integral mu (- b) x (f \o -%R)) \o -%R)}.
  apply: subspace_eq_continuous => /= x /[!inE] xab/=.
  rewrite /from_subspace/= -parameterized_integralN ?(itvP xab)//.
  apply: continuous_subspaceW abf.
  by apply: subset_itvr; rewrite bnd_simp (itvP xab).
apply: within_continuous_compN.
apply: parameterized_integral_continuous; first by rewrite lerN2.
apply: continuous_compact_integrable => //; first exact: segment_compact.
by apply: within_continuous_compN; rewrite !opprK.
Qed.

End parameterized_integral_continuous.

Section integral_cst.
Context {d} {T : measurableType d} {R : realType}
  (mu : {measure set T -> \bar R}).

(* TODO: PR? *)
Lemma integrable_cst D (c : R) : measurable D -> (mu D < +oo)%E ->
  mu.-integrable D (EFin \o cst c).
Proof.
move => h1 h2.
apply: measurable_bounded_integrable => //=.
exact: bounded_cst.
Qed.

End integral_cst.

(* TODO: move *)
Lemma closed_ball_split {R : realFieldType} (U : normedModType R) (x1 x2 y : U)
    q : 0 < q ->
  closed_ball x1 (q / 2) y -> closed_ball x2 (q / 2) x1 -> closed_ball x2 q y.
Proof.
move=> q0.
have q20 : 0 < q / 2 by rewrite divr_gt0.
rewrite !closed_ballE// /closed_ball_ /= => h1 h2.
by rewrite -(subrKA x1 x2) (le_trans (ler_normD _ _))// (splitr q) lerD.
Qed.

(* TODO: to appear in MCA 1.18.0 *)
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
Context {R : realType} {U : normedModType R}
  (a b c : R) (f : R -> U) (g : R -> U).

Hypothesis ab : a <= b.
Hypothesis bc : b <= c.
Hypothesis cont1 : {within `[a, b], continuous f}.
Hypothesis cont2 : {within `[b, c], continuous g}.
Hypothesis matchb : f b = g b.

Lemma within_continuous_patch : {within `[a, c], continuous (patch g `[a, b] f)}.
Proof.
have -> : `[a, c] = `[a, b] `|` `[b, c].
  rewrite [in RHS](@itv_bndbnd_setU _ _ _ (BLeft b)) ?bnd_simp//=.
  rewrite [in RHS](@itv_bndbnd_setU _ _ _ (BRight b) (BRight c)) ?bnd_simp//=.
  rewrite -setUA (setUA `[b, b]) setUid -itv_bndbnd_setU ?bnd_simp//.
  by rewrite -itv_bndbnd_setU// bnd_simp ltW.
apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b c)).
  apply: subspace_eq_continuous cont1.
  by move=> /=r rab; rewrite /from_subspace /patch rab.
have : {in `[b, c], g =1 patch g `[a, b] f }.
  move=> r rab.
  rewrite /patch; case: ifPn => [xab|xabnot//].
  suff -> : r = b by rewrite matchb.
  apply: le_anti.
  by move: rab xab; rewrite 2!inE/= => /itvP -> /itvP ->.
by move/subspace_eq_continuous; exact.
Qed.

End continuous_patch.

Lemma norm_rowmx {K : rcfType} {m n1 n2}
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
rewrite /Num.norm/= !mx_normrE; apply: bigmax_le.
  by rewrite -mulrA mulr_ge0// mulr_ge0//; apply/le_trans/(le_bigmax _ _ (ord0, ord0)).
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
move=> /= df1; apply: differentiable_comp => //.
exact: differentiable_rsubmx.
Qed.

Lemma differentiable_lsubmx_comp {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => lsubmx (f x)) t.
Proof.
move=> /= df1; apply: differentiable_comp => //.
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

(* NB: not used *)
Section gradient.

Definition jacobian1 {R : numFieldType} n (f : 'rV[R]_n -> R)
    : 'rV_n -> 'cV_n :=
  jacobian (scalar_mx \o f).

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
