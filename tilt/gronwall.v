From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  poly archimedean generic_quotient ring_quotient interval_inference
  ring_tactic field_tactic.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets
  contra functions reals topology prodnormedzmodule tvs normedtype landau
  ereal sequences exp derive numfun measure realfun measurable_realfun
  lebesgue_measure lebesgue_integral ftc.
Require Import tilt_analysis.

(**md**************************************************************************)
(* # Gronwall's lemma                                                         *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Section gronwall.
Context {R : realType} (a b : R) (ab : a < b) (lambda : R -> R) (mu y : R -> R).
Hypotheses (lambda_cont : {within `[a, b], continuous lambda})
           (mu_cont : {within `[a, b], continuous mu})
           (mu_ge0 : forall x, x \in `[a, b] -> 0 <= mu x)
           (y_cont : {within `[a, b], continuous y}).

Let lm := @lebesgue_measure R.

Import MeasurableR.

Lemma solve_diff_equa (z f : R -> R) : z a = 0 ->
  {within `[a, b], continuous f} ->
  {within `[a, b], continuous z} ->
  {in `]a, b[%R, forall x, derivable z x 1} ->
  (forall t, t \in `]a, b[%R -> 'D_1 z t = mu t * z t + f t) ->
  let phi t s := expR (\int[lm]_(tau in `[s, t]) mu tau) in
  forall t, t \in `[a, b]%R ->
    z t = \int[lm]_(s in `[a, t]) (phi t s * f s).
Proof.
move=> za0 cf contz derivable_z eqn phi t tab.
have ? : measurable_fun `]a, t[ f.
  apply: open_continuous_measurable_fun => //.
  rewrite -continuous_open_subspace//.
  apply: continuous_subspaceW cf.
  by apply: subset_itv; rewrite bnd_simp// (itvP tab).
have ? : measurable_fun `]a, t[ (phi t).
  apply/measurableT_comp => //=.
  apply: subspace_continuous_measurable_fun => //.
  apply: (@continuous_subspaceW _ _ _ `[a, t]) => //.
    exact: subset_itv_oo_cc.
  apply: parameterized_integralN_continuous.
    by rewrite (itvP tab).
  apply: continuous_subspaceW mu_cont.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
rewrite /Rintegral integral_itvbb_itvoo//=.
  exact/measurable_EFinP/measurable_funM.
have {}eqn : forall t : R, t \in `]a, b[%R ->
    ('D_1 z t - mu t * z t) * (phi t a)^-1 = f t * (phi t a)^-1.
  move=> x xab.
  by rewrite eqn// addrAC subrr add0r.
have derivable_int_mu u : u \in `]a, b[%R ->
    derivable (fun x => \int[lm]_(tau in `[a, x]) mu tau) u 1.
  move=> uab.
  apply: (@continuous_FTC1 _ mu (BLeft a) u b _ _ _ _).1 => /=.
  - by move: uab; rewrite inE => /itvP ->.
  - by apply: continuous_compact_integrable mu_cont; exact: segment_compact.
  - by rewrite lte_fin; move: uab; rewrite inE => /itvP ->.
  - by move: uab; rewrite inE; exact: within_continuous_continuous.
have derivablephiV u : u \in `]a, b[%R -> derivable (fun x => (phi x a)^-1) u 1.
  move=> uab.
  apply: derivableV => //; first by rewrite expR_eq0.
  apply: diff_derivable. (* TODO: lemma derivable_comp *)
  apply: differentiable_comp => /=; last first.
    exact/derivable1_diffP/derivable_expR.
  exact/derivable1_diffP/derivable_int_mu.
have H u : u \in `]a, b[%R ->
  ('D_1 z u - mu u * z u) * (phi u a)^-1 =
  'D_1 (fun t0 => z t0 * (phi t0 a)^-1) u.
  move=> uab/=.
  rewrite [in RHS]deriveM//=.
    exact: derivable_z.
    exact: derivablephiV.
  rewrite [in RHS]addrC.
  rewrite [in LHS]mulrBl [X in X - _]mulrC; congr (_ + _).
  rewrite mulrAC mulrC -mulrN; congr (_ * _).
  rewrite [X in 'D_1 X u](_ : _ =
    (fun x => expR (- \int[lm]_(tau in `[a, x]) mu tau))).
    by apply/funext => w; rewrite expRN.
  rewrite -derive1E derive1_comp//.
    exact/derivableN/derivable_int_mu.
  rewrite derive1E derive1_comp//; first exact: derivable_int_mu.
  rewrite derive1N// derive1_id mulN1r/=.
  rewrite (@continuous_FTC1 _ _ (BLeft a) _ b _ _ _ _).2 //=.
  - by move: uab; rewrite inE => /itvP ->.
  - by apply: continuous_compact_integrable mu_cont; exact: segment_compact.
  - by rewrite lte_fin; move: uab; rewrite inE => /itvP ->.
  - by move: uab; rewrite inE; exact: within_continuous_continuous.
  rewrite -mulNr [in RHS]mulrC; congr (_ * _).
  by rewrite -expRN -[in LHS]derive_expR.
have {}eqn u : u \in `]a, b[%R ->
    'D_1 (fun t0 => z t0 / phi t0 a) u = f u / phi u a.
  move=> uab.
  rewrite -eqn// deriveM/=.
  + exact: derivable_z.
  + exact: derivablephiV.
  rewrite [in RHS]mulrBl.
  rewrite [in LHS]addrC [X in X + _ = _]mulrC; congr (_ + _).
  rewrite -[in RHS]mulrA [in RHS]mulrCA -[in RHS]mulrN; congr (_ * _).
  rewrite [X in 'D_1 X u](_ : _ =
      (fun x => expR (- \int[lm]_(tau in `[a, x]) mu tau))).
    by apply/funext => w; rewrite expRN.
  rewrite -derive1E derive1_comp//; first exact/derivableN/derivable_int_mu.
  have [tau1 tau2] : derivable (fun x => \int[lm]_(t0 in `[a, x]) mu t0) u 1 /\
      (fun x => \int[lm]_(t0 in `[a, x]) mu t0)^`() u = mu u.
    apply: (@continuous_FTC1 _ mu (BLeft a) u b).
    + by rewrite inE in uab; rewrite (itvP uab).
    + by apply: continuous_compact_integrable => //; exact: segment_compact.
    + by rewrite inE in uab; rewrite /= lte_fin (itvP uab).
      move/continuous_within_itvP : mu_cont => /(_ ab)[+ _ _].
      by apply; rewrite inE in uab.
    + rewrite derive1N//= derive1E tau2 mulrN; congr (- _).
      rewrite mulrC; congr (_ * _).
      by rewrite /phi -expRN -[in RHS]derive_expR.
suff: z t / phi t a =
     fine (\int[lm]_(z0 in `]a, t[) (phi t z0 * f z0)%:E) / phi t a.
  move=> /(congr1 (fun x => x * phi t a)).
  by rewrite -!mulrA mulVf ?mulr1// gt_eqF// expR_gt0.
have ? : {in `]a, t[, continuous (fun x0 : R => (phi x0 a)^-1)}.
  rewrite -continuous_open_subspace//.
  apply: derivable_within_continuous => /= x xat.
  apply: derivablephiV.
  rewrite inE.
  by apply: subset_itvl xat; rewrite bnd_simp (itvP tab).
have ? : measurable_fun `]a, t[ (fun x : R => (phi x a)^-1).
  exact: open_continuous_measurable_fun.
have cphi : {within `[a, t], continuous phi^~ a}.
  apply: (@within_continuous_comp _ _ _ _ _ expR) => /=.
    by move=> x _; exact: continuous_expR.
  apply: parameterized_integral_continuous.
    by rewrite (itvP tab).
  apply: continuous_compact_integrable; first exact: segment_compact.
  apply: continuous_subspaceW mu_cont.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
transitivity (\int[lm]_(z0 in `]a, t[)
    'D_1 (fun t0 => z t0 / phi t0 a) z0) => /=.
  have mzphi : measurable_fun `]a, t[(fun x => ('D_1 (fun t0 : R => z t0 / phi t0 a) x)).
    apply/measurable_fun_eqP.
      move=> x xat; rewrite eqn.
      by rewrite inE in xat; rewrite inE; apply: subset_itvl xat; rewrite bnd_simp (itvP tab).
      reflexivity.
    rewrite /=.
    exact: measurable_funM.
  rewrite /Rintegral integral_itvob_itvcb//=.
    exact/measurable_EFinP.
  rewrite /Rintegral integral_itvbo_itvbc//=.
    apply/measurable_EFinP.
    exact/measurable_fun_itvob_itvcbP.
  rewrite (_ : integral _ _ _ = (\int[lebesgue_measure]_(x in `[a, t]) ((f x / phi x a))%:E)%E).
    rewrite integral_itvbb_itvoo//=.
      by apply/measurable_EFinP.
    rewrite [RHS]integral_itvbb_itvoo//=.
      apply/measurable_EFinP => //.
      by apply/measurable_funM.
    apply: eq_integral => x xat/=.
    rewrite eqn//.
    by rewrite inE in xat; rewrite inE; apply: subset_itvl xat; rewrite bnd_simp (itvP tab).
  have [<-|ta] := eqVneq a t.
    by rewrite za0 mul0r set_itv1 integral_set1.
  have {}tab : t \in `]a, b]%R.
    rewrite in_itv/= lt_neqAle ta/=.
    by rewrite in_itv in tab.
  rewrite (@continuous_FTC2 _ _ (fun t0 : R => z t0 / phi t0 a)).
    by rewrite (itvP tab).
    rewrite /=.
    apply: within_continuousM => //.
    apply: continuous_subspaceW cf.
    by apply: subset_itvl; rewrite bnd_simp (itvP tab).
    apply: (@within_continuous_comp _ _ _ _ (phi ^~ a) (fun x => x^-1)).
      move=> /= x.
      rewrite inE/= => -[r rat <-].
      apply: inv_continuous.
      by rewrite gt_eqF// expR_gt0.
    exact: cphi.
    split => /=.
    + move=> x xat.
      apply: derivableM.
        apply: derivable_z.
        by rewrite inE; apply: subset_itvl xat; rewrite bnd_simp (itvP tab).
      apply: derivablephiV => //.
      by rewrite inE; apply: subset_itvl xat; rewrite bnd_simp (itvP tab).
    + apply: cvgM.
        by move/continuous_within_itvP : contz => /(_ ab)[].
      apply: cvgV.
        by rewrite gt_eqF// expR_gt0.
      move/continuous_within_itvP : cphi => /(_ _)[].
        by rewrite (itvP tab).
      move=> _ + _.
      exact.
    + have {}contz : {within `[a, t], continuous z}.
        apply: continuous_subspaceW contz.
        by apply: subset_itvl; rewrite bnd_simp (itvP tab).
      apply: cvgM.
        move/continuous_within_itvP : contz => /(_ _)[]; last by [].
        by rewrite (itvP tab).
      apply: cvgV.
        by rewrite gt_eqF// expR_gt0.
      move/continuous_within_itvP : cphi => /(_ _)[].
        by rewrite (itvP tab).
      by [].
  move=> u uat.
  rewrite derive1E eqn//.
  by rewrite inE; apply: subset_itvl uat; rewrite bnd_simp (itvP tab).
  by rewrite {3}/phi set_itv1 Rintegral_set1 expR0 divr1 za0 sube0/=.
transitivity (\int[lm]_(z0 in `]a, t[) ((phi t z0 * f z0) / phi t a)); last first.
  rewrite RintegralZr//=.
  apply: (@integrableS _ _ _ lebesgue_measure (`[a, t]%classic)) => //=.
    exact: subset_itv_oo_cc.
  apply: continuous_compact_integrable; first exact: segment_compact.
  apply: within_continuousM.
    apply: within_continuous_comp.
      by move=> x _; exact: continuous_expR.
   apply: parameterized_integralN_continuous.
    by rewrite (itvP tab).
  apply: continuous_subspaceW mu_cont.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
  apply: continuous_subspaceW cf.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
apply: eq_Rintegral => u uat.
rewrite eqn.
  rewrite 2!inE in uat *.
  by apply: subset_itvl uat; rewrite bnd_simp (itvP tab).
rewrite mulrAC mulrC; congr (_ * _).
rewrite /phi -expRB -expRN; congr expR.
rewrite -opprB; congr (- _).
apply/esym/eqP; rewrite subr_eq.
rewrite [in X in _ + X]/Rintegral -integral_itvob_itvcb//=.
  apply/measurable_EFinP.
  apply/measurable_fun_itvbo_itvbcP.
  apply: subspace_continuous_measurable_fun => //.
  apply: continuous_subspaceW mu_cont.
  apply: subset_itv; rewrite bnd_simp//.
  by move: uat; rewrite inE => /itvP ->.
  by rewrite (itvP tab).
rewrite -[X in _ + X]/(Rintegral lm _ _) -Rintegral_setU//.
- apply: continuous_compact_integrable => //.
  + rewrite inE in uat.
    rewrite -itv_bndbnd_setU// ?bnd_simp ?(itvP uat)//.
    exact: segment_compact.
  + rewrite inE in uat.
    rewrite -itv_bndbnd_setU// ?bnd_simp ?(itvP uat)//.
    apply: continuous_subspaceW mu_cont.
    by apply: subset_itvl; rewrite bnd_simp (itvP tab).
  + apply: lt_disjoint => v w/=.
    rewrite !in_itv/= => /andP[av vu] /andP[uw wt].
    by rewrite (le_lt_trans vu).
- rewrite inE in uat.
  by rewrite -itv_bndbnd_setU// ?bnd_simp// (itvP uat).
Qed.

Lemma gronwall :
  (forall t, t \in `[a, b] ->
    y t <= lambda t + \int[lm]_(s in `[a, t]) (mu s * y s)) ->
  forall t, t \in `[a, b] ->
    y t <= lambda t +
      \int[lm]_(s in `[a, t])
        (lambda s * mu s * expR (\int[lm]_(tau in `[s, t]) mu tau)).
Proof.
move=> lambdamuy t /[!inE] tab.
pose z t := \int[lm]_(s in `[a, t]) (mu s * y s).
pose v t := z t + lambda t - y t.
have v_ge0 : forall x, x \in `]a, b[ -> 0 <= v x.
  move=> x xab.
  rewrite /v subr_ge0 (le_trans (lambdamuy _ _))//.
    rewrite inE.
    move: xab.
    rewrite inE.
    exact: subset_itv_oo_cc.
  by rewrite addrC lerD2l.
have FTC1z : forall x, x \in `]a, b[%R ->
    derivable
      (fun x0 => \int[lm]_(t0 in `[a, x0]) (mu t0 * y t0)) x 1 /\
    (fun x0 => \int[lm]_(t0 in `[a, x0]) (mu t0 * y t0))^`() x =
  mu x * y x.
  move=> x xab.
  apply: (@continuous_FTC1_closed _ (fun s => mu s * y s) a x b _ _ _).
  by move: xab; rewrite inE => /itvP ->.
  apply: continuous_compact_integrable.
  exact: segment_compact.
  exact: within_continuousM.
  by move: xab; rewrite inE => /itvP ->.
  by apply: continuousM; exact: (@within_continuous_continuous _ _ _ a b).
have derivez : forall x, x \in `]a, b[%R ->
    derive z x 1 = mu x * z x + mu x * lambda x - mu x * v x.
  move=> x xab.
  rewrite -derive1E.
  rewrite (FTC1z _ _).2//.
  rewrite /v.
  by field.
pose phi (t s : R) := expR (\int[lm]_(tau in `[s, t]) mu tau).
have za0 : z a = 0 by rewrite /z set_itv1// Rintegral_set1.
have contz : {within `[a, b], continuous z}.
  apply: parameterized_integral_continuous => /=.
    exact: ltW.
  apply: continuous_compact_integrable; first exact: segment_compact.
  by apply: within_continuousM => //=.
have contv : {within `[a, b], continuous v}.
  apply: within_continuousB => //=.
  exact: within_continuousD.
have contmu : {within `[a, t], continuous mu}.
  apply: continuous_subspaceW mu_cont.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
have contphi : {within `[a, t], continuous phi t}.
  apply: (@within_continuous_comp _ _ _ _ _ expR) => /=.
    by move=> x _; exact: continuous_expR.
  apply: parameterized_integralN_continuous => //.
  by rewrite (itvP tab).
have zE : forall x, x \in `[a, b]%R ->
    z x = \int[lm]_(s in `[a, x]) (phi x s * (mu s * lambda s - mu s * v s)).
  move=> x.
  rewrite in_itv/= => /andP[].
  rewrite le_eqVlt => /predU1P[<- _|ax xb].
    by rewrite za0 set_itv1 Rintegral_set1.
  apply: solve_diff_equa => //=.
  - apply: within_continuousB => /=.
      by apply: within_continuousM => //=.
    by apply: within_continuousM => //=.
  - move=> u uab.
    by apply: (FTC1z _ _).1.
  - by move=> u uab; rewrite derivez// addrA.
  - by rewrite in_itv/= (ltW ax) xb.
have phimuv : 0 <= \int[lm]_(s in `[a, t]) (phi t s * mu s * v s).
  rewrite /Rintegral integral_itvbb_itvoo//=.
    apply/measurable_EFinP => /=; apply: measurable_funM => //=.
      apply: measurable_funM => //=.
      apply/measurable_fun_itvbo_itvbcP.
      apply/measurable_fun_itvob_itvcbP.
      exact: subspace_continuous_measurable_fun.
    apply: subspace_continuous_measurable_fun => //.
    apply: continuous_subspaceW contmu.
    apply: subset_itv; rewrite bnd_simp//.
    apply: subspace_continuous_measurable_fun => //.
    apply: continuous_subspaceW contv.
    by apply: subset_itv; rewrite bnd_simp// (itvP tab).
  apply: Rintegral_ge0 => //= u uab.
  rewrite -mulrA mulr_ge0// ?expR_ge0// mulr_ge0 ?v_ge0//.
    by rewrite mu_ge0// inE; apply: subset_itv uab; rewrite bnd_simp// (itvP tab).
  rewrite inE.
  by apply: subset_itvl uab; rewrite bnd_simp (itvP tab).
rewrite (le_trans (lambdamuy _ _))// 1?inE// lerD2l -/(z t).
rewrite zE//.
apply: (@le_trans _ _ (\int[lm]_(s in `[a, t]) (phi t s * mu s * lambda s)
                   - \int[lm]_(s in `[a, t]) (phi t s * mu s * v s))).
  rewrite -RintegralB//=.
    apply: continuous_compact_integrable => /=; first exact: segment_compact.
    apply: within_continuousM => /=.
      apply: within_continuousM => /=.
        apply: (within_continuous_comp _ _ expR).
          by move=> x _; exact: continuous_expR.
        apply: parameterized_integralN_continuous => //.
        by rewrite (itvP tab).
      apply: continuous_subspaceW mu_cont.
      by apply: subset_itvl; rewrite bnd_simp (itvP tab).
    apply: continuous_subspaceW lambda_cont.
    by apply: subset_itvl; rewrite bnd_simp (itvP tab).
  apply: continuous_compact_integrable.
    exact: segment_compact.
  apply: within_continuousM => /=.
    by apply: within_continuousM => //=.
  apply: continuous_subspaceW contv.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
  apply: le_Rintegral => //=.
    apply: continuous_compact_integrable; first exact: segment_compact.
    apply: within_continuousM => //=.
    apply: within_continuousB => /=.
      apply: within_continuousM => //=.
      apply: continuous_subspaceW lambda_cont.
      by apply: subset_itvl; rewrite bnd_simp (itvP tab).
    apply: within_continuousM => //=.
    apply: continuous_subspaceW contv.
    by apply: subset_itvl; rewrite bnd_simp (itvP tab).
    apply: continuous_compact_integrable; first exact: segment_compact.
    apply: within_continuousB => /=.
      apply: within_continuousM => //=.
        by apply: within_continuousM => //=.
      apply: continuous_subspaceW lambda_cont.
      by apply: subset_itvl; rewrite bnd_simp (itvP tab).
    apply: within_continuousM => //=.
      exact: within_continuousM.
    apply: continuous_subspaceW contv.
    by apply: subset_itvl; rewrite bnd_simp (itvP tab).
  move=> u uat.
  rewrite mulrBr.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by field.
rewrite lerBlDl.
rewrite ler_wpDl//.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
apply: eq_Rintegral => //= u uat.
rewrite -/(phi t u).
by field.
Qed.

End gronwall.
