From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  interval_inference poly archimedean generic_quotient ring_quotient.
From mathcomp Require Import unstable.
From mathcomp Require Import boolp classical_sets contra functions reals.
From mathcomp Require Import topology prodnormedzmodule tvs normedtype.
From mathcomp Require Import landau ereal sequences derive numfun measure.
From mathcomp Require Import realfun measurable_realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc.
Require Import tilt_mathcomp tilt_analysis vector_integral ode_common
  ode_contseg.

(**md**************************************************************************)
(*                                                                            *)
(* # Contraction property of the Picard operator                              *)
(*                                                                            *)
(* `sup_ODE`                                                                  *)
(* : sup {phi t u0 | t \in [a, b]}                                            *)
(*                                                                            *)
(* `safe_dist phi a b u0 r k rho`                                             *)
(* : safe distance for the forward version of the Cauchy-Lipschitz theorem    *)
(*                                                                            *)
(* `@img_cball R n f a b k u0 r k0 rho`                                       *)
(* : set of functions of type `` `C([a, b] U) `` s.t.                         *)
(* : ``f @` `[a, a + safe_dist] `<=` closed_ball u0 r``                       *)
(*                                                                            *)
(* `picard_fun_subdef phi a b u0 r g gabB`                                    *)
(* : `` fun t => u0 + \vint_(x in `[a, t]) phi x (g x) ``                     *)
(* : defined as a continuous function from `` `[a, b] `` to `'rV_n`           *)
(* : morally, takes a function g and returns a function g                     *)
(* : gabB is a proof that `` g @` `[a, b] `<=` closed_ball u0 r ``            *)
(*                                                                            *)
(* `picard_fun cont1 lip2 g`                                                  *)
(* : same as picard_fun_subdef when g @` `[a, b] `<=` closed_ball u0 r and    *)
(* : cst 0 o.w.                                                               *)
(*                                                                            *)
(* `picard`                                                                   *)
(* : similar to picard_fun as a function from/to the quotient of functions    *)
(* : continuous over `[a, b]                                                  *)
(* : more precisely, function of type {fun img_cball >-> img_cball}           *)
(*                                                                            *)
(* `picard_fix`                                                               *)
(* : fixpoint of the integral equation defined by picard                      *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

(* TODO: move *) (* NB: not useful any more?! *)
(*Definition measure_rV_display : measure_display -> measure_display.
Proof. exact. Qed.

Section measurable_rV.
Context {d} {T : sigmaRingType d} (n : nat).

Let coors : 'I_n -> 'rV[T]_n -> T := fun i x => x 0 i.

Let rV_set0 : g_sigma_preimage coors set0.
Proof. exact: sigma_algebra0. Qed.

Let rV_setC A : g_sigma_preimage coors A -> g_sigma_preimage coors (~` A).
Proof. exact: sigma_algebraC. Qed.

Let rV_bigcup (F : _^nat) : (forall i, g_sigma_preimage coors (F i)) ->
  g_sigma_preimage coors (\bigcup_i (F i)).
Proof. exact: sigma_algebra_bigcup. Qed.

HB.instance Definition _ := @isMeasurable.Build (measure_rV_display d)
  'rV[T]_n (g_sigma_preimage coors) rV_set0 rV_setC rV_bigcup.

End measurable_rV.*)

HB.lock Definition sup_ODE {R : realType} {n : nat}
  (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R) (u0 : U)
  : R := sup [set `|phi t u0| | t in `[a, b]].
Canonical sup_ODE_unlockable := Unlockable sup_ODE.unlock.

Section sup_ODE.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num : set U.

Lemma sup_ODE_ge0 : 0 <= sup_ODE phi a b u0.
Proof. by rewrite unlock/= /sup_ODE sup_ge0//= => x [y _ <-]. Qed.

Hypothesis cont1 : {in B, forall y : U, {within `[a, b], continuous phi^~ y}}.

Lemma normr_phi_sup_ODE x : x \in `[a, b]%R ->
  `|phi x u0| <= sup_ODE phi a b u0.
Proof.
move=> xab.
rewrite unlock/= ub_le_sup//.
  have [M [Mb1 Mb2]] : bounded_set [set `|phi t u0| | t in `[a,b]].
    apply/compact_bounded/continuous_compact; last exact: segment_compact.
    have [ab|] := ltP a b; last first.
      rewrite le_eqVlt => /predU1P[ab|ab].
        rewrite [X in {within X, continuous _}](_ : _ = [set a]).
          by rewrite ab set_itv1.
        exact: continuous_subspace1.
      rewrite set_itv_ge// ?bnd_simp -?ltNge//.
      exact: continuous_subspace0.
    apply: within_continuous_comp_norm.
    by apply cont1;rewrite inE; exact: closed_ballxx.
  exists (M + 1) => _ [x0 x0ab] <- /=.
  rewrite -normr_id.
  apply Mb2.
    by rewrite ltrDl.
  by exists x0.
by exists x.
Qed.

End sup_ODE.

Section sup_ODE_lemmas.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (u0 : U).

Lemma sup_ODES a b c d : {within `[a, b], continuous (phi ^~ u0)} ->
  a <= b -> `[c, d] `<=` `[a, b] ->
  sup_ODE phi c d u0 <= sup_ODE phi a b u0.
Proof.
move=> cf ab cdab.
rewrite unlock/=.
have [cd|dc] := leP c d.
  apply: sup_le => //.
  - move=> _/= [r rcd <-].
    rewrite /down/=.
    exists `|phi r u0|; split => //.
    by exists r => //; exact: cdab.
  - exists `|phi c u0| => /=.
    by exists c => //; rewrite bound_itvE.
  - split.
      exists `|phi a u0| => /=.
      by exists a => //; rewrite bound_itvE.
    have : {within `[a, b], continuous fun t : R => `|phi t u0|}.
      exact: within_continuous_comp_norm.
    move=> /(EVT_max ab)[e eab Hmax].
    exists (`|phi e u0|) => x/= [r rab <-].
    exact: Hmax.
rewrite set_itv_ge ?bnd_simp/= -?ltNge// image_set0 sup0.
by apply: sup_ge0 => x/= [y _ <-//].
Qed.

End sup_ODE_lemmas.

HB.lock Definition safe_dist {R : realType} {n} (U := 'rV[R]_n)
    (phi : R -> U -> U) (a b : R) (u0 : U) (r k rho : R) :=
  Num.min (b - a)
 (Num.min (r / (k * r + sup_ODE phi a b u0))
          (rho / k)).
Canonical safe_dist_unlockable := Unlockable safe_dist.unlock.

Section safe_dist.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r k rho : R).

Local Notation safe_dist := (safe_dist phi a b u0 r k rho).
Local Notation sup_ODE := (sup_ODE phi a b u0).

Lemma safe_dist_itv : safe_dist <= b - a.
Proof. by rewrite unlock/= ge_min lexx. Qed.

Lemma safe_dist_le_sup_ODEV : safe_dist <= r / (k * r + sup_ODE).
Proof. by rewrite unlock/= 2!ge_min mulrC lexx/= orbT. Qed.

Lemma safe_dist_le_rho : 0 < k -> k * safe_dist <= rho.
Proof.
by move=> k0; rewrite mulrC -ler_pdivlMr// unlock/= !ge_min lexx !orbT.
Qed.

Lemma safe_dist_ge0 : a <= b -> 0 <= k -> 0 <= r -> 0 <= rho -> 0 <= safe_dist.
Proof.
move=> ab k0 r0 rho0.
rewrite unlock/= le_min subr_ge0 ab/= le_min mulr_ge0//=; last first.
  by rewrite divr_ge0.
by rewrite invr_ge0// addr_ge0 ?sup_ODE_ge0// mulr_ge0.
Qed.

Lemma leDl_safe_dist : a <= b -> 0 <= k -> 0 <= r -> 0 <= rho ->
  a <= a + safe_dist.
Proof. by move=> ab k0 r0 rho0; rewrite lerDl safe_dist_ge0. Qed.

Lemma safe_dist_gt0 : a < b -> 0 < k -> 0 < r -> 0 < rho -> 0 < safe_dist.
Proof.
move=> ab k0 r0 rho0.
rewrite unlock/= lt_min subr_gt0 ab/= lt_min mulr_gt0 ?divr_gt0//.
by rewrite invr_gt0// ltr_wpDr ?sup_ODE_ge0// mulr_gt0.
Qed.

Lemma ltDl_safe_dist : a < b -> 0 < k -> 0 < r -> 0 < rho -> a < a + safe_dist.
Proof. by move=> ab k0 r0 rho0; rewrite ltrDl// safe_dist_gt0. Qed.

End safe_dist.

Lemma safe_dist_rho_le {R : realType} {n} phi (a b : R) (u0 : 'rV[R]_n) r k
    rho rho' : 0 < k -> rho <= rho' ->
  safe_dist phi a b u0 r k rho <= safe_dist phi a b u0 r k rho'.
Proof.
move => k0 rhorho'.
rewrite unlock/= !le_min !ge_min !lexx /= !orbT /=.
by rewrite ler_pdivlMr// ler_pM2r ?rhorho' ?orbT// invr_gt0.
Qed.

Section image_in_closed_ball.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).
Hypothesis k0 : 0 <= k.

Import ContSeg_quot.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).
Local Notation C := (`C([a, a + safe_dist] U)).

Definition img_cball : set C :=
  [set f : C | f @` `[a, a + safe_dist] `<=` closed_ball u0 r%:num].

Lemma img_cball_nonempty : img_cball !=set0.
Proof.
exists (pi C (cst u0)) => _ [y aay] <-.
suff -> : fun_of_quot_contSeg (\pi_C%qT (cst u0)) y = u0.
  exact: closed_ballxx.
rewrite /fun_of_quot_contSeg/=.
have /eqmod_on_itv : (repr (\pi_C%qT (cst u0)) = cst u0 %[mod C])%qT.
  by rewrite reprK.
by apply; rewrite inE.
Qed.

Lemma img_cballE : a <= b -> img_cball =
  @closed_ball R C (pi C (@cst (subspace `[a, a + safe_dist]) U u0)) r%:num.
Proof.
move=> ab; rewrite closed_ballE//.
apply: eq_set => /= f; apply propext; split => h.
- rewrite -(@reprK _ C f).
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite infty_norm_pi pre_infty_norm_le//.
    by exists a => /=; rewrite bound_itvE lerDl// safe_dist_ge0// ltW.
  move=> x adx.
  move /(_ (f x)) : h.
  rewrite closed_ballE//.
  apply.
  exists x => //=.
  by rewrite inE in adx.
- move => _ [x xad] <-.
  rewrite closed_ballE// /closed_ball_ /=.
  have -> : u0 - f x = ((pi C (cst u0)) - f : C) x.
    rewrite -(@reprK _ C f) /GRing.opp /=.
    rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv// inE.
  rewrite -(@reprK _ C f).
  rewrite /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  rewrite eval_mod_on_itv; first by rewrite inE.
  move/mem_set in xad.
  apply: (le_trans (pre_infty_norm_ge _ _  _ xad)).
  + by exists a => /=; rewrite bound_itvE lerDl// safe_dist_ge0.
  + exact: segment_compact.
  + rewrite -infty_norm_pi.
    by rewrite Quotient.pi_add Quotient.pi_opp reprK.
Qed.

Lemma closed_img_cball : a <= b -> closed img_cball.
Proof. by move=> ?; rewrite img_cballE//; exact: closed_ball_closed. Qed.

End image_in_closed_ball.

(* picard contraction starts here *)

Definition picard_fun_subdef {R : realType} n (U := 'rV[R]_n)
    (phi : R -> U -> U) (a b : R) (u0 : U) (r : R) (B := closed_ball u0 r)
    (g : R -> U) (gabB : g @` `[a, b] `<=` B) : R -> U :=
  fun t => u0 + \vint[lebesgue_measure]_(x in `[a, t]) phi x (g x).

(* make picard_fun_subdef a function from [a,b] to the whole set of vector *)
Section picard_fun_subdef_isFun.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}).
Let B : set U := closed_ball u0 r%:num.
Variable g : R -> U.
Hypothesis gabB : g @` `[a, b] `<=` B.

Let set_fun_picard_fun_subdef :
  {homo picard_fun_subdef phi gabB : x / `[a, b] x >-> [set: U] x}.
Proof. by []. Qed.

HB.instance Definition _ := @isFun.Build
  (subspace `[a, b]) _ `[a, b] [set: U] (picard_fun_subdef phi gabB)
    (set_fun_picard_fun_subdef).

End picard_fun_subdef_isFun.

Section picard_fun_subdef_isContinuous.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R).

Let B : set U := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Variable g : R -> U.
Variable cg : {within `[a, b], continuous g}.
Hypothesis gabB : g @` `[a, b] `<=` B.

Lemma within_continuous_picard_fun_subdef :
  {within `[a, b], continuous (picard_fun_subdef phi gabB)}.
Proof.
have [ab|] := ltP a b; last first.
  rewrite le_eqVlt => /predU1P[ab|ab].
    rewrite [X in {within X, continuous _}](_ : _ = [set a]).
      by rewrite ab set_itv1.
    exact: continuous_subspace1.
  by rewrite set_itv_ge// ?bnd_simp -?ltNge//; exact: continuous_subspace0.
apply/within_continuous_coord => i/=.
suff: {within `[a, b],
    continuous (fun t => \int[mu]_(y in `[a, t]) phi y (g y) 0 i)}.
  move=> abf x.
  rewrite (_ : (fun r => picard_fun_subdef phi gabB r 0 i) =
      (fun r => u0 0 i + \int[mu]_(y in `[a, r]) (phi y (g y)) 0 i)).
    by apply/funext=> r0; rewrite mxE rowRintegralE.
  by apply: cvgD; [exact: cvg_cst|exact: abf].
move=> /= x.
apply: (parameterized_integral_continuous (ltW ab)).
apply: continuous_compact_integrable; first exact: segment_compact.
move=> {x}.
apply/within_continuous_coord : i => /=.
exact: (within_continuous_lipschitz cont1 lip2 cg).
Qed.

HB.instance Definition _ := isContinuous.Build (subspace `[a, b]) U
  (picard_fun_subdef phi gabB : subspace _ -> _)
  within_continuous_picard_fun_subdef.

End picard_fun_subdef_isContinuous.

Section picard_fun.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Definition picard_fun (k : R)
    (cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}})
    (lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)})
    (g : R -> U) : R -> U :=
  match pselect (g @` `[a, b] `<=` B) with
  | left gabB => picard_fun_subdef phi gabB
  | _ => cst 0
  end.

End picard_fun.

Section picard_fun_isFun.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).

Lemma cont1_safe_dist :
  {in B, forall y, {within `[a, a + safe_dist], continuous phi ^~ y}}.
Proof.
move=> /= x xB; apply/continuous_subspaceW; last exact: cont1.
by apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
Qed.

Lemma lip2_safe_dist :
  {in `[a, a + safe_dist]%R, forall x, k.-lipschitz_B (phi x)}.
Proof.
move/in_switch : lip2 => lip2'.
apply/in_switch; apply: lipschitzW lip2'.
by apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
Qed.

Local Notation picard_fun := (picard_fun cont1_safe_dist lip2_safe_dist).

Lemma picard_funE g t : g @` `[a, a + safe_dist] `<=` B ->
  picard_fun g t = u0 + \vint[mu]_(x in `[a, t]) phi x (g x).
Proof. by rewrite /picard_fun; case: pselect. Qed.

Lemma picard_fun_init g : g @` `[a, a + safe_dist] `<=` B ->
  picard_fun g a = u0.
Proof.
by move => h; rewrite picard_funE// set_itv1 rowRintegral_set1 addr0.
Qed.

Import ContSeg_quot.

Local Notation C := (`C([a, a + safe_dist] U)).

Let set_fun_picard_fun (g : C) :
  set_fun `[a, a + safe_dist] [set: U] (picard_fun g).
Proof. by []. Qed.

HB.instance Definition _ (g : C) := @isFun.Build
  (subspace `[a, a + safe_dist]) _
    `[a, a + safe_dist] setT (picard_fun g) (set_fun_picard_fun g).

End picard_fun_isFun.

Section picard_fun_isContinuous.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).

Local Notation picard_fun := (picard_fun
  (@cont1_safe_dist R n phi a b u0 r k rho cont1)
  (@lip2_safe_dist R n phi a b u0 r k rho lip2)).

Import ContSeg_quot.

Local Notation C := (`C([a, a + safe_dist] U)).

Let continuous_picard_fun (g : C) :
  {within `[a, a + safe_dist], continuous (picard_fun g)}.
Proof.
have [aaD|] := ltP a (a + safe_dist); last first.
  rewrite le_eqVlt => /predU1P[aaD|aaD].
    rewrite [X in {within X, continuous _}](_ : _ = [set a]).
      by rewrite aaD set_itv1.
    exact: continuous_subspace1.
  rewrite set_itv_ge// ?bnd_simp -?ltNge//.
  exact: continuous_subspace0.
have := @continuous_fun _ _ g.
rewrite /picard_fun; case: pselect => /=.
  move=> z cg.
  apply: (@continuous_fun (subspace `[a, a + safe_dist]) U (picard_fun_subdef phi z)).
  - exact: cont1_safe_dist.
  - exact: lip2_safe_dist.
  - exact: cg.
by move=> _ _; apply: continuous_subspaceT => z; exact: cvg_cst.
Qed.

HB.instance Definition _ (g : C) := @isContinuous.Build _ _
  (picard_fun g : subspace _ -> _) (@continuous_picard_fun g).

Check fun g : C => picard_fun g : continuousSubspaceType _ _.

Check fun g : C => (\pi_C%qT (picard_fun g)) : C.

End picard_fun_isContinuous.

Section integrable_comp.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).

Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).

Import ContSeg_quot.

Local Notation C := (`C([a, a + safe_dist] U)).

Import MeasurableR.

Lemma integrable_comp (F : C) y i : y \in `[a, a + safe_dist]%R ->
  F @` `[a, y] `<=` B ->
  mu.-integrable `[a, y] (EFin \o (fun t => phi t (F t) 0 i)).
Proof.
move=> yaadelta ab0r.
apply: continuous_compact_integrable; first exact: segment_compact.
move: (yaadelta); rewrite in_itv/= => /andP[ay yadelta].
move: i; apply/within_continuous_coord.
apply/within_continuous_lipschitz.
- rewrite -/B => x xB.
  have := @cont1_safe_dist R n phi a b u0 r k rho cont1 _ xB.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- apply/in_switch.
  move/in_switch : (@lip2_safe_dist R n phi a b u0 r k rho lip2).
  by apply/lipschitzW/subset_itvl; rewrite bnd_simp.
- have := @continuous_fun _ _ F.
  by apply/continuous_subspaceW/subset_itvl; rewrite bnd_simp.
- exact: ab0r.
Qed.

End integrable_comp.

Section picard_def.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).

Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).
Local Notation picard_fun := (picard_fun
  (@cont1_safe_dist R n phi a b u0 r k rho cont1)
  (@lip2_safe_dist R n phi a b u0 r k rho lip2)).

Import ContSeg_quot.

Local Notation C := (`C([a, a + safe_dist] U)).

Definition picard (_ : 0 <= k) (f : C) : C := \pi_C%qT (picard_fun f).
End picard_def.

Section picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).

Hypothesis k0 : 0 <= k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).
Local Notation picard_fun := (picard_fun
  (@cont1_safe_dist R n phi a b u0 r k rho cont1)
  (@lip2_safe_dist R n phi a b u0 r k rho lip2)).

Import ContSeg_quot.

Local Notation C := (`C([a, a + safe_dist] U)).

Local Notation img_cball := (@img_cball R n phi a b u0 r k rho).
Local Notation sup_ODE := (sup_ODE phi a b u0).

Import MeasurableR.

Let set_fun_picard : set_fun img_cball img_cball (picard cont1 lip2 k0).
Proof.
move=> F.
rewrite /img_cball/= => invariant _/= [y yaaDelta <-].
rewrite /picard.
apply/closed_ball_coord => //= i.
rewrite closed_ball_itv//=.
rewrite in_itv//=.
rewrite [X in _ <= X <= _](_ : _ = (picard_fun F) y 0 i).
  have /eqmod_on_itv :
      (repr (\pi_C%qT (picard_fun F)) = picard_fun F %[mod C])%qT.
    by rewrite reprK.
  by move=> <- //; rewrite inE.
rewrite /picard_fun; case: pselect => /= abu0r; last by [].
rewrite /picard_fun_subdef /=.
rewrite mxE/=.
rewrite -ler_distl.
rewrite -addrA subrKC.
rewrite rowRintegralE.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  apply: integrable_comp => //.
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move : yaaDelta; rewrite in_itv /= => /andP[].
have integrable2 : mu.-integrable `[a, y] (EFin \o (fun x => phi x (F x) 0 i)).
  apply integrable_comp => //=.
  apply: subset_trans abu0r.
  apply/image_subset/subset_itvl; rewrite bnd_simp.
  by move: yaaDelta; rewrite in_itv /= => /andP[].
have integrable1 : mu.-integrable `[a, y]
    (fun x => `|phi x (F x) 0 i - phi x u0 0 i|%:E + `|phi x u0 0 i|%:E).
  rewrite integrableD//=.
    apply: integrable_norm => /=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinN.
    rewrite integrableN //=.
    apply: continuous_compact_integrable => //=; first exact: segment_compact.
    move: i {integrable2}; apply/within_continuous_coord.
    apply/continuous_subspaceW/(@cont1_safe_dist _ _ _ _ _ _ _ k rho cont1).
      by apply: subset_itvl; rewrite bnd_simp (itvP yaaDelta).
   by rewrite /B inE; exact: closed_ballxx.
  apply: integrable_norm => /=.
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  move: i {integrable2}; apply/within_continuous_coord.
  apply/continuous_subspaceW/(@cont1_safe_dist _ _ _ _ _ _ _ k rho cont1).
    by apply: subset_itvl; rewrite bnd_simp (itvP yaaDelta).
  rewrite /B inE.
  exact: closed_ballxx.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y])
    (`|phi x (F x) 0 i - phi x u0 0 i| + `|phi x u0 0 i|)))//.
  apply: le_Rintegral => //=.
  - exact: integrable_norm.
  - by move=> x xay; rewrite (le_trans _ (ler_normD _ _))// subrK.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * `|F x - u0| + sup_ODE)))//.
  apply: le_Rintegral => //=.
    under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr//=; first exact: bounded_cst.
      apply: integrable_row_mx_norm => //= j.
      under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
      rewrite integrableB//=.
        apply: continuous_compact_integrable => //; first exact: segment_compact.
        move: j; apply/within_continuous_coord/continuous_subspaceW/continuous_fun.
        by apply: subset_itvl; rewrite bnd_simp (itvP yaaDelta).
      apply: measurable_bounded_integrable => //=; last exact: bounded_cst.
      rewrite lebesgue_measure_itv//=.
      by case: ifPn => //=; rewrite -EFinD ltry.
    apply: measurable_bounded_integrable => //=; last exact: bounded_cst.
    rewrite lebesgue_measure_itv //=.
    by case: ifPn => //=; rewrite -EFinD ltry.
  move=> x xay.
  rewrite lerD//.
    have /(lip2_safe_dist lip2) : x \in `[a, a + safe_dist]%R.
      by apply: subset_itvl xay; rewrite bnd_simp (itvP yaaDelta).
    rewrite lipschitz_coord//= => /(_ i (F x, u0)) => /=.
    apply.
    split => /=.
      apply: invariant => /=.
      exists x => //.
      by apply: subset_itvl xay; rewrite bnd_simp (itvP yaaDelta).
    exact: closed_ballxx.
  apply: (@le_trans _ _ `|phi x u0|) => //.
    by rewrite /Num.norm/= mx_normrE /= (le_bigmax _ _ (ord0, i)).
  apply: (@normr_phi_sup_ODE _ _ _ _ _ _ r) => //.
  apply: subset_itvl xay; rewrite bnd_simp.
  move : yaaDelta; rewrite in_itv /= => /andP[_].
  move=> /le_trans; apply.
  by rewrite -lerBrDl safe_dist_itv.
rewrite (@le_trans _ _ (\int[mu]_(x in `[a, y]) (k * r%:num + sup_ODE)))//.
  apply: le_Rintegral => //=.
  - under [x in integrable _ _  x]eq_fun do rewrite EFinD.
    rewrite integrableD //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr //=; first exact: bounded_cst.
      apply: integrable_row_mx_norm => // j /=.
      under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
      rewrite integrableB//=.
        apply continuous_compact_integrable; first exact: segment_compact.
        move: j; apply/within_continuous_coord/continuous_subspaceW/continuous_fun.
        by apply: subset_itvl; rewrite bnd_simp (itvP yaaDelta).
      apply: measurable_bounded_integrable => //=; last exact: bounded_cst.
      rewrite lebesgue_measure_itv//=.
      by case: ifPn => //=; rewrite -EFinD ltry.
    apply: measurable_bounded_integrable => //=; last exact: bounded_cst.
    rewrite lebesgue_measure_itv//=.
    by case: ifPn => //=; rewrite -EFinD ltry.
  - apply: measurable_bounded_integrable => //=; last exact: bounded_cst.
    rewrite lebesgue_measure_itv //=.
    by case: ifPn => //=; rewrite -EFinD ltry.
  - move=> x xay.
    rewrite lerD2r ler_wpM2l//.
    have : B (F x).
      apply: invariant => /=.
      exists x => //.
      move: xay; rewrite !in_itv/= => /andP[] -> /= /le_trans.
      apply.
      by rewrite (itvP yaaDelta).
    by rewrite /B closed_ballE// /closed_ball_/=; rewrite distrC.
rewrite Rintegral_cst//.
rewrite /= (* NB: IMP: to remove a reverse_coercion *).
rewrite lebesgue_measure_itv/=.
rewrite lte_fin.
move: (yaaDelta); rewrite in_itv/= => /andP[+ yadelta].
rewrite le_eqVlt => /predU1P[->|ay].
  by rewrite ltxx/= mulr0.
rewrite (@le_trans _ _ ((k * r%:num + sup_ODE) * safe_dist))//.
  rewrite ler_wpM2l//.
    by rewrite addr_ge0 ?mulr_ge0 ?(ltW k0)// sup_ODE_ge0.
  by rewrite ay//= lerBlDl.
move: k0; rewrite le_eqVlt => /predU1P[<-|].
  rewrite mul0r add0r.
  have := sup_ODE_ge0 phi a b u0.
  rewrite le_eqVlt => /predU1P[<-|sup_ODE_gt0].
    by rewrite mul0r.
  rewrite -ler_pdivlMl//.
  rewrite (le_trans (safe_dist_le_sup_ODEV _ _ _ _ _ _ _))//.
  by rewrite mul0r add0r mulrC.
move=> k_gt0.
rewrite -ler_pdivlMl//.
  by rewrite ltr_pwDl ?mulr_gt0// sup_ODE_ge0.
by rewrite mulrC safe_dist_le_sup_ODEV.
Qed.

Fail Check picard_to_cont : {fun [set: V] >-> [set: V]}.

HB.instance Definition _ :=
  @isFun.Build _ _ _ _ (picard cont1 lip2 k0) set_fun_picard.

Check picard cont1 lip2 k0 : {fun img_cball >-> img_cball}.
(* still, we can't state that it is a contraction for typing reasons *)

Fail Lemma tmp : is_contraction (picard : {fun [set: _] >-> [set: _]}).
About is_contraction.

End picard.

Section is_contraction_picard.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).

Hypothesis ab : a <= b.
Hypothesis k0 : 0 <= k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis rho1 : rho%:num < 1.

Import ContSeg_quot.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).

Notation C := (quot_contSeg a (a + safe_dist) U).
Notation img_cball := (@img_cball _ n phi a b k u0 r rho).

Check @cst (subspace `[a, a + safe_dist]) U u0
  : {fun `[a, a + safe_dist] >-> [set: U]}.

Check @cst (subspace `[a, a + safe_dist]) U u0
  : continuousType (subspace `[a, a + safe_dist]) U.

Local Notation picard := (@picard R n phi a b u0 r k rho cont1 lip2 k0).

Import MeasurableR.

Lemma is_contraction_picard : is_contraction picard.
Proof.
rewrite /is_contraction /contraction.
rewrite /picard /picard_fun /picard_fun_subdef.
exists (NngNum (ge0 rho)); split => //=.
move=> /= [/= x y] [Vrx Vry].
rewrite /picard/=.
rewrite !piE/=.
rewrite infty_norm_pi/=.
rewrite /pre_infty_norm/=.
apply: ge_sup => //=.
  set u := _ \o _; exists (u a) => /=; exists a => //.
  by rewrite in_itv/= lexx leDl_safe_dist// ltW.
move=> _ /= [t tNdd <-].
have tb : t <= b.
  move: tNdd.
  rewrite in_itv/= => /andP[Ndt].
  move=> /le_trans; apply.
  by rewrite -lerBrDl safe_dist_itv.
rewrite /picard_fun/=; case: pselect => //= Hg; case: pselect => [Hg2|//].
rewrite /picard_fun_subdef/=.
rewrite !fctE.
rewrite (addrC u0).
rewrite addrKA.
rewrite [in leLHS]/Num.norm/= mx_normrE.
apply: bigmax_le => //= -[i j] _.
rewrite {i}(ord1 i)/=.
rewrite mxE rowRintegralE mxE rowRintegralE.
have integrable1 : mu.-integrable `[a, t] (EFin \o (fun t => phi t (x t) 0 j)).
  apply: integrable_comp => //=.
  apply: subset_trans Hg; apply: image_subset.
  apply/subset_itvl; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[].
have integrable2 : mu.-integrable `[a, t] (EFin \o (fun t => phi t (y t) 0 j)).
  apply: integrable_comp => //=.
  move=> _ [x0 h] <-.
  apply: Hg2 => /=.
  exists x0 => //.
  apply/subset_itvl/h; rewrite bnd_simp.
  by move: tNdd; rewrite !in_itv/= => /andP[].
rewrite -RintegralB//=.
rewrite (le_trans (le_normr_Rintegral _ _))//=.
  under [x in integrable _ _  x]eq_fun do rewrite EFinB.
  by rewrite integrableB.
have integrable3 : mu.-integrable `[a, t] (fun x0 => `|x x0 - y x0|%:E).
  rewrite /=.
  apply: integrable_row_mx_norm; first exact: measurable_itv.
  move => i.
  under [x in integrable _ _  x]eq_fun do rewrite !mxE EFinB.
  rewrite integrableB//=.
    apply continuous_compact_integrable => //=; first exact: segment_compact.
    move: i; apply/within_continuous_coord/continuous_subspaceW/continuous_fun.
    apply: subset_itvl; rewrite bnd_simp.
    by move: tNdd; rewrite in_itv /= => /andP[].
  apply continuous_compact_integrable => //=; first exact: segment_compact.
  move: i; apply/within_continuous_coord/continuous_subspaceW/continuous_fun.
  apply: subset_itvl; rewrite bnd_simp.
  by move: tNdd; rewrite in_itv /= => /andP[].
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `| x t0 - y t0|))//.
  rewrite (@le_trans _ _ (\int[mu]_(t0 in `[a, t]) (k * `|x t0 - y t0|)))//.
    apply: le_Rintegral => //=.
      apply: integrable_norm => //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinB.
      rewrite integrableB //=.
      under [x in integrable _ _  x]eq_fun do rewrite EFinM.
      rewrite integrableMr//=.
      exact: bounded_cst.
    move=> x0 x0at.
    have : x0 \in `[a, b]%R by apply /subset_itvl/x0at.
    move/lip2.
    rewrite /dominated_by/= => /(_ (x x0, y x0)) /=.
    have Bxy : B (x x0) /\ B (y x0).
      split.
        apply: Vrx => /=.
        exists x0 => //.
        apply/subset_itvl/x0at.
        by rewrite bnd_simp (itvP tNdd).
      apply: Vry => /=.
      exists x0 => //.
      apply/subset_itvl/x0at.
      by rewrite bnd_simp (itvP tNdd).
    move=> /(_ Bxy); apply: le_trans.
    rewrite [in leRHS]/Num.norm/= mx_normrE.
    apply: le_trans; last first.
      by apply: le_bigmax => /=; exact: (0, j).
    by rewrite /= !mxE.
  by rewrite RintegralZl.
rewrite (@le_trans _ _ (k * \int[mu]_(t0 in `[a, t]) `|x - y| ))//.
  rewrite ler_wpM2l//.
  apply: le_Rintegral => //=.
    apply: measurable_bounded_integrable => //=; last exact: bounded_cst.
    rewrite lebesgue_measure_itv //=.
    by case: ifPn => //=; rewrite -EFinD ltry.
  move=> x0 x0at.
  have x0ad : x0 \in `[a, a + safe_dist]%R.
    by apply: subset_itvl x0at; rewrite bnd_simp (itvP tNdd).
  have -> : x x0 - y x0 = (x - y : C) x0.
    apply (@eqmod_on_itv _ _ _ _ (repr x - repr y)) => //.
    by rewrite Quotient.pi_add Quotient.pi_opp !reprK.
  rewrite pre_infty_norm_ge//.
  - by exists a => /=; rewrite bound_itvE// lerDl// safe_dist_ge0// ltW.
  - exact: segment_compact.
  - by rewrite inE.
rewrite (@le_trans _ _ (k * `|x - y| * (t - a)))//.
  rewrite -mulrA ler_wpM2l//.
  rewrite Rintegral_cst// ler_pM//.
  move: tNdd; rewrite in_itv/= => /andP[+ _].
  rewrite le_eqVlt => /predU1P[->|].
    by rewrite set_itv1 lebesgue_measure_set1 subrr lexx.
  by rewrite /= (lebesgue_measure_itv `[a,t]%R) /= lte_fin => ->.
rewrite [leLHS]mulrAC ler_wpM2r//.
have [->|] := eqVneq k 0.
  by rewrite mul0r.
rewrite neq_lt ltNge k0/= => k0'.
move: tNdd; rewrite in_itv/= => /andP[Ndt].
rewrite -lerBlDl -[in X in X -> _](@ler_pM2l _ k)// => /le_trans; apply.
by rewrite safe_dist_le_rho.
Qed.

End is_contraction_picard.
