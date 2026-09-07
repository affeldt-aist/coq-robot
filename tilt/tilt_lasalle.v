From HB Require Import structures.
From mathcomp Require Import boot algebra ring_tactic.
From mathcomp Require Import interval_inference finmap.
From mathcomp Require Import boolp classical_sets functions reals order.
From mathcomp Require Import topology normedtype landau sequences derive realfun.
From mathcomp Require Import matrix_normedtype exp.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.
Require Import lasalle (* to at least get the structure of filters on sets *).
Require Import ode_common ode_local tilt_stability tilt_lyapunov ode_global.

(**md**************************************************************************)
(* # Formalization of [benallegue2023itac] (2/2)                              *)
(*                                                                            *)
(* The main result of this file is to show that all solutions converge to one *)
(* of the two equilibrium points.                                             *)
(*                                                                            *)
(* `sublevel (V : U -> R) (c : R)`                                            *)
(* : [set x : U | V x <= c].                                                  *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [cohen2017itp] C. Cohen, D. Rouhling. A formal proof in Coq of LaSalle’s *)
(* invariance principle. ITP 2017                                             *)
(* - [benallegue2023itac]                                                     *)
(* https://hal.science/hal-04271257v1/file/benallegue2019tac_October_2022.pdf *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.ExtraDef Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

Section sublevel.
Context {R : realType} {n : nat} (U := 'rV[R]_n).

Definition sublevel (V : U -> R) c := [set x : U | V x <= c].

Lemma sublevel_preimage (V : U -> R) c : sublevel V c = V @^-1` [set r | r <= c].
Proof. by []. Qed.

Lemma mem_sublevel_img (V : U -> R) p : sublevel V (V p) p.
Proof. by rewrite /sublevel/=. Qed.

End sublevel.

Section LaSalle_tilt.
Context {K : realType} (U := 'rV[K]_6) (alpha1 gamma : K)
  (phi := Tilt.eqn alpha1 gamma).

Hypotheses (alpha1_gt0 : 0 < alpha1) (gamma_gt0 : 0 < gamma).

Definition sublevelV1 (p : U) :=
  sublevel (Tilt.V1 alpha1 gamma) (Tilt.V1 alpha1 gamma p).

Definition sublevelV1Upsilon1 (p : U) :=
  sublevelV1 p `&` Tilt.Upsilon1.

Lemma mem_sublevelV1Upsilon1 p : Tilt.Upsilon1 p ->
  p \in sublevelV1Upsilon1 p.
Proof.
move=> up; rewrite inE; split => //.
exact: mem_sublevel_img.
Qed.

(* NB: not used *)
Lemma point1_sublevelV1Upsilon1 p : sublevelV1Upsilon1 p Tilt.point1.
Proof.
split => /=; last by have /set_mem := @tilt_point1_in_state_space K.
rewrite /sublevelV1 /sublevel/= /Tilt.point1 /Tilt.V1.
rewrite lsubmx_const rsubmx_const/= !enorm0 !expr0n /= !mul0r add0r.
by rewrite addr_ge0// divr_ge0// ?sqr_ge0 ?mulr_ge0// ltW.
Qed.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

Lemma compact_sublevelV1 p : compact (sublevelV1 p).
Proof.
(* TODO: use something similar to compact_sphere *)
apply: bounded_closed_compact.
- rewrite /= /bounded_near.
  near=> r.
  move=> /= x.
  rewrite /sublevelV1 /sublevel /= /Tilt.V1/=.
  rewrite !addf_div; rewrite ?lt0r_neq0 ?mulr_gt0//.
  rewrite ler_pdivrMr ?mulr_gt0// divrK.
    by rewrite unitfE lt0r_neq0 // ?mulr_gt0.
  rewrite !(mulrC 2) !mulrA -!mulrDl ler_pM2r// => h.
  set c := `| Left p |_e ^+ 2 * gamma + `| Right p |_e ^+ 2 * alpha1.
  have c0 : 0 <= c by rewrite addr_ge0// mulr_ge0 ?sqr_ge0 ?ltW.
  have hL : `| Left x |_e <= Num.sqrt (c / gamma).
    rewrite -(sqr_sqrtr (enorm_ge0 (Left x))).
    rewrite expr2 -sqrtrM ?enorm_ge0//.
    rewrite ler_sqrt ?divr_ge0 ?(ltW gamma_gt0)//.
    rewrite ler_pdivlMr//.
    apply: le_trans h.
    by rewrite -expr2 lerDl mulr_ge0 ?sqr_ge0 ?ltW.
  have hR : `| Right x |_e <= Num.sqrt (c / alpha1).
    rewrite -(sqr_sqrtr (enorm_ge0 (Right x))).
    rewrite expr2 -sqrtrM ?enorm_ge0//.
    rewrite ler_sqrt// ?divr_ge0 ?(ltW alpha1_gt0)//.
    rewrite ler_pdivlMr//.
    apply: le_trans h.
    by rewrite addrC lerDl mulr_ge0// ?sqr_ge0 ?ltW.
  have : `|x| <= `| Left x |_e  + `|Right x|_e.
    rewrite -[in leLHS](@hsubmxK _ 1 3 3 x) (norm_rowmx (Left x)) ge_max.
    by rewrite !(le_trans (mxnorm_enorm_le _))//= ?lerDl ?lerDr ?enorm_ge0.
  move/le_trans; apply.
  exact/(le_trans (lerD hL hR)).
- rewrite /sublevelV1 sublevel_preimage.
  apply: preimage_closed.
    move=> /= x xin.
    exact: (differentiable_continuous (V1_diff _ _ _)).
  exact: closed_le.
Unshelve. all: by end_near. Qed.

Lemma compact_sublevelV1Upsilon1 p : compact (sublevelV1Upsilon1 p).
Proof.
apply: compact_closedI; first exact: compact_sublevelV1.
rewrite Tilt.Upsilon1_preimage.
apply: preimage_closed => // => x xp.
apply: (@continuous_comp _ _ _ (fun x0 : 'rV[K^o]_6 => 'e_2 - Right x0)).
  apply: continuousB.
    exact: cst_continuous.
  exact: continuous_rsubmx.
exact: continuous_enorm.
Qed.

Lemma compact_Upsilon1 : compact (@Tilt.Upsilon1 K).
Proof.
rewrite /Tilt.Upsilon1.
(* TODO: I think we already proved that inside a proof *)
Abort.

Let tilt_solP' y0 : y0 \in Tilt.Upsilon1 ->
  exists2 sol, is_sol_cauchy (fun=> phi) 0 +oo%O y0 sol &
               (h^-1 *: (sol h - sol 0)) @[h --> 0^'+] --> phi (sol 0).
Proof.
move=> y0Upsilon1.
suff [sol [solP2 solP1]] : exists2 sol,
    is_sol_cauchy (fun => phi) 0 +oo%O y0 sol &
    (h^-1 *: (sol (0 + h) - sol 0)) @[h --> 0^'+] --> phi (sol 0).
  move : solP2; under eq_fun do rewrite add0r; move=>solP2.
  by exists sol.
apply: (@compact_global_solution _ _ _ _ _ (sublevelV1Upsilon1 y0)) => /=.
- exact: compact_sublevelV1Upsilon1.
- exact/mem_sublevelV1Upsilon1/set_mem.
- by move=> x; exact: cst_continuous.
- move=> b b0 y1.
  have [r [k y0r]] := @tilt_eqn_locally_lipschitz K alpha1 _ gamma_gt0 y1.
  by exists r, k.
move=> t y' [init [solp cont]] y1 [t0 /= t0t <-].
split; last first.
  apply/(@tilt_state_spaceS  _ alpha1 gamma).
  exists y', t; split; rewrite ?init//=.
  by exists t0.
rewrite /sublevelV1 /sublevel/=.
rewrite -init.
apply: (@V_nincr _ _ t) => /=.
- by move=> t' itvt'; apply solp.
- apply/continuous_subspaceW/cont.
  rewrite closure_itvoo; first by rewrite (itvP t0t).
  by apply: subset_itvl; rewrite bnd_simp.
- exact: V1_diff.
- apply: (@derive_along_V1_le0 _ _ _ _ _ t) => //.
    by rewrite init.
  by move=> t1 t1t; apply/derivable1_diffP; apply solp.
- by rewrite (itvP t0t).
- by rewrite (itvP t0t) lexx.
Qed.

(* NB: this is the first part of the hypotheses to apply LaSalle's invariance principle *)
Lemma tilt_solP : exists2 sol, (forall p, sol p 0 = p) &
  lasalle_solP phi Tilt.Upsilon1 sol.
Proof.
have /choice [sol0 sol0P] : forall y0, exists sol, sol 0 = y0 /\
    (y0 \in Tilt.Upsilon1 -> is_sol_cauchy (fun => phi) 0 +oo%O y0 sol /\
    (h^-1 *: (sol h - sol 0)) @[h --> 0^'+] --> phi (sol 0)).
  move => y0.
  have [|y01] := boolP (y0 \in Tilt.Upsilon1); last by exists (cst y0).
  move/tilt_solP' => [sol [sol0 solp solpr]].
  by exists sol.
set sol := fun y0 t =>
  if t < 0 then 2 *: y0 - sol0 y0 (- t)
  else sol0 y0 t.
exists sol.
  move => p.
  rewrite /sol ltxx.
  by have [+ _] := sol0P p.
move=> /= y /mem_set yp.
split; last first.
  move => ->.
  split => t tp.
    rewrite /sol tp /= ltxx ltrNl oppr0 ltNge ltW ?tp//=.
    suff {1}-> : y 0 = sol0 (y 0) 0 by [].
    by have [-> _] := sol0P (y 0).
  rewrite /sol ltNge tp/=.
  move: tp; rewrite le_eqVlt => /predU1P[<-| tp]; last first.
  - set g := (X in is_derive _ _ X _).
    set df := (X in is_derive _ _ _ X).
    apply: (near_eq_is_derive (f := sol0 (y 0))).
      near=> t0.
      rewrite /g.
      rewrite ltNge.
      suff -> : 0 <= t0 by [].
      by near: t0; exact: lt_le_nbhsr.
    have [_ +] := sol0P (y 0).
    move /(_ yp) => [[_ [+ _]] _].
    move /(_ t).
    by move => h; split; rewrite -?derive1E; apply h; rewrite in_itv/= tp.
  - rewrite /is_sol_cauchy/sol_is_deriv_obnd/= in sol0P.
    have [init [d c]] := ((sol0P (y 0)).2 yp).1.
    set f := sol0 (y 0).
    set F := fun t => if t < 0 then 2 *: y 0 - f (- t) else f t.
    set v := phi (f 0).
    suff cvg : (fun (h : K)  => h^-1 *: (F h - F 0)) @ 0^' --> v.
      apply: DeriveDef.
        apply/cvgP.
        by under eq_fun do rewrite /= addr0 scaler1; exact: cvg.
      apply: cvg_lim => //.
      by under eq_fun do rewrite /= addr0 scaler1; exact: cvg.
    rewrite /F ltxx.
    rewrite [X in X h @[h --> _] --> _](_ : _ = fun h => `|h|^-1 *: (f `|h| - f 0)).
      apply/funext => h.
      case: ifPn => h0.
        rewrite ltr0_norm// invrN scaleNr -scalerN opprD opprK; congr (_ *: _).
        have -> : f 0 = y 0 by apply sol0P.
        by rewrite scaler_nat/= mulr2n -!addrA (addrC (- f (-h)) (y 0)) subrKC.
      by rewrite ger0_norm// leNgt.
    have cvg_right : (h^-1 *: (f h - f 0)) @[h --> 0^'+] --> v.
      by rewrite /f /v; apply sol0P.
    apply/cvgrPdist_lt => /= eps eps0.
    move/cvgrPdist_lt : cvg_right => /(_ _ eps0)[/= e e0 B].
    near=> t0.
    have [lt0|ge0] := ltP t0 0.
    + rewrite ltr0_norm ?oppr_lt0// B ?oppr_gt0//.
      rewrite /ball_/= opprK add0r.
      by near: t0; exact: dnbhs0_lt.
    + rewrite ger0_norm//.
      have gt0 : 0 < t0.
        rewrite lt_neqAle ge0 andbT eq_sym.
        by near: t0; exact: nbhs_dnbhs_neq.
      rewrite B// /ball_/= ball_norm_sym/ball_/=// subr0.
      by near: t0; exact: dnbhs0_lt.
move => is_sol.
suff h : forall t, t >= 0 -> y t = sol0 (y 0) t.
  apply/funext => /= t.
  rewrite /sol; case: ifPn => t0.
    have [+ _] := is_sol.
    move /(_ _ t0) => ->; congr (_ - _).
    by rewrite h// lerNr oppr0 ltW.
  by rewrite h// leNgt.
move=> /= t t0.
have [_ +] := is_sol.
move /(_ _ t0) => h.
move: t0; rewrite le_eqVlt => /predU1P[<-|tp].
  by have [-> _] := sol0P (y 0).
have hs : is_sol_cauchy_oo (fun=> phi) 0 t (sol0 (y 0) 0) (sol0 (y 0)).
  split; first reflexivity.
  split.
    move=> t0 t0t; apply sol0P => //.
    exact: subset_itvl t0t.
  have [_ +] := sol0P (y 0).
  move=> /(_ yp)[_ _ +].
  apply: continuous_subspaceW.
    apply: closureS.
    exact: subset_itvl.
  have [_ [_]]:= ((sol0P (y 0)).2 yp).1.
  exact/continuous_subspaceW/closureS/subset_itvl.
apply: (locally_cauchy_lipschitz_unique _ _ hs) => /=.
- exact: tp.
- split.
    by have [-> _] := sol0P (y 0).
  split.
    move=> t0 t0t; rewrite derive1E.
    by split; apply is_sol; rewrite ltW// (itvP t0t).
  rewrite closure_itvoo//.
  apply: continuous_in_subspaceT => /= t0 t0t.
  apply: differentiable_continuous.
  apply/derivable1_diffP.
  apply is_sol => //.
  by rewrite inE in t0t; rewrite (itvP t0t).
- move=> t0 t00 t0t.
  have [r [k y0r]] := @tilt_eqn_locally_lipschitz K alpha1 _ gamma_gt0 (y t0).
    exists r, k; split => // v vy0r.
    exact: cst_continuous.
- by rewrite bound_itvE ltW.
Unshelve. all: by end_near. Qed.

Let tilt_sol := proj1_sig (cid2 tilt_solP).
Let tilt_sol_spec := proj2_sig (cid2 tilt_solP).

Lemma tilt_sol0 p : tilt_sol p 0 = p.
Proof. by apply tilt_sol_spec. Qed.

Let isSol p : p \in Tilt.Upsilon1 -> sol_is_deriv_c0y (fun=> phi) (tilt_sol p).
Proof.
move=> Kp t; rewrite in_itv/= andbT => t0.
have [/= _ H] : lasalle_is_sol phi (tilt_sol p).
  by apply tilt_sol_spec; rewrite ?tilt_sol0//; exact/set_mem.
split.
  by apply (H _ t0).
by rewrite derive1E; apply H.
Qed.

Let isSol_oo p t : p \in Tilt.Upsilon1 ->
  is_sol_cauchy_oo (fun=> phi) 0 t (tilt_sol p 0) (tilt_sol p).
Proof.
move => ph.
split; first by [].
split.
  split.
    apply isSol => //.
    by apply: subset_itv H; rewrite bnd_simp.
  apply isSol => //.
  by apply: subset_itv H; rewrite bnd_simp.
apply: continuous_in_subspaceT => /= t0 t0p.
apply/differentiable_continuous/derivable1_diffP; apply isSol => //.
suff h : 0 < t.
  move: t0p; rewrite closure_itvoo// inE/=.
  by apply: subset_itvl; rewrite bnd_simp.
rewrite ltNge; apply: contraPN t0p => t_le0.
by rewrite set_itv_ge ?closure0 ?in_set0 // bnd_simp -leNgt.
Qed.

Lemma invariant_sublevelUpsilon1 p :
  lasalle.is_invariant tilt_sol (sublevelV1Upsilon1 p).
Proof.
rewrite /is_invariant/= => /= x.
rewrite /sublevelV1Upsilon1/= =>  -[Vx Kx] t t0.
split; last first.
  apply/(@tilt_state_spaceS  _ alpha1 gamma).
  exists (tilt_sol x), (t + 1) => /=. (* use large enough time *)
  split.
  - by rewrite tilt_sol0; exact/mem_set.
  - by apply isSol_oo;rewrite inE.
  - exists t => //.
    by rewrite /= in_itv/=t0/=ltrDl.
move/mem_set : (Kx) => /isSol solA.
rewrite /sublevelV1/= /sublevel/=.
rewrite (le_trans _ Vx)//.
rewrite -[in leRHS](@tilt_sol0 x).
apply : (V_nincr (D := t + 1)).
- move=> t' t'0t1.
  apply isSol => //.
    by rewrite inE.
  by rewrite in_itv/= andbT (itvP t'0t1).
- apply: continuous_in_subspaceT => t' t't1.
  apply/differentiable_continuous/derivable1_diffP.
  apply solA.
  by move: t't1; rewrite inE; apply: subset_itvl; rewrite bnd_simp.
- exact: V1_diff.
- move=> t1 tt1; apply: (@derive_along_V1_le0 _ _ _ _ _ (t + 1)) => /=.
  + by [].
  + by [].
  + by rewrite tilt_sol0 inE.
  + by apply isSol_oo; rewrite inE.
  + move=> t2 t2t1.
    apply/derivable1_diffP.
    apply solA.
    by rewrite in_itv/= andbT (itvP t2t1).
- by [].
- by rewrite ltrDl.
- by rewrite lexx.
Qed.

(* NB: this is the first part of the hypotheses to apply LaSalle's invariance principle,
   namely continuity in initial value *)
Lemma tilt_sol_cont p (t : K) : {within sublevelV1Upsilon1 p, continuous tilt_sol^~ t}.
Proof.
(* TODO: using thm 3.4 *)
move=> /= u.
have [pu|] := nbhs_subspaceP _ u; last first.
  move=> pu y.
  (* to be cleaned *)
  rewrite /nbhs/= => -[M/= HM Hy].
  rewrite /nbhs_subspace.
  rewrite ifF.
    apply/negP.
    by rewrite inE.
  rewrite /globally/= => _ ->.
  apply: Hy => //= i j.
  rewrite /from_subspace.
  have := HM i j.
  rewrite /nbhs/=.
  rewrite /nbhs_ball_/= => -[e /= e0].
  apply.
  rewrite /ball_/=.
  rewrite /from_subspace.
  by rewrite subrr normr0.
have : u \in Tilt.Upsilon1 by move: pu => -[_ /mem_set].
move: t u pu.
suff : forall t, 0 < t -> {in sublevelV1Upsilon1 p,
    continuous (from_subspace (sublevelV1Upsilon1 p) (tilt_sol^~ t))}.
  move => Ht0 t u pu uUpsilon1.
  have [|t0] := ltP 0 t.
    by move => t0; apply Ht0; rewrite ?inE.
  have cont0 : {in sublevelV1Upsilon1 p, continuous (tilt_sol^~ 0)}.
    suff -> : (tilt_sol ^~ 0) = fun x => x by move => ? _; apply: cvg_id.
    apply/funext => x0.
    by rewrite tilt_sol0.
  have [-> |Ht] := eqVneq t 0.
    apply: continuous_in_subspaceT.
    by apply cont0; rewrite inE.
  have heq : {in sublevelV1Upsilon1 p,
      (fun p => 2 *: tilt_sol p 0 - tilt_sol p (- t)) =1 (tilt_sol^~ t)}.
    move => p' p's.
    have [/= h _] : lasalle_is_sol phi (tilt_sol p').
      apply tilt_sol_spec; rewrite tilt_sol0//.
      by move: p's; rewrite inE => -[].
    by rewrite -h// lt_neqAle Ht.
  apply: (subspace_eq_continuous heq).
  rewrite continuous_subspace_in.
  move => /= u' u'p.
  apply: cvgB => //=.
    apply: cvgZ; first by apply: cvg_cst.
    rewrite /nbhs_subspace/= u'p.
    apply: cvg_within_filter.
    exact: cont0.
  apply: Ht0 => //.
  by rewrite oppr_gt0 lt_neqAle Ht.
move=> t t0 u uUpsilon1.
apply/cvgrPdist_le => //= e e0.
near=> v.
have [pv|] := nbhs_subspaceP _ v; last first.
  move=> pv.
  exfalso.
  apply: pv.
  near: v.
  red.
  red.
  simpl.
  red.
  simpl.
  red.
  rewrite uUpsilon1.
  exact: withinT.
move : pv.
near:v.
have t01 : 0 < t + 1 by rewrite addr_gt0.
have [r' pur] : exists r' : {posnum K},
    sublevelV1Upsilon1 p `<=` closed_ball u r'%:num.
  have [M [Mr Mb ]]:= compact_bounded (@compact_sublevelV1Upsilon1 p).
  have mup : `|M| + `| u | + 1  > 0 by rewrite (lt_le_trans ltr01)// lerDr.
  exists (PosNum mup) => x0 Sx0.
  rewrite closed_ballE // /closed_ball_/= /incl_subspace/=.
  apply: (le_trans (ler_normB _ _)).
  rewrite -addrA [leRHS]addrC -addrA lerD//.
  apply Mb => //.
  apply: (le_lt_trans (ler_norm M)).
  by rewrite -{1}(add0r `|M|) ltr_leD.
have [k' k'r'phi] :
  exists (k' :  {posnum K}), {in `[0, t + 1]%R, K -> k'%:num.-lipschitz_(closed_ball u r'%:num) phi}.
  have [k kur'] := @tilt_eqn_locally_lipschitz_new _ alpha1 _ gamma_gt0 u r'%:num.
  exists k => x xt1.
  exact: kur'.
have k'0 : 0 < k'%:num by [].
near=>v.
move => pv.
have : {in closed_ball u r'%:num, forall y : 'rV_6,
    {within `[0, t + 1], continuous fun=> phi y} }.
  by move=> /= w wur ?//; exact: cvg_cst.
move/(@continuous_dependence K 6 (fun=> phi) 0 (t + 1) u v r' k' t01) => /(_ k'r'phi).
have vUpsilon1 : v \in Tilt.Upsilon1 by move: pv => -[_ /mem_set].
move=> /(_ (tilt_sol u) (tilt_sol v)).
have u0u : tilt_sol u 0 = u by rewrite /tilt_sol; case: cid2 => //= phi' [+ _]; exact.
have v0v : tilt_sol v 0 = v by rewrite /tilt_sol; case: cid2 => //= phi' [+ _]; exact.
have uUpsilon1' : u \in Tilt.Upsilon1.
  by apply mem_set; have /set_mem [_ +] := uUpsilon1.
have := @isSol_oo u (t + 1) uUpsilon1'.
rewrite u0u => /[swap] /[apply].
have := @isSol_oo v (t + 1) vUpsilon1.
rewrite v0v.
move=> /[swap] /[apply].
set hu := (X in (X -> _) -> _).
set hv := (X in (_ -> X -> _) -> _).
have Hu : hu.
  rewrite {}/hu/=.
  apply: subset_trans pur.
  move=> _ [y /= y0t] <-.
  apply: invariant_sublevelUpsilon1 => //.
    exact/set_mem.
  by rewrite (itvP y0t).
have Hv : hv.
  rewrite {}/hv/=.
  apply: subset_trans pur.
  move=> _ [y /= y0t] <-.
  apply: invariant_sublevelUpsilon1 => //.
  by rewrite (itvP y0t).
move/(_ Hu Hv) => /=.
move=> /(_ t).
rewrite inE/= in_itv/= (ltW t0)/= lerDl ler01 => /(_ isT).
move=> /le_trans; apply.
rewrite subr0.
rewrite -ler_pdivlMr ?expR_gt0//.
have: ball u (e /  expR (k'%:num * t)) v.
  near: v.
  have gt0 : 0 < e / expR (k'%:num * t) by rewrite !divr_gt0// expR_gt0.
  have [F/= mF Fu] := near_ball u _ gt0.
  red.
  red.
  simpl.
  red.
  simpl.
  red.
  simpl.
  red.
  rewrite uUpsilon1//.
  red.
  simpl.
  red.
  red.
  simpl.
  red.
  simpl.
  red.
  simpl.
  exists F => //= x/= Hx px.
  by apply: Fu.
by rewrite -ball_normE/= => /ltW.
Unshelve. all: by end_near. Qed.

Local Lemma sol_sublevelV1Upsilon1 p u :
  u \in sublevelV1Upsilon1 p -> sol_is_deriv_c0y (fun=> phi) (tilt_sol u).
Proof.
rewrite inE/= => -[h1 h2].
apply isSol => //.
by rewrite inE.
Qed.

Lemma V1dot_point1_eq0 : V1dot Tilt.point1 = (0 : K).
Proof.
rewrite /V1dot /Tilt.point1 /=.
rewrite lsubmx_const rsubmx_const enorm0 expr0n /= oppr0 add0r !mul0mx sub0r oppr0.
by rewrite mxE.
Qed.

Lemma V1dot_point2_eq0 : V1dot Tilt.point2 = (0 : K).
Proof.
rewrite /V1dot /Tilt.point2 /=.
rewrite row_mxKl row_mxKr.
rewrite enorm0 expr0n /= oppr0 add0r.
rewrite -!scalemxAl -scalerBr.
rewrite trmx0 mulmx0 subr0.
rewrite !scalemxAl.
rewrite norm_spin.
rewrite -!scalemxAl enormZ.
rewrite spinE.
suff -> : 'e_2 *v 'e_2 = (0 : 'rV[K]_3).
  by rewrite enorm0 /GRing.exp /= !mulr0 oppr0.
by rewrite vece2 /= scale0r.
Qed.

Local Lemma tilt_sol_continuous p : p \in Tilt.Upsilon1 -> continuous (tilt_sol p).
Proof.
move => sp t.
have [issol0 issol1]: lasalle_is_sol phi (tilt_sol p).
  apply: (@lasalle.sol_is_sol _ _ _ Tilt.Upsilon1 tilt_sol) => /=.
  - exact: tilt_sol0.
  - by move => y Ky; apply tilt_sol_spec.
  - exact/set_mem.
apply/differentiable_continuous/derivable1_diffP.
have [ht | ht] := ltP t 0; last first.
  apply: ex_derive.
  exact: issol1.
apply : (@near_eq_derivable _ _ _ (fun t => 2 *: tilt_sol p 0 - tilt_sol p (-t))) => /=.
  near do (rewrite -issol0//).
  exact: lt_nbhsl.
apply/derivable1_diffP.
apply: differentiable_comp => //.
apply: differentiable_comp => //.
apply: differentiable_comp => //.
apply/derivable1_diffP.
apply/ex_derive/issol1.
by rewrite ltW// oppr_gt0.
Unshelve. all: by end_near. Qed.

(* NB: application of lasalle.stable_limS *)
Local Lemma tilt_limS_subset_V1dot0 p :
  p \in Tilt.Upsilon1 ->
  lasalle.limS tilt_sol (sublevelV1Upsilon1 p) `<=`
  [set x : 'rV[K]_6 | V1dot x = 0] `&` Tilt.Upsilon1.
Proof.
move => ps.
have lasalle_sol : lasalle_solP phi (sublevelV1Upsilon1 p) tilt_sol.
  move=> y Ky.
  apply tilt_sol_spec.
  by apply Ky.
have H : lasalle.limS tilt_sol (sublevelV1Upsilon1 p) `<=`
         [set x | (Tilt.V1 alpha1 gamma \o tilt_sol x)^`()%classic 0 = 0] `&`
         Tilt.Upsilon1.
  rewrite subsetI; split.
  - apply: (@lasalle.stable_limS _ _ _ _ (@compact_sublevelV1Upsilon1 p) _ _
        lasalle_sol _ (@invariant_sublevelUpsilon1 p)
        (Tilt.V1 alpha1 gamma)) => //=.
    + exact: tilt_sol0.
    + exact: tilt_sol_cont.
    + apply/continuous_subspaceT => x xK.
      apply: differentiable_continuous.
      exact: V1_diff.
    + move=> /= p0 t K0 t0.
      apply/derivable1_diffP.
      apply: differentiable_comp.
        apply/derivable1_diffP.
        apply isSol => //; last first.
          by rewrite in_itv/= andbT.
        rewrite inE.
        by have [_ +] := K0.
      exact: V1_diff.
    + move=> p0 K0.
      have p0s : p0 \in Tilt.Upsilon1.
        by move : K0; rewrite inE/= /inE/= => -[].
      rewrite derive1E -derive_along_derive.
      * rewrite tilt_sol0.
        exact: V1_diff.
      * apply /derivable1_diffP.
        apply isSol => //.
        by rewrite in_itv/= lexx.
      * apply : derive_along_V1_le0_global => //=.
          by rewrite tilt_sol0.
        by apply isSol.
  - move=>/=x [q qKsub xcl].
    suff [] : (sublevelV1Upsilon1 q) x by [].
    rewrite (closure_id (sublevelV1Upsilon1 q)).1.
      apply compact_closed => //.
      exact: compact_sublevelV1Upsilon1.
    have qs (t : K) : 0 <= t -> state_space phi (sublevelV1Upsilon1 q) (tilt_sol q t).
      move=> t0; exists (tilt_sol q), (t + 1); split.
      + by rewrite tilt_sol0; apply: mem_sublevelV1Upsilon1; case: qKsub.
        by apply isSol_oo; rewrite inE; apply qKsub.
      + exists t => //.
        by rewrite /= in_itv/= t0 ltrDl ltr01.
    have lim_sp : (tilt_sol q x @[x --> +oo]) (sublevelV1Upsilon1 q).
      exists 0; split => // t t0 /=.
      apply invariant_sublevelUpsilon1.
        split => //=.
          exact: mem_sublevel_img.
        by case: qKsub.
      by rewrite ltW.
    by move: xcl; rewrite clusterE; exact.
apply: (subset_trans H) =>/= x [+ h1] /=.
rewrite /= derive1E -derive_along_derive.
- exact: V1_diff.
- apply/derivable1_diffP.
  apply isSol => //; last first.
    by rewrite bound_itvE.
  by rewrite inE.
- rewrite derive_along_V1_global//=.
    split.
      apply isSol => //.
        by apply/mem_set.
      apply isSol => //.
      by apply/mem_set.
  by rewrite tilt_sol0 ?inE.
Qed.

Lemma tilt_limS_points p : p \in Tilt.Upsilon1 ->
  limS tilt_sol (sublevelV1Upsilon1 p) `<=` Tilt.points.
Proof.
suff : Tilt.points = [set x : 'rV[K]_6 | V1dot  x = 0] `&` Tilt.Upsilon1.
  move=> ->.
  by apply tilt_limS_subset_V1dot0.
apply/seteqP; split => x /=.
  case => ->; split; [exact: V1dot_point1_eq0 | | exact: V1dot_point2_eq0 |].
    have := @tilt_point1_in_state_space K.
    by rewrite inE.
  have := @tilt_point2_in_state_space K.
  by rewrite inE.
move => [h1 h2'].
have h2 : x \in Tilt.Upsilon1 by rewrite inE.
move : h1.
have hi := tilt_sol0 x.
rewrite -hi => h1.
have sol' : sol_is_deriv_co (fun=> phi) 0 1 (tilt_sol x).
  apply: sol_is_deriv_c0yco.
  by apply isSol.
rewrite /Tilt.points/=.
apply: (V1dot_eq0_p1_or_p2 _ (isSol_oo 1 h2 )) => //.
  rewrite hi.
  exact/mem_set.
by rewrite bound_itvE ltr01.
Qed.

(* NB: application of lasalle.cvg_to_limS *)
Lemma cvg_to_set_points p : p \in Tilt.Upsilon1 ->
  tilt_sol p t @[t --> +oo] --> (Tilt.points : set 'rV_6).
Proof.
move=> /set_mem ps.
have p0K : forall p0 : 'rV_6, p0 \in sublevelV1Upsilon1 p -> tilt_sol p0 0 = p0.
  move => q /set_mem[_ h].
  exact: tilt_sol0.
apply: (cvg_trans (lasalle.cvg_to_limS (@compact_sublevelV1Upsilon1 p)
                    (@invariant_sublevelUpsilon1 p) _)).
  by apply/set_mem/mem_sublevelV1Upsilon1.
move => /= S [eps eps0 Be].
exists eps => //.
apply bigcup_sub => /= x H.
apply: (subset_trans _ Be).
have ps' : p \in Tilt.Upsilon1 by exact/mem_set.
have : Tilt.points x by apply: (tilt_limS_points ps').
move => h x' Bx'.
by exists x.
Qed.

Local Lemma avoid_x (x : U) : (~` Tilt.points) x ->
  exists S : set U, [/\ open S, Tilt.points `<=` S & ~ closure S x].
Proof.
move => hx.
have cx : closed [set x].
  by apply accessible_closed_set1; apply hausdorff_accessible.
have cp : closed (@Tilt.points K).
  rewrite /Tilt.points.
  by apply accessible_finite_set_closed => //; apply hausdorff_accessible.
have /(@normal_openP K) Hn : normal_space U by apply: pseudometric_normal.
have [|V1 [V2 [V1o V2o V1c V2c Vdisj]]] := (Hn _ _ cx cp).
  apply disjoints_subset.
  by rewrite sub1set; apply/mem_set .
exists V2;split => //.
move => h.
have [_ +] := open_disjoint_separated V1o V2o Vdisj.
apply /nonemptyPn => /=.
rewrite not_notE.
exists x.
split => //.
by apply V1c.
Qed.

Lemma tilt_cluster_points p : p \in Tilt.Upsilon1 ->
  cluster (tilt_sol p t @[t --> +oo]) `<=` Tilt.points.
Proof.
move => ps.
have /cvg_cluster cp12 := cvg_to_set_points ps.
apply: (subset_trans cp12).
rewrite clusterE.
move => /= x H.
suff : (~ (~` Tilt.points) x) by apply contrapT.
move => Hdist.
have [S [So Sc Sx]] := avoid_x Hdist.
have [e1 /= e10 /= P1] :  \forall e \near 0^'+, ball Tilt.point1 e `<=` S.
  apply: open_subball => //.
  by apply Sc; left.
have [e2 /= e20 /= P2] :  \forall e \near 0^'+, ball Tilt.point2 e `<=` S.
  apply: open_subball => //.
  by apply Sc; right.
set eps := Num.min (e1 / 2) (e2 / 2).
have eps0 : 0 < eps by rewrite lt_min !divr_gt0.
have B1 : ball Tilt.point1 eps `<=` S.
  apply P1 => //.
  rewrite /ball_/= sub0r normrN ger0_norm ?gt_min ?ltW // ltr_pdivrMr // ltr_pMr ?ltrDr //.
  by apply/orP; left.
have B2 : ball Tilt.point2 eps `<=` S.
  apply P2 => //.
  rewrite /ball_/= sub0r normrN ger0_norm ?gt_min ?ltW // ?ltr_pdivrMr // ltr_pMr ?ltrDr //.
  by apply/orP; right.
have nbh' : nbhs Tilt.points S.
  exists eps => //=.
  rewrite /ball_set.
  by apply: bigcup_sub => /= _ [-> | ->].
by have := H _ nbh'.
Qed.

Local Lemma connected2_subset (A : set U) : connected A -> A !=set0 ->
  A `<=` Tilt.points -> A = [set Tilt.point1] \/ A = [set Tilt.point2].
Proof.
move=> Ac Anonempty Asub.
have sep : separated [set (@Tilt.point1 K)] [set Tilt.point2].
  split.
  - rewrite -(closure_id _).1.
      by apply accessible_closed_set1; apply hausdorff_accessible.
    apply/disjoints_subset.
    rewrite sub1set.
    apply/mem_set => /=.
    exact/eqP/Tilt.point1_neq2.
  - rewrite setIC -(closure_id _).1.
      by apply accessible_closed_set1; apply hausdorff_accessible.
    apply/disjoints_subset.
    rewrite sub1set.
    apply/mem_set => /=.
    exact/nesym/eqP/Tilt.point1_neq2.
have [/subset_set1 [/nonemptyPn A0 | ] | /subset_set1 [/nonemptyPn A0 |] ] :=
  connected_subset sep Asub Ac => //.
by left.
by right.
Qed.

Local Lemma tilt_cluster_nonempty p : p \in Tilt.Upsilon1 ->
  cluster (tilt_sol p t @[t --> +oo]) !=set0.
Proof.
move => sp.
suff : (sublevelV1Upsilon1 p) `&` cluster (tilt_sol p t @[t --> +oo]) !=set0.
  move => [x [_ cx]].
  by exists x.
apply (@compact_sublevelV1Upsilon1 p) => //.
  exact: fmap_proper_filter.
apply (@sub_image_at_infty K^o) => /=.
move => _ [t t0] <-.
apply invariant_sublevelUpsilon1 => //.
exact/set_mem/mem_sublevelV1Upsilon1/set_mem.
Qed.

Lemma tilt_cvg_point1_point2 p : p \in Tilt.Upsilon1 ->
  (tilt_sol p t @[t --> +oo] --> Tilt.point1) \/
  (tilt_sol p t @[t --> +oo] --> Tilt.point2).
Proof.
move => ps.
have cluster_con : connected (cluster (tilt_sol p t @[t --> +oo])).
  apply: (compact_connected_cluster _ _ _ (@compact_sublevelV1Upsilon1 p) ) => //.
  - exact: pseudometric_normal.
  - exact: tilt_sol_continuous.
  - move=> t t0.
    apply/mem_set/invariant_sublevelUpsilon1 => //.
    exact/set_mem/mem_sublevelV1Upsilon1/set_mem.
have := connected2_subset cluster_con (tilt_cluster_nonempty ps)
                          (tilt_cluster_points ps).
suff H (q : U): cluster (tilt_sol p t @[t --> +oo]) = [set q] ->
    tilt_sol p t @[t --> +oo] --> q.
  by move => [h | h]; [left|right]; apply H.
move => H.
have sublevelUpsilon1q : sublevelV1Upsilon1 p q.
  suff: cluster (tilt_sol p t @[t --> +oo]) `<=` sublevelV1Upsilon1 p.
     by apply; rewrite H.
  rewrite clusterE.
  apply: (@subset_trans  _ (closure (tilt_sol p @` `[0, +oo[))).
    apply: bigcap_inf => //=.
    exists 0; split => //= x x0.
    exists x =>//.
    by rewrite in_itv/=ltW//.
  rewrite (closure_id (sublevelV1Upsilon1 p)).1.
    by apply: compact_closed => //; exact: compact_sublevelV1Upsilon1.
  apply: closureS => /= _ [t +] <-.
  rewrite /= in_itv/= andbT => t0.
  apply/invariant_sublevelUpsilon1 => //.
  exact/set_mem/mem_sublevelV1Upsilon1/set_mem.
have [M [Mr Mp]] : bounded_set (sublevelV1Upsilon1 p).
  apply compact_bounded.
  exact: compact_sublevelV1Upsilon1.
have [M0 | M0] := leP 0 M; last first.
  suff : `|q| < 0 by rewrite normr_lt0.
  have M02 : M < M / 2 by rewrite ltr_pdivlMr // gtr_nMr // ltrDl.
  have /= := Mp _ M02 _ sublevelUpsilon1q.
  move/le_lt_trans => ->//.
  by rewrite ltr_pdivrMr// mul0r.
set V := ball (p : U) (`|p| + (M + 1 + 1) : K).
have VsublevelUpsilon1  : sublevelV1Upsilon1 p `<=` V.
  move => /= x Kx.
  rewrite /V -ball_normE/ball_ /=.
  by rewrite (le_lt_trans (ler_normB _ _))// ltrD2l ltr_pwDr// Mp// ltrDl.
have cV : compact (closure V).
  rewrite closure_ballE closed_ballE//.
    by rewrite ltr_wpDl// addr_gt0// ltr_wpDl.
  apply: bounded_closed_compact; last exact: closed_closed_ball_.
  exists (`|p| + (`|p| + (M + 1 + 1))).
  split => //= x xB y Hy.
  rewrite -(subrKC p y).
  rewrite (le_trans (ler_normD _ _))// distrC (le_trans (lerD (lexx _ ) Hy))//.
  exact/ltW.
apply: (compact_cluster_set1 _ cV ) => //.
  rewrite nbhsE/=.
  exists V; last exact: subset_closure.
  by split => //; [exact: ball_open|exact: VsublevelUpsilon1].
apply: (filterS (closureS VsublevelUpsilon1)).
exists 0; split => //= x /ltW x0.
rewrite -(closure_id (sublevelV1Upsilon1 p)).1.
  by apply compact_closed =>//; exact: compact_sublevelV1Upsilon1.
apply: invariant_sublevelUpsilon1 => //.
exact/set_mem/mem_sublevelV1Upsilon1/set_mem.
Qed.

End LaSalle_tilt.
