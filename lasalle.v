(* LaSalle (c) 2025--2026 Inria and AIST. Licence: CeCILL-C.                  *)
(* -------------------------------------------------------------------------- *)
(* Copyright (c) - 2017 -- 2019 Inria                                         *)
(* -------------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import order interval_inference.
From mathcomp Require Import fintype bigop ssralg ssrnum finmap interval ssrint.
From mathcomp Require Import boolp reals classical_sets functions.
From mathcomp Require Import topology normedtype landau derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Def Num.Theory Order.POrderTheory Order.TotalTheory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.

Lemma mul2r (R : pzRingType) (x : R) : (2 * x = x + x)%R.
Proof. by rewrite -mulr2n mulr_natl. Qed.

Section pseudoMetricType_numDomainType.
Context {R : numDomainType} {M : pseudoMetricType R}.

Definition ball_set (A : set M) e := \bigcup_(p in A) ball p e.

(*HB.instance Definition _ := isPointed.Build (set M) [set point].*)

HB.instance Definition _ := isFiltered.Build M (set M) (nbhs_ball_ ball_set).

End pseudoMetricType_numDomainType.

Section PositiveLimitingSet.
Context {R : realFieldType} {U : pseudoPMetricType R}.

Definition pos_limit_set (y : R -> U) :=
  \bigcap_(eps in [set e | 0 < e]%R) \bigcap_(T in [set T | 0 < T]%R)
    [set p | ltr T `&` (y @^-1` ball p eps) !=set0].

Lemma plim_cluster (y : R -> U) :
  pos_limit_set y = cluster (y @ +oo%R).
Proof.
rewrite predeqE => p; split.
  move=> plim_p A B [M [Mreal ygtM_A]].
  move=> /nbhs_ballP [e egt0 pe_B].
  wlog Mgt0 : M Mreal ygtM_A / (0 < M)%R; last first.
    by have [t [/ygtM_A Ayt /pe_B Byt]] := plim_p _ egt0 _ Mgt0; exists (y t).
  move=> /(_ (maxr M 1%R)) []; last by move=> q ?; exists q.
      by rewrite max_real// real1.
    by move=> ?; rewrite gt_max => /andP [/ygtM_A].
  by rewrite lt_max orbC ltr01.
move=> clyp e egt0 T Tgt0.
have [] := clyp (y @` ltr T) (ball p e).
  by exists T; rewrite num_real; split => //; exact: imageP.
  by rewrite -nbhs_ballE; exists e.
by move=> _ [[t ? <-] ?]; exists t.
Qed.

Lemma plimn0 (y : R -> U) (A : set U) :
  compact A -> (y @ +oo%R) A -> cluster (y @ +oo%R) !=set0.
Proof. by move=> Aco /Aco [p []]; exists p. Qed.

Lemma closed_plim (y : R -> U) : closed (cluster (y @ +oo%R)).
Proof.
by rewrite clusterE; apply: closed_bigI => ??; apply: closed_closure.
Qed.

Lemma filter_cluster (F : set (set U)) (A : set U) :
  ProperFilter F -> F A -> compact A ->
  forall e, (0 < e)%R -> F (ball_set (cluster F) e).
Proof.
move=> FF FA; rewrite compact_In0 => Aco e egt0.
set B := ball_set (cluster F) e.
have Fn0 : F !=set0 by exists A.
have : A `&` (cluster F `\` B°) = set0.
  suff -> : cluster F `\` B° = set0 by rewrite setI0.
  rewrite setD_eq0 => p clFp.
  by rewrite /interior -nbhs_ballE; exists e => // ??; exists p.
rewrite clusterE.
rewrite -[_ `\` _]bigcapIl // setIC.
rewrite -bigcapIl // => IFBoA0.
set f := fun C => closure C `&` ~` B° `&` A.
have [G sGF IGBoA0] : exists2 G : {fset (set U)},
  {subset G <= F} & \bigcap_(C in [set C | C \in G]) f C = set0.
  have {}IFBoA0 : ~ (\bigcap_(C in F) f C !=set0).
    by move=> [p IFBoAp]; rewrite -[False]/(set0 p) -IFBoA0.
  have /Aco : closed_fam_of A F f.
    exists (fun C => closure C `&` ~` B°).
      move=> C _; apply: closedI (@closed_closure _ _) _.
      by rewrite closedC; exact/open_interior.
    by move=> ? _; rewrite setIC.
  move=> /contra_not /(_ IFBoA0) /asboolPn /existsp_asboolPn [H /asboolPn].
  move=> /imply_asboolPn [sHF IHBoA0]; exists H => //.
  by rewrite predeqE => p; split=> // IHBoAp; apply: IHBoA0; exists p.
have Gn0 : [set C | C \in G] !=set0.
  apply: contrapT => /asboolPn /forallp_asboolPn G0.
  by rewrite -[False]/(@set0 U point) -IGBoA0 => ? /G0.
move: IGBoA0; have -> : \bigcap_(C in [set C | C \in G]) f C =
  \bigcap_(C in [set C | C \in G]) (A `&` closure C `&` ~` B°).
  by rewrite predeqE => a; split=> IGBoAa ? /IGBoAa [[]].
rewrite bigcapIl // setD_eq0 => sIGABo.
suff : F B° by apply: filterS => ?; apply: nbhs_singleton.
apply: filterS sIGABo _; apply: filter_bigI => C /sGF; rewrite in_setE => FC.
by apply: filterI FA _; apply: filterS (@subset_closure _ C) _.
Qed.

Lemma cvg_to_plim (y : R -> U) (A : set U) :
  (y @ +oo%R) A -> compact A -> y @ +oo%R --> cluster (y @ +oo%R).
Proof.
move=> yinftyA coA B [e egt0 scleB].
by apply: filterS scleB _; exact: filter_cluster coA _ egt0.
Qed.

(* Lemma cvg_to_plim y (A : set U) : *)
(*   (y @ +oo) A -> compact A -> y @ +oo --> cluster (y @ +oo). *)
(* Proof. *)
(* move=> yinftyA coA; apply/NNP. *)
(* move=> /asboolPn /existsp_asboolPn [B] /asboolPn /imply_asboolPn. *)
(* move=> [[e egt0 plim_e_B] /asboolPn /forallp_asboolPn nygtxB]. *)
(* suff : ~` B `&` B !=set0 by case=> ? []. *)
(* have proper_within_CB : ProperFilter (within (~` B) (y @ +oo)). *)
(*   apply: Build_ProperFilter=> C [T ygtTsBC]. *)
(*   have /asboolPn /existsp_asboolPn [t /asboolPn /imply_asboolPn [tgtT nByt]] *)
(*     := nygtxB T. *)
(*   by exists (y t); apply: ygtTsBC. *)
(* have [|p [Ap plimnBp]] := coA _ proper_within_CB. *)
(*   exact: flim_within yinftyA. *)
(* apply plimnBp; first exact: withinT. *)
(* rewrite -locally_ballE; exists e => // q pe_q; apply: plim_e_B. *)
(* by exists p => // C D yinftyC; apply/plimnBp; apply: flim_within yinftyC. *)
(* Qed. *)

Lemma sub_image_at_infty (y : R -> U) (A : set U) :
  y @` (>= 0)%R `<=` A -> (y @ +oo%R) A.
Proof.
move=> syRpA; exists 0%R; rewrite real0; split => // t tgt0.
exact/syRpA/imageP/ltW.
Qed.

Lemma sub_plim_clos_invar (y : R -> U) (A : set U) :
  y @` (>= 0)%R `<=` A -> cluster (y @ +oo%R) `<=` closure A.
Proof. by move=> syRpA p ypp B /ypp; apply; exact: sub_image_at_infty. Qed.

Lemma map_sub_cluster (S T : topologicalType) (F : set_system S) (f : S -> T)
  (A : set S) : Filter F -> {within A, continuous f} -> F A -> closed A ->
  f @` (cluster F) `<=` cluster (f @ F).
Proof.
move=> Ffilt fcont FA Acl _ [p clFp <-] B C fFB.
have Ap : A p by apply: Acl => ? /clFp - /(_ _ FA).
move/subspace_continuousP in fcont.
move=> /(fcont _ Ap) fp_C.
suff /clFp /(_ fp_C) [q [[Aq ?] /(_ Aq)]] : F (A `&` f @^-1` B) by exists (f q).
exact: filterI.
Qed.

Lemma c0_cvg_cst_on_plim A (y : R -> U) (V : U -> R^o) (l : R^o) :
  {within A, continuous V} -> V \o y @ +oo%R --> l ->
  closed A -> y @` (>= 0)%R `<=` A -> cluster (y @ +oo%R) `<=` V @^-1` [set l].
Proof.
move=> Vcont Vypl Acl syRpA p plimp.
have Aypinfty : (y @ +oo%R) A by apply: sub_image_at_infty.
have : (V @` cluster (y @ +oo%R)) (V p) by exists p.
move=> /(map_sub_cluster _ Vcont Aypinfty Acl).
by move=> /(cvg_cluster Vypl) /Rhausdorff ->.
Qed.

End PositiveLimitingSet.

Lemma bounded_plim (K : realFieldType) (V : normedModType K) (y : K -> V) :
  bounded_set (y @` (>= 0)%R) -> bounded_set (cluster (y @ +oo%R)).
Proof.
rewrite /bounded_set => - [N [Nreal ybndN]].
wlog Ngt0 : N Nreal ybndN / (0 < N)%R.
  move=> bnd_plim; apply: (bnd_plim (maxr N 1%R)); last first.
    by rewrite lt_max orbC ltr01.
  by move=> ?; rewrite gt_max => /andP [/ybndN].
  by rewrite max_real// real1.
rewrite /bounded_set.
red.
near=> M => p plimp.
have [] := plimp (y @` (>= 0)%R) (ball_ Num.norm p (PosNum Ngt0)%:num).
- exact: sub_image_at_infty.
- exact: nbhs_ball_norm.
move=> _ [[t tge0 <-] pN_yt]; rewrite -[p](subrK (y t)).
apply: (le_trans (ler_normD _ _)).
rewrite -lerBrDr.
apply/ltW; apply: lt_le_trans pN_yt _.
rewrite lerBrDr addrC -lerBrDr; apply: ybndN; last by exists t.
by rewrite ltrBrDr; near: M; exists (N + N)%R; rewrite realD.
Unshelve. all: by end_near. Qed.

(* TODO: update lasalle on github *)
Lemma nearN (R : realFieldType) (P : set R) :
  (\forall x \near (0%R : R^o), P x) = (\forall x \near (0%R : R^o), P (- x)%R).
Proof.
by rewrite propeqE; split; rewrite -nearN oppr0.
Qed.

Section DifferentialSystem.
Context {R : realType}.
Variable U : normedModType R.
Let hU : hausdorff_space U := @norm_hausdorff _ U.

(* function defining the differential system *)
Variable F : U -> U.

Definition is_sol (y : [the normedModType _ of R^o] -> U) :=
  (forall t, t < 0 -> y t = 2 *: (y 0) - (y (- t)))%R /\
  forall t, (0 <= t)%R -> is_derive (t : R^o) 1%R y (F (y t)).

(* compact set used in LaSalle's invariance principle *)
Variable K : set U.
Hypothesis Kco : compact K.

(* solution function *)
Variable sol : U -> R -> U.
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y : R -> U, K (y 0%R) -> is_sol y <-> y = sol (y 0%R).
Hypothesis sol_cont : forall t, {within K, continuous (sol^~ t)}.

Lemma sol_is_sol p : K p -> is_sol (sol p).
Proof. by move=> Kp; apply/solP; rewrite sol0. Qed.
Hint Resolve sol_is_sol : core.

Lemma uniq_sol (x y : R -> U) :
  K (x 0%R) -> K (y 0%R) -> is_sol x -> is_sol y -> x 0%R = y 0%R -> x = y.
Proof. by move=> Kx0 Ky0 /(solP Kx0)-> /(solP Ky0)->; rewrite !sol0 => ->. Qed.

Definition is_invariant A := forall p, A p -> forall t, (0 <= t)%R -> A (sol p t).

Hypothesis Kinvar : is_invariant K.

Definition shift_sol p t0 t :=
  (if t >= 0 then sol p (t + t0) else 2 *: (sol p t0) - (sol p (- t + t0)))%R.

Lemma sol_shift p (t0 : R^o) : K p -> (0 <= t0)%R -> is_sol (shift_sol p t0).
Proof.
move=> Kp t0ge0; split=> [t tlt0|t tge0].
  rewrite /shift_sol leNgt tlt0/= lexx/=.
  rewrite ltW ?oppr_gt0//.
  rewrite [X in _ = (2 *: sol p X - _)%R](_ : _ = t0)//.
  by rewrite add0r.
suff dshift : (shift_sol p t0) \o shift t = (cst (shift_sol p t0 t) +
  (fun h : R^o => h *: F (shift_sol p t0 t)))%R +o_ (0%R : R^o) (id : R^o -> R^o).
  move=> [:dshiftE].
  have diff_shift : differentiable (shift_sol p t0 : R^o -> _) t.
    apply/diff_locallyP; split; last first.
      apply/eqaddoE; rewrite dshift.
      congr +%R.
(* 0.3.6:
  (cst (shift_sol p t0 t) +  *:%R^~ (F (shift_sol p t0 t)))%R =
  (cst (shift_sol p t0 t) + 'd (shift_sol p t0) t)%R *)
      congr +%R.
      abstract: dshiftE.
      have lin_scal : linear (fun h : R^o => h *: F (shift_sol p t0 t))%R.
        by move=> ???; rewrite scalerDl scalerA.
      pose glM := GRing.isLinear.Build _ _ _ _ _ lin_scal.
      pose gL : {linear R^o -> U} := HB.pack ( *:%R^~ (F (shift_sol p t0 t))) glM.
      have -> : (fun h : R^o => h *: F (shift_sol p t0 t))%R = gL by [].
      apply/esym.
      apply: diff_unique; first exact: scalel_continuous.
      apply/eqaddoE; rewrite dshift.
(* 0.3.6:
  (cst (shift_sol p t0 t) +  *:%R^~ (F (shift_sol p t0 t)) + 'o_[filter of 0] id )%R =
  (cst (shift_sol p t0 t) + Linear lin_scal + 'a_o_(nbhs_filter_on 0) id )%R *)
      by [].
    by rewrite -dshiftE; apply: scalel_continuous.
  apply: DeriveDef; first exact/derivable1_diffP.
  by rewrite deriveE // -dshiftE scale1r.
have /sol_is_sol [_ solp] := Kp.
have /solp solp' : (0 <= t + t0)%R by apply: addr_ge0 => //; apply: ltrW.
rewrite /shift_sol tge0.
move: tge0; rewrite le_eqVlt orbC => /orP [tgt0|/eqP teq0].
  apply/eqaddoP => _ /posnumP[e]; near=> s.
  rewrite -![(_ + _ : _ -> _)%R _]/(_ + _)%R /=.
  have /derivable_nbhs : derivable (sol p : R^o -> U) (t + t0) 1 by [].
  rewrite funeqE => /(_ s) /=; rewrite addrA [(_%:A)%R]mulr1 =>->.
  suff -> /= : (0 <= s + t)%R.
    rewrite derive_val addrC addrA [(_ s + _)%R]addrC subrr add0r.
    near: s.
    case: e => /= e.
    rewrite /Itv.num_sem/= num_real/= in_itv/= andbT.
    move: e.
    apply/(eqoP (nbhs_filter_on (0%R : R))).
    (* 0.3.6: 'o_[filter of nbhs 0%R] id  = 'o_(nbhs_filter_on 0%R) id  *)
    by [].
  near: s; exists t => // s; rewrite /ball_ /= => ltst.
  rewrite -lerBlDl sub0r; apply/ltW; apply: le_lt_trans ltst.
  by rewrite sub0r ler_norm.
rewrite -teq0.
rewrite shift0.
rewrite add0r.
apply/eqaddoP => _ /posnumP[e]; near=> s.
rewrite -![(_ + _ : _ -> _)%R _]/(_ + _)%R /=.
rewrite -[t0]add0r/=.
rewrite {1 2 3 4 5 6}teq0.
have /derivable_nbhs dsol : derivable (sol p : R^o -> U) (t + t0) 1 by [].
have := dsol; rewrite funeqE => /(_ (- s)%R) /=; rewrite [(_%:A)%R]mulr1 =>->.
have := dsol; rewrite funeqE => /(_ s) /=; rewrite [(_%:A)%R]mulr1 =>->.
rewrite -{1}teq0 derive_val; case: (lerP 0 s) => [le0s|lts0].
  rewrite addrC addrA [(_ s + _)%R]addrC subrr add0r; near: s.
  case: e => /= e.
  rewrite /Itv.num_sem num_real in_itv/= andbT.
  move: e.
  apply/(eqoP (nbhs_filter_on (0%R : R))).
(* 0.3.6:
  'o_[filter of nbhs 0%R] id  = 'o_(nbhs_filter_on 0%R) id *)
  by [].
rewrite !opprD oppox /cst /= addrACA -[(- _ : _ -> _)%R _]/(- _)%R !addrA.
rewrite [X in (X *: _)%R](_ : _ = (1 + 1)%R); first by [].
rewrite scalerDl scale1r -[(_ - _ - sol _ _)%R]addrA -opprD subrr sub0r.
rewrite scaleNr opprK addrC addKr -[in X in (_ <= X)%R]normrN; near: s.
rewrite !near_simpl.
rewrite -(nearN (fun x : R^o => `|_ x| <= e%:num * `|x|%R))%R.
case: e => /= e.
rewrite /Itv.num_sem num_real in_itv/= andbT => e0.
near=> x.
set u := (X in `|X x|%R).
near: x.
exact: (@eqoP _ _ _ _ (nbhs_filter_on (0%R : R^o)) id u).1.
Unshelve. all: by end_near. Qed.

Lemma solD p t0 t :
  K p -> (0 <= t0)%R -> (0 <= t)%R -> sol p (t + t0) = sol (sol p t0) t.
Proof.
move=> Kp t0ge0 tge0; have /sol_shift /(_ t0ge0) /solP := Kp.
rewrite [shift_sol _ _ _]/shift_sol lexx.
rewrite add0r.
move=> <-; first exact: Kinvar.
by rewrite /shift_sol tge0.
Qed.

Lemma invariant_plim p : K p -> is_invariant (cluster (sol p @ +oo%R)).
Proof.
move=> Kp q plim_q t0 t0_ge0 A B [M].
wlog Mge0 : M / (0 <= M)%R => [sufMge0|] [Mreal solpMinfty_A].
  apply: (sufMge0 (maxr 0%R M)); first by rewrite le_max lexx.
  split.
    by rewrite max_real// real0.
  by move=> x; rewrite gt_max => /andP[_]; apply: solpMinfty_A.
have Kq : K q.
  apply: compact_closed => // C qC.
  move: plim_q; apply => //.
  exists 0%R; split => // t /ltW tge0.
  exact: Kinvar.
have sol_cont' : forall t : R,
    (forall x : U, K x -> (sol^~ t) x @[x --> within K (nbhs x)] --> (sol^~ t) x).
  by move=> t; exact/subspace_continuousP/sol_cont.
move=> /(sol_cont' t0 _ Kq) /plim_q q_Bsolt0.
have /q_Bsolt0 [_ [[[t tgtM <-] _]]] : (sol p @ +oo%R) (sol p @` (> M)%R `&` A).
  by exists M; split => // => t tgtM; split; [apply: imageP|apply: solpMinfty_A].
have tge0 : (0 <= t)%R by apply/ltW; apply: le_lt_trans tgtM.
have Ksolpt : K (sol p t) by apply: Kinvar.
move=> /(_ Ksolpt) /=; rewrite -solD // => Bsolpt0t; exists (sol p (t0 + t)).
by split=> //; exact/solpMinfty_A/ltr_wpDl.
Qed.

Definition limS (A : set U) := \bigcup_(q in A) cluster (sol q @ +oo%R).

Lemma invariant_limS A : A `<=` K -> is_invariant (limS A).
Proof.
move=> sAK p [q Aq plimp] t tge0.
by exists q => //; apply: invariant_plim => //; apply: sAK.
Qed.

Lemma nincr_lb_cvg (f : R -> R) :
  (forall x y, 0 <= x <= y -> f y <= f x)%R ->
  (exists M, f @` (>= 0)%R `<=` (> M)%R) -> cvg (f @ +oo%R).
Proof.
move=> fnincr [M ltMf].
apply/cvg_ex; exists (inf (fun x => x \in f @` (>= 0)%R)).
move=> A /nbhs_ballP [_ /posnumP[e] infe_A].
have imf_inf : has_inf (fun x => x \in f @` (>= 0)%R).
  split; first by exists (f 0%R); rewrite in_setE; apply: imageP.
  by exists M; apply/lbP => ?; rewrite in_setE => /ltMf /ltW.
have := imf_inf => /inf_adherent => /(_ e%:num)%R.
move=> /(_ (gt0 e)) [x].
rewrite in_setE => -[t tge0 <-] ltftinfe.
exists t; rewrite num_real; split => // s ltts; apply: infe_A.
rewrite /ball/=.
rewrite distrC ger0_norm; last first.
  rewrite ltrBlDl.
  by apply: le_lt_trans ltftinfe; apply: fnincr; rewrite tge0 (ltW ltts).
rewrite subr_ge0.
apply: ge_inf.
  by case: imf_inf.
rewrite in_setE; apply: imageP.
by apply: ltW; exact: le_lt_trans ltts.
Qed.

(* todo: use directional derivative *)
Lemma stable_limS (V : U -> R^o) :
  {within K, continuous V} ->
  (forall p t, K p -> (0 <= t)%R -> derivable (V \o sol p : R^o -> R^o) t 1) ->
  (forall (p : U), K p -> (V \o sol p)^`() 0 <= 0)%R ->
  limS K `<=` [set p | (V \o sol p)^`() 0 = 0]%R.
Proof.
move=> Vcont Vsol_drvbl Vsol'le0 p [q Kq plimp].
have ssqRpK : sol q @` (>= 0)%R `<=` K by move=> _ [t tge0 <-]; apply: Kinvar.
(* should be inferred *)
(*have atrF := at_right_proper_filter 0%R. (* is it now?*) *)
suff : exists l, cluster (sol q @ +oo%R) `<=` V @^-1` [set l].
  move=> [l Vpliml]/=; rewrite derive1E /derive cvg_at_rightE.
    apply: Vsol_drvbl => //; apply: compact_closed => //.
    exact: sub_plim_clos_invar plimp.
  apply: (@cvg_lim _ _ _ (at_right _)) => // A A0.
  rewrite !near_simpl; near=> h.
  rewrite /= sol0 addr0.
  rewrite [X in sol p X](_ : _ = h); first by rewrite scaler1.
  rewrite Vpliml//.
    by apply: invariant_plim => //; apply: ltW; near: h; exists 1%R.
  by rewrite Vpliml // subrr scaler0; apply: nbhs_singleton.
suff cvVsol : cvg (V \o sol q @ +oo%R).
  exists (lim (V \o sol q @ +oo%R)); apply: (c0_cvg_cst_on_plim Vcont) => //.
  exact: compact_closed.
apply: nincr_lb_cvg; last first.
  have: compact (V @` K) by exact: continuous_compact.
  move=> /compact_bounded [N imVltN].
  exists (- (N + 2))%R=> _ [t tge0 <-].
  suff : (`|(V \o sol q) t| < N + 2)%R by rewrite ltr_norml => /andP[].
  rewrite (@le_lt_trans _ _ (N + 1)%R)// ?ltrD2l ?ltr1n//.
  by apply: imVltN.2; [rewrite ltrDl|apply/imageP/Kinvar].
move=> s t /andP [sge0 slet].
apply: (@ler0_derive1_le_cc _ _ s t); first 2 last.
  apply: continuous_in_subspaceT => x.
  rewrite inE/= in_itv/= => /andP[sx xt].
  have := Vsol_drvbl _ _ Kq (le_trans sge0 sx).
  move/derivable1_diffP/differentiable_continuous.
  exact.
  by rewrite in_itv/= slet lexx.
  by rewrite in_itv/= lexx slet.
  by [].
  move=> r rst.
  apply: Vsol_drvbl => //; apply: le_trans sge0 _.
  by rewrite (itvP rst).
move=> r rst.
have rge0 : (0 <= r)%R by apply: le_trans sge0 _; rewrite (itvP rst).
suff -> : derive1 (V \o sol q) r = derive1 (V \o (sol (sol q r))) 0.
  exact/Vsol'le0/Kinvar.
rewrite derive1E /derive cvg_at_rightE; first exact: Vsol_drvbl.
rewrite derive1E /derive cvg_at_rightE.
  by apply: Vsol_drvbl => //; apply: Kinvar.
congr (lim _); rewrite predeqE /= nbhs_filterE => A; split.
  move=> [_/posnumP[e] Ae]; exists e%:num%R=> //= x xe xgt0.
  rewrite sol0/=.
  rewrite addr0 -solD //; [|exact: Ae].
  by rewrite scaler1 ltW.
move=> [_/posnumP[e] Ae]; exists e%:num%R => //= x xe xgt0.
have /Ae - /(_ xe) := xgt0.
by rewrite sol0/= addr0 -solD// scaler1 ltW.
Unshelve. all: by end_near. Qed.

Lemma cvg_to_limS (A : set U) : compact A -> is_invariant A ->
  forall p, A p -> sol p @ +oo%R --> (limS A : set U).
Proof.
move=> Aco Ainvar p Ap B [_/posnumP[e] limSeB].
apply: (cvg_to_plim _ Aco).
  exists 0%R; split => //.
  by move=> _/posnumP[?]; exact: Ainvar.
exists e%:num%R=> //= q [r plimr re_q].
by apply: limSeB; exists r => //; exists p.
Qed.

End DifferentialSystem.
