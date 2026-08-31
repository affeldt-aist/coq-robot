From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  poly archimedean generic_quotient ring_quotient interval_inference
  ring_tactic field_tactic.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets
  contra functions reals topology prodnormedzmodule tvs normedtype landau
  ereal sequences exp derive numfun measure realfun measurable_realfun
  lebesgue_measure lebesgue_integral ftc.
Require Import tilt_mathcomp tilt_analysis vector_integral ode_common
  ode_contseg picard_contraction ode_local gronwall.

(**md**************************************************************************)
(* # Global versions of the Cauchy-Lipschitz theorem                          *)
(*                                                                            *)
(* `sol_extended`                                                             *)
(* : TODO                                                                     *)
(*                                                                            *)
(* `valid_right_endpoints phi a u0`                                           *)
(* : the set of right end-points b such that there is a solution on [a, b]    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Section is_sol_cauchy_ooN.
Context {R : realType} {n} (U := 'rV[R]_n).

Let is_sol_cauchy_ooN0 (phi : R -> U -> U) (a b : R) (f : R -> U) :
    a <= b -> is_sol_cauchy_oo phi a b (f a) f ->
  is_sol_cauchy_oo (fun t x => - phi (- t) x) (- b) (- a) (f b) (f \o -%R).
Proof.
move=> ab [_ [df cf]]; split => /=; first by rewrite opprK.
split.
  move=> x.
  rewrite -oppr_itvoo => /df[derivablef Df].
  have derivablefN : derivable (f \o -%R) x 1.
    apply/derivable1_diffP; apply differentiable_comp => //.
    exact/derivable1_diffP.
  split => //.
  apply/rowP => i.
  rewrite mxE derive1E derive_mx//= mxE -derive1E/=.
  rewrite [X in X^`()](_ : _ = ((fun t => f t 0 i) \o -%R)); first exact/funext.
  rewrite derive1_comp/=; first by [].
  - by move/derivable_mxP: derivablef.
  - rewrite !derive1N//=derive1_id/= mulrN1.
    move/rowP : Df =>  /(_ i).
    rewrite !derive1E/= !derive_mx/=; first exact: derivablef.
    by rewrite /=!mxE => ->.
move: ab; rewrite le_eqVlt => /predU1P[->|ab].
  rewrite set_itv_ge ?closure0; last exact: continuous_subspace0.
  by rewrite bnd_simp ltxx.
rewrite closure_itvoo; first by rewrite ltrN2.
by apply: within_continuous_compN; rewrite !opprK -closure_itvoo.
Qed.

Lemma is_sol_cauchy_ooN (phi : R -> U -> U) (a b : R) (f : R -> U) :
    a <= b -> is_sol_cauchy_oo phi a b (f a) f <->
  is_sol_cauchy_oo (fun t x => - phi (- t) x) (- b) (- a) (f b) (f \o -%R).
Proof.
move=> ab; split; first by apply is_sol_cauchy_ooN0.
move=> is_solf.
suff : is_sol_cauchy_oo (fun t x => - - (phi (- - t) x)) (- - a) (- - b)
    ((f \o -%R) (- a)) ((f \o -%R) \o -%R).
  rewrite /= !opprK.
  have -> : ((f \o -%R) \o -%R) = f.
    by rewrite -compA; apply/funext=> x /=; rewrite opprK.
  by congr is_sol_cauchy_oo; apply/eq2_fun => t x; rewrite !opprK.
apply: (@is_sol_cauchy_ooN0 (fun t x => - phi (- t) x)).
  by rewrite lerN2.
by rewrite /= opprK.
Qed.

End is_sol_cauchy_ooN.

Section is_sol_cauchy_inftyP.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a : R) (u0 : U).

Lemma is_sol_cauchy_inftyP f : is_sol_cauchy phi a +oo%O u0 f <->
  (forall b, is_sol_cauchy_oo phi a b u0 f).
Proof.
split.
- move => [fau0 [derivf contf]] b; split; first exact: fau0.
  split.
    move=> t tab; apply derivf.
    exact: subset_itvl tab.
  apply/continuous_subspaceW/contf/closureS.
  exact: subset_itvl.
- move=> h; split; first by apply h.
  split.
    move=> t tab.
    apply (h (t + 1)).
    by rewrite in_itv/= (itvP tab) ltrDl ltr01.
  rewrite closure_neitv_oy; apply/continuous_within_itvcyP.
  split.
    move=> /= t tab.
    have := (h (t + 1)).2.2.
    have at1 : a < t + 1 by rewrite ltr_wpDr// (itvP tab).
    rewrite closure_itvoo//.
    move=> /(continuous_within_itvP _ at1)[+ _ _].
    apply.
    by rewrite in_itv/= (itvP tab) ltrDl/=.
  have := (h (a + 1)).2.2.
  rewrite closure_itvoo.
    by rewrite ltrDl.
  move/continuous_within_itvP.
  rewrite ltrDl => /(_ ltr01).
  by case => [_ + _].
Qed.

End is_sol_cauchy_inftyP.

Section extend_solution.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b c : R)
  (u0 u1 : U) (r : {posnum R}) (k : R) (f : R -> U).

Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis k0 : 0 < k.
Let B := closed_ball u1 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, c], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, c]%R, forall x, k.-lipschitz_B (phi x)}.

Let cont1_restr : {in B, forall y, {within `[b, c], continuous phi ^~ y}}.
Proof.
move=> x xb; apply/continuous_subspaceW/cont1 => //.
by apply: subset_itvr; rewrite ltW.
Qed.

Let lip2_restr : {in `[b, c]%R, forall x, k.-lipschitz_B (phi x)}.
Proof.
move=> x xb; apply lip2.
by apply: subset_itvr xb; rewrite bnd_simp/= ltW.
Qed.

(* (* solution on max interval [a, b) *) *)
(* Hypothesis is_integral_sol_co : forall b', b' \in `[a,b[%R -> is_integral_sol phi u0 a b' sol. *)

Hypothesis is_sol_oo_f : forall t, t \in `[a, b[%R ->
  is_sol_cauchy_oo phi a t u0 f.

(* limit at the right boundary is u1 and u1 is in safe area *)
Hypothesis has_left_limit : f @ b^'- --> u1.

Let rho : {posnum R} := 2^-1%:pos.

Let rho1 : rho%:num < 1. Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Let f0 : f a = u0.
Proof.
have /is_sol_oo_f : a \in `[a, b[%R by rewrite bound_itvE.
by case.
Qed.

Let sol_is_deriv_f : sol_is_deriv phi `]a, b[%R f.
Proof.
move=> t tab.
have [t' tt' t'ab] : exists2 t', t < t' & t' \in `[a, b[%R.
  exists ((t + b) / 2).
    by rewrite midf_lt ?(itvP tab).
  rewrite in_itv/= midf_lt ?(itvP tab) ?andbT//.
  by rewrite (@le_trans _ _ t) ?(itvP tab)// midf_le ?(itvP tab).
have [_ [+ _]] := is_sol_oo_f t'ab.
apply.
by rewrite in_itv/= (itvP tab) tt'.
Qed.

Let cont_f t : t \in `]a, b[%R -> continuous_at t f.
Proof.
move=> tab.
have [t' tt' t'ab] : exists2 t', t < t' & t' \in `[a, b[%R.
  exists ((t + b) / 2).
    by rewrite midf_lt ?(itvP tab).
  rewrite in_itv/= midf_lt ?(itvP tab) ?andbT//.
  by rewrite (@le_trans _ _ t) ?(itvP tab)// midf_le ?(itvP tab).
have [_ [_ +]] := is_sol_oo_f t'ab.
have at' : a < t' by rewrite (lt_trans _ tt')// (itvP tab).
rewrite closure_itvoo//.
move/(continuous_within_itvP _ at') => [+ _ _]; apply.
by rewrite in_itv/= tt' (itvP tab).
Qed.

Let cont_left_f : f x @[x --> a^'+] --> f a.
Proof.
have [t' t'a t'ab] : exists2 t', a < t' & t' \in `[a, b[%R.
  exists ((a + b) / 2).
    by rewrite midf_lt.
  by rewrite in_itv/= midf_lt ?andbT// ltW// midf_lt.
have [_ [_ +]] := is_sol_oo_f t'ab.
rewrite closure_itvoo//.
by move /(continuous_within_itvP _ t'a) => [_ + _].
Qed.

(* the function u1 at b and f elsewhere *)
Let f_ext_bu1 := patch f [set b] (cst u1).

Lemma is_sol_oo_f_ext_bu1 : is_sol_cauchy_oo phi a b u0 f_ext_bu1.
Proof.
rewrite /f_ext_bu1.
split; first by rewrite patchC // in_setC in_set1 lt_eqF.
split.
  move=> t /[dup] tab.
  rewrite in_itv/= => /andP[at0 tb0].
  have hn : {near t, f =1 f_ext_bu1}.
    near=> x.
    rewrite /f_ext_bu1 patchC //in_setC in_set1 lt_eqF //.
    by near: x; exact: lt_nbhsl.
  split.
    apply: (near_eq_derivable hn).
    by apply sol_is_deriv_f.
  rewrite derive1E.
  rewrite (near_eq_derive (g := f)).
    by near do symmetry.
  by rewrite patchC // ?in_setC ?in_set1 ?lt_eqF // -derive1E; apply sol_is_deriv_f.
rewrite closure_itvoo//.
apply/continuous_within_itvP => //; split.
- move=> x /[dup] xab.
  rewrite in_itv/= => /andP[ax xb].
  apply : cvg_trans.
    apply: (near_eq_cvg (f := f)).
    near=> t.
    rewrite patchC // ?in_setC ?in_set1 ?lt_eqF //.
    by near: t; exact: lt_nbhsl.
  by rewrite patchC // ?in_setC ?in_set1 ?lt_eqF //; apply cont_f.
- rewrite patchC // ?in_setC ?in_set1 ?lt_eqF//.
  apply: cvg_trans; last exact: cont_left_f.
  apply: (near_eq_cvg (f := f)).
  near=> t.
  by rewrite patchC // ?in_setC ?in_set1 ?lt_eqF.
- rewrite patch_in ?in_set1//.
  apply: cvg_trans; last by apply has_left_limit.
  apply: (near_eq_cvg (f := f)).
  near=> t.
  by rewrite patchC // in_setC in_set1.
 Unshelve. all: by end_near. Qed.

(* Local Notation safe_dist := (@safe_dist R n phi b c k u1 (r%:num / 2)%:pos rho). *)
Local Notation safe_dist_fwd := (@safe_dist R n phi b c u1 (r%:num / 2)%:pos k rho).
Local Notation safe_dist := (@safe_dist_sym R n phi a c u1 r k b).

Let bac : b \in `]a, c[%R.
Proof. by rewrite in_itv /= ab bc. Qed.

Let f_sym_at_b := cauchy_lipschitz_f_sym k0 cont1 lip2 bac.

Let f_sym_at_b_init : f_sym_at_b b = u1.
Proof. by apply cauchy_lipschitz_sym. Qed.

Let is_sol_oo_f_sym_at_b : is_sol_cauchy_oo phi (b - safe_dist) (b + safe_dist)
  (f_sym_at_b (b - safe_dist))(* initial state value*) f_sym_at_b.
Proof. exact: cauchy_lipschitz_sym_oo. Qed.

(* extends f_sym_at_b with f_ext_bu1 on [a,b] *)
Definition sol_extended := patch f_sym_at_b `[a, b] f_ext_bu1.

Lemma sol_extended_continuous : {within `[a, b + safe_dist], continuous sol_extended}.
Proof.
apply: (within_continuous_patch (ltW ab)) => //.
- by rewrite lerDl ltW// safe_dist_sym_gt0.
- by have [_ [_ +]] := is_sol_oo_f_ext_bu1; rewrite closure_itvoo.
- have [_ [_ +]] := is_sol_oo_f_sym_at_b.
  apply/continuous_subspaceW.
  rewrite closure_itvoo ?ler_ltD ?gtrN ?safe_dist_sym_gt0 //.
  apply: subset_itvr.
  by rewrite bnd_simp gerBl ltW // safe_dist_sym_gt0.
- by rewrite /f_ext_bu1 patch_in ?in_set1.
Qed.

Let sol_extended_init : sol_extended a = u0.
Proof.
rewrite /sol_extended /f_ext_bu1 patch_in ?patchC ?in_setC ?in_set1 ?lt_eqF //.
by rewrite inE/= bound_itvE ltW.
Qed.

Let sol_extended_near_b : {near b, f_sym_at_b =1 sol_extended}.
Proof.
near=>t.
rewrite /sol_extended /patch.
case: ifP => // /[dup] tab.
rewrite inE /= in_itv/= => -/andP[_ tb].
have := is_sol_oo_f_ext_bu1.
have <- : f_ext_bu1 a = u0 by apply is_sol_oo_f_ext_bu1.
move /(is_sol_cauchy_ooN _ _ (ltW ab)) => hext0.
rewrite /f_sym_at_b cauchy_lipschitz_sym_left /=; last first.
  have -> : f_ext_bu1 t = (f_ext_bu1 \o -%R) (-t) by rewrite /= opprK.
  apply: cauchy_lipschitz_unique.
    have <- : (f_ext_bu1 \o -%R) (- b) = u1.
      by rewrite /= opprK /f_ext_bu1 patch_in //= in_set1.
    apply /is_sol_cauchy_oo_subset/hext0=>//.
    by rewrite -lerBDl; exact: safe_dist_itv.
  rewrite oppr_itv/= opprD !opprK in_itv/= tb andbT.
  apply ltW.
  near: t; apply: lt_nbhsr.
  by rewrite gtrBl safe_dist_gt0 // ltrN2.
rewrite in_itv/= tb andbT ltW//=.
near: t; apply: lt_nbhsr.
by rewrite gtrBl safe_dist_sym_gt0 // ltrN2.
Unshelve. all: by end_near. Qed.

Lemma is_sol_cauchy_oo_sol_extended :
  is_sol_cauchy_oo phi a (b + safe_dist) u0 sol_extended.
Proof.
split; first by [].
split; last first.
  rewrite closure_itvoo ?(lt_trans ab) // ?ltrDl ?safe_dist_sym_gt0//.
  by apply sol_extended_continuous.
move => x xab.
have := xab.
rewrite in_itv/= => /andP[xa _].
case: (ltgtP x b) => Hxb.
- have xab' : x \in `]a,b[%R.
    by rewrite /=in_itv/=;apply /andP;split.
  split.
    apply: (near_eq_derivable (f := f)).
      near=> x0.
      rewrite /sol_extended patch_in /f_ext_bu1 ?patchC// ?in_setC ?in_set1 ?lt_eqF//; last first.
        by near: x0; exact: lt_nbhsl.
      rewrite inE/= in_itv/=; apply/andP; split; rewrite ltW//.
        by near: x0; exact: lt_nbhsr.
      by near: x0; exact: lt_nbhsl.
    by apply sol_is_deriv_f; rewrite in_itv/= xa.
  rewrite derive1E.
  rewrite (near_eq_derive (g := f)); last first.
    rewrite -derive1E.
    rewrite /sol_extended patch_in /f_ext_bu1 ?patchC// ?in_setC ?in_set1 ?lt_eqF//; last first.
      by apply sol_is_deriv_f.
    by rewrite inE; apply: subset_itv_oo_cc.
  near=>x0.
  rewrite /sol_extended patch_in /f_ext_bu1 ?patchC// ?in_setC ?in_set1 ?lt_eqF//.
    rewrite inE/=in_itv/=; apply/andP; split; rewrite ltW//.
      by near: x0; exact: lt_nbhsr.
    by near: x0; exact: lt_nbhsl.
  by near: x0; exact: lt_nbhsl.
- split.
    apply: (near_eq_derivable (f := f_sym_at_b)).
      near=> x0.
      rewrite /sol_extended ?patchC// ?in_setC ?notin_setE ?inE /= ?in_itv /= .
      rewrite !leNgt; apply/negP; rewrite negb_and; apply/orP; right; apply/negPn.
      by near: x0; exact: lt_nbhsr.
    have [_ [+ _]]:= is_sol_oo_f_sym_at_b.
    move /(_ x) => []//.
    move : xab; rewrite !in_itv/= => /andP[_ ->].
    rewrite andbT.
    apply /lt_trans/Hxb.
    by rewrite gtrBl safe_dist_sym_gt0.
  rewrite derive1E.
  rewrite (near_eq_derive (g := f_sym_at_b)); last first.
    rewrite -derive1E.
    rewrite /sol_extended ?patchC// ?in_setC ?notin_setE ?inE /= ?in_itv /=; last first.
      apply is_sol_oo_f_sym_at_b.
      move: xab.
      rewrite !in_itv/= => /andP[_ ->].
      rewrite andbT.
      apply /lt_trans/Hxb.
      by rewrite gtrBl safe_dist_sym_gt0.
    by rewrite !leNgt; apply/negP; rewrite negb_and; apply/orP; right; apply/negPn.
  near=>x0.
  rewrite /sol_extended ?patchC// ?in_setC ?notin_setE ?inE /= ?in_itv /= .
  rewrite !leNgt;apply /negP; rewrite negb_and;apply /orP;right;apply /negPn.
  by near:x0; apply: lt_nbhsr.
- rewrite Hxb.
  split.
  apply: (near_eq_derivable (f := f_sym_at_b)).
  + exact: sol_extended_near_b.
  + have [_ [+ _]]:= is_sol_oo_f_sym_at_b.
    move /(_ b) => []//.
    rewrite in_itv/=; apply/andP; split.
      by rewrite gtrBl safe_dist_sym_gt0.
    by rewrite ltrDl safe_dist_sym_gt0.
  + rewrite {2}/sol_extended patch_in /f_ext_bu1 ?patch_in ?in_set1 //=; last first.
      rewrite -f_sym_at_b_init derive1E (near_eq_derive (g := f_sym_at_b)); last first.
        rewrite -derive1E.
        have [_ [+ _]]:= is_sol_oo_f_sym_at_b.
        move /(_ b) => []//.
        rewrite in_itv/=; apply/andP; split.
          by rewrite gtrBl safe_dist_sym_gt0.
        by rewrite ltrDl safe_dist_sym_gt0.
    near do symmetry.
    apply: sol_extended_near_b.
    by rewrite inE/= in_itv/= lexx//= andbT ltW.
Unshelve. all: by end_near. Qed.

End extend_solution.

(*
(* maybe not useful? *)
Section extend_from_lipschitz.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b c : R)
  (u0 : U) (sol : R -> U).

Hypothesis ab : a < b.
Hypothesis bc : b < c.

Hypothesis sol_oo :
  forall b', b' \in `[a, b[%R -> is_sol_cauchy_oo phi a b' u0 sol.

Variable k : R.
Hypothesis k0 : 0 < k.

Variable r : {posnum R}.
Let u1 : U := lim (sol @ b^'-).
Let B := closed_ball u1 r%:num.

Hypothesis cont1 :
  {in B, forall y, {within `[a, c], continuous phi ^~ y}}.

Hypothesis lip2 :
  {in `[a, c]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis sol_lip :
  {in `]a, b[%R &, forall s t, `| sol t - sol s | <= k * `|t - s|}.

Let has_left_limit : sol @ b^'- --> u1.
Proof.
rewrite /u1.
exact/(@lipschitz_has_left_limit _ _ a b k).
Qed.

Local Notation sol_extended := (sol_extended sol ab bc k0 cont1 lip2 ).
Local Notation safe_dist := (@safe_dist_sym R n phi a c u1 r k b).

Lemma solution_extends_from_lipschitz :
  is_sol_cauchy_oo phi a (b + safe_dist) u0 sol_extended.
Proof. by apply : is_sol_cauchy_oo_sol_extended. Qed.

End extend_from_lipschitz.
*)

Section extend_from_compact_containment.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b c : R)
  (u0 : U) (sol : R -> U).

Variable K : set U.

Hypothesis ab : a < b.
Hypothesis bc : b < c.

Hypothesis sol_oo :
  forall b', b' \in `[a, b[%R -> is_sol_cauchy_oo phi a b' u0 sol.

Hypothesis compactK : compact K.

Hypothesis solK : sol @` `[a, b[ `<=` K.

Hypothesis phi_loc_lip : forall y0, y0 \in K ->
  exists r k : {posnum R},
    {in closed_ball y0 r%:num, forall y, {within `[a, c], continuous phi ^~ y}} /\
    {in `[a, c]%R, forall t, k%:num.-lipschitz_(closed_ball y0 r%:num) (phi t)}.

(* should be derivable from the previous *)
Hypothesis phi_cont :
  {within `[a,c] `*` K,
    continuous (fun p : (R * U)%type => phi p.1 p.2)}.

Let u1 := lim (sol @ b^'-).

Lemma rhs_bounded_on_solution :
  bounded_set [set `| phi t (sol t) | | t in `[a, b[].
Proof.
suff [M [h1 h2]] :   bounded_set [set `| phi p.1 p.2 | | p in (`[a, c] `*` K)].
  exists M;split=>// x Mx /= x0 [t tab h].
  apply h2 => //.
  exists (t, sol t) => //=.
  split; first by move: tab; apply: subset_itvl; rewrite bnd_simp ltW.
  by apply solK.
apply compact_bounded.
apply continuous_compact;last by apply compact_setX => //; exact: segment_compact.
apply : within_continuous_comp.
  by move=> ? ?; apply: norm_continuous.
simpl.
exact: phi_cont.
Qed.

Lemma sol_is_lipschitz : exists2 M, 0 < M &
  {in `]a, b[%R &, forall s t, `|sol t - sol s| <= M * `|t - s|}.
Proof.
have [M [mr h]] := rhs_bounded_on_solution;exists (`| M|+1) => [ | s t asb tab].
  by rewrite ltr_wpDl.
wlog st : s t asb tab / s <= t.
  move => H.
  have [st|ts] := leP s t.
    exact: H.
  rewrite distrC (distrC t).
  apply H => //.
  by apply ltW.
set b' := t + (b - t) / 2.
have bb' : b' < b.
  rewrite /b' -ltrBrDl ltr_pdivrMr // mulr2n mulrDr mulr1 ltrDl subr_gt0.
  by rewrite (itvP tab).
have tb' : t < b'.
  rewrite /b' ltrDl divr_gt0 // subr_gt0.
  by rewrite (itvP tab).
have b'ab : b' \in `[a, b[%R.
  rewrite in_itv/= bb' andbT.
  move: tab.
  rewrite in_itv/= => /andP[/ltW + _].
  move/le_trans; apply.
  by rewrite ltW.
have atb' : t \in `]a, b'[%R.
  by move: tab; rewrite !in_itv/= tb' andbT => /andP[].
have sab' : s \in `]a, b'[%R.
  move: asb; rewrite !in_itv/= => /andP[-> _]/=.
  by apply (le_lt_trans st).
apply/bounded_derivative_lipschitz/atb'/sab'.
- by rewrite addr_ge0.
- have [_ [_ +]] := sol_oo b'ab.
  rewrite closure_itvoo//.
  apply/lt_trans/tb'.
  by rewrite (itvP atb').
move => x xab.
have [_ [+ _]] := sol_oo b'ab.
move /(_ _ xab) => [hd ->].
split=>//.
have MM' : M < `|M| + 1 by rewrite (le_lt_trans (ler_norm _))// ltrDl.
have := h _ MM' `|phi x (sol x)| .
rewrite /= normr_id; apply.
exists x => //.
by rewrite in_itv/= (itvP xab)/= (@lt_trans _ _ b')// (itvP xab).
Qed.

Lemma sol_has_left_limit : sol @ b^'- --> u1.
Proof.
rewrite /u1.
have [/= M M0 lip] := sol_is_lipschitz.
by apply/lipschitz_has_left_limit/lip.
Qed.

Lemma left_limit_in_K : u1 \in K.
Proof.
rewrite inE.
apply: closed_cvg sol_has_left_limit.
  exact: compact_closed.
near=> t.
apply solK => /=.
exists t => //.
rewrite in_itv/=; apply/andP; split.
  apply ltW; near: t.
  apply: cvg_at_left_filter; first by apply cvg_id.
  by apply: lt_nbhsr.
by near: t; exact: nbhs_left_lt.
Unshelve. all: by end_near. Qed.

Lemma solution_extends_from_compact :
  exists d : {posnum R}, exists2 sol' : R -> U,
    is_sol_cauchy_oo phi a (b + d%:num) u0 sol' &
    {in `[a, b[%R, sol =1 sol'}.
Proof.
have [r [k [cont1 lip2]]] := phi_loc_lip left_limit_in_K.
have k0 : 0 < k%:num by [].
exists (PosNum (safe_dist_sym_gt0 phi u1 r ab bc k0)).
exists (sol_extended sol ab bc k0 cont1 lip2).
  apply: is_sol_cauchy_oo_sol_extended => //.
  exact: sol_has_left_limit.
move=> t tab.
rewrite /sol_extended patch_in; first by rewrite inE; apply: subset_itv_co_cc.
by rewrite patchC // in_setC in_set1 /= lt_eqF // (itvP tab).
Qed.

End extend_from_compact_containment.

Section valid_right_endpoints.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a : R) (u0 : U).

Definition valid_right_endpoints :=
  [set b | b >= a /\ exists f, is_sol_cauchy_oo phi a b u0 f].

Lemma valid_right_endpoints_down b c : a <= b -> b <= c ->
  valid_right_endpoints c -> valid_right_endpoints b.
Proof.
move=> ab bc [ac [sol solp]]; split=> //.
exists sol.
have <- : sol a = u0 by apply solp.
exact/is_sol_cauchy_oo_subset/solp.
Qed.

End valid_right_endpoints.

Section max_solution.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a : R) (u0 : U).

Variable K : set U.
Hypothesis compactK : compact K.
Hypothesis u0K : u0 \in K.

(* Hypothesis solK : *)
(*   forall sol @` `[a, b[ `<=` K. *)


(* Hypothesis phi_loc_lip : *)
(*   forall y0,  *)
(*     exists r k : {posnum R},  *)
(*           (forall t, *)
(*          k%:num.-lipschitz_(closed_ball y0 r%:num) (phi t)) /\ *)
(*          {in closed_ball y0 r%:num, forall y, *)
(*             continuous (phi ^~ y)}. *)


(* Local Lemma phi_cont : *)
(*     continuous (fun p : (R * U)%type => phi p.1 p.2). *)
(* Proof. *)
(* move => [/= t0 y0]. *)
(* apply/cvg_ballP => eps eps0 /=. *)
(* have [r [k [Hlip Hcont]]] := phi_loc_lip y0. *)
(* have y0B : y0 \in closed_ball y0 r%:num by rewrite inE/=;apply closed_ballxx. *)
(* have e20 : 0 < eps / 2 by rewrite divr_gt0. *)
(* (* todo: improve proof *) *)
(* have c1 : *)
(*   \forall p \near (t0, y0), *)
(*     `| phi t0 y0 - phi p.1 y0 | < eps / 2. *)
(*   have /cvgrPdist_lt := Hcont y0 y0B t0. *)
(*   move => /(_ _ e20) [e0 e00 H]. *)
(*   exists (ball t0 e0 , [set: U]) => /=. *)
(*   split => //=. *)
(*   by apply: nbhsx_ballx. *)
(*   exact: filterT. *)
(*   move => [t1 t2] [b1 b2]. *)
(*   by apply: H. *)
(* have c2 : *)
(*   \forall p \near (t0, y0), *)
(*     `| phi p.1 y0 - phi p.1 p.2 | < eps / 2. *)
(*   near=>p. *)
(*   have  B0 : ((closed_ball y0 r%:num `*` closed_ball y0 r%:num) (y0, p.2)). *)
(*     split; first by apply closed_ballxx. *)
(*     near:p. *)
(*     exists ([set:R], ball y0 r%:num) => /=. *)
(*     split => //=. *)
(*     exact: filterT. *)
(*     by apply: nbhsx_ballx. *)
(*     move => [t1 t2] [b1 b2 /=]. *)
(*     by apply subset_closed_ball. *)
(*   move : (Hlip p.1 (y0, p.2) B0). *)
(*   move/le_lt_trans;apply. *)
(*   rewrite -ltr_pdivlMl//= mulrC. *)
(*   suff : ball y0 (eps/2/k%:num) p.2 by rewrite -ball_normE. *)
(*   near:p. *)
(*   exists ([set:R], ball y0 (eps/2/k%:num)) => /=. *)
(*   split => //=. *)
(*   exact: filterT. *)
(*   apply: nbhsx_ballx. *)
(*   by rewrite divr_gt0. *)
(*   move => [t1 t2] [b1 b2 /=]. *)
(*   exact b2. *)
(* near=> t. *)
(* rewrite -ball_normE/=. *)
(* rewrite -(subrKA (phi t.1 y0 ) (phi t0 y0)) (le_lt_trans (ler_normD _ _))  // (splitr eps) ltrD//. *)
(* by near:t;exact: c1. *)
(* by near:t;exact: c2. *)
(* Unshelve. all: end_near. Qed. *)

Hypothesis phi_continuous : forall y, continuous (phi ^~ y).

(* Hypothesis phi_cont : *)
(*   continuous (fun p : (R * U)%type => phi p.1 p.2). *)

Hypothesis phi_loc_lip :
  forall c, a < c -> forall y0,
    exists r k : {posnum R},
      {in `[a, c]%R, forall t,
        k%:num.-lipschitz_(closed_ball y0 r%:num) (phi t)}.

Local Lemma phi_local_conds c (ac : a < c) y0 :
  exists r k : {posnum R},
    {in closed_ball y0 r%:num, forall y,
      continuous (phi ^~ y)} /\
    {in `[a, c]%R, forall t,
      k%:num.-lipschitz_(closed_ball y0 r%:num) (phi t)}.
Proof.
have [r [k Hlip]] := @phi_loc_lip c ac y0.
exists r, k; split=> // y _.
Qed.

Local Lemma phi_cont c (ac : a < c) :
  {within `[a, c] `*` K,
    continuous (fun p : (R * U)%type => phi p.1 p.2)}.
Proof.
apply/subspace_continuousP => /=  [[t0 y0] [/= pD1 pD2]].
apply/cvgrPdist_lt => eps eps0 /=.
have [r [k [Hcont Hlip]]] := phi_local_conds ac y0.
have y0B : y0 \in closed_ball y0 r%:num by rewrite inE/=;apply closed_ballxx.
have e20 : 0 < eps / 2 by rewrite divr_gt0.
(* todo: improve proof *)
have c1 :
  \forall p \near (t0, y0),
    `| phi t0 y0 - phi p.1 y0 | < eps / 2.
  have /cvgrPdist_lt := Hcont y0 y0B t0.
  move => /(_ _ e20) [e0 e00 H].
  exists (ball t0 e0 , [set: U]) => /=.
  split => //=.
  by apply: nbhsx_ballx.
  exact: filterT.
  move => [t1 t2] [b1 b2].
  by apply: H.
have c2 :
  \forall p \near within (`[a, c] `*` K) (nbhs (t0, y0)),
      `|phi p.1 y0 - phi p.1 p.2| < eps / 2.
  rewrite near_withinE; near=> p => ptD.
  have  B0 : ((closed_ball y0 r%:num `*` closed_ball y0 r%:num) (y0, p.2)).
    split; first by apply closed_ballxx.
    near: p.
    exists ([set: R], ball y0 r%:num) => /=.
      split => //=.
        exact: filterT.
      by apply: nbhsx_ballx.
    move => [t1 t2] [b1 b2 /=].
    by apply subset_closed_ball.
  move: (Hlip p.1 ptD.1 (y0, p.2) B0).
  move/le_lt_trans;apply.
  rewrite -ltr_pdivlMl//= mulrC.
  suff : ball y0 (eps/2/k%:num) p.2 by rewrite -ball_normE.
  near:p.
  exists ([set:R], ball y0 (eps/2/k%:num)) => /=.
    split => //=.
      exact: filterT.
    apply: nbhsx_ballx.
    by rewrite divr_gt0.
  move => [t1 t2] [b1 + /=].
  exact.
near=> t.
rewrite -(subrKA (phi t.1 y0 ) (phi t0 y0)) (le_lt_trans (ler_normD _ _))// (splitr eps) ltrD//.
by near: t; rewrite near_withinE; exact: filterS c1.
by near: t; exact: c2.
Unshelve. all: end_near. Qed.

Let rho : {posnum R} := 2^-1%:pos.

Let rho1 : rho%:num < 1.
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Local Lemma valid_right_endpoints_ex :
  exists2 x, valid_right_endpoints phi a u0 x & a < x.
Proof.
have a1 : a < a + 1 by rewrite ltrDl.
have [r [k [c1 l2]]] := phi_local_conds a1 u0.
pose B := closed_ball u0 r%:num.
have lip2 : {in `[a, a + 1]%R, forall x, k%:num.-lipschitz_B (phi x)} by [].
have cont1 : {in B, forall y : 'rV_n, {within `[a, a + 1], continuous phi^~ y}}.
  by move=> x xb; apply: continuous_subspaceT; exact: c1.
exists (a + safe_dist phi a (a + 1) u0 (r%:num / 2) k%:num rho%:num); last first.
  by rewrite ltDl_safe_dist.
split; first by rewrite leDl_safe_dist// ltW.
exists (cauchy_lipschitz_f (ltW a1) (ge0 k) lip2 cont1 rho1).
exact: is_sol_cauchy_lipschitz_f.
Qed.

Local Lemma valid_right_endpoints_nonempty :
  valid_right_endpoints phi a u0 !=set0.
Proof.
have [x [bx ax]]:= valid_right_endpoints_ex.
by exists x.
Qed.

Local Lemma lt_sup_valid_right_endpoints :
  has_sup (valid_right_endpoints phi a u0) ->
  a < sup (valid_right_endpoints phi a u0).
Proof.
move => h.
have [x bx ax] := valid_right_endpoints_ex.
by rewrite (lt_le_trans ax)// sup_upper_bound.
Qed.

Local Lemma empty_itv_is_sol_cauchy sol b : b <= a -> sol a = u0 ->
  is_sol_cauchy_oo phi a b u0 sol.
Proof.
move => ba sol0; split; first by [].
split.
  move => t; rewrite in_itv/= => /andP[ta tb].
  by have := lt_trans ta tb; rewrite ltNge ba.
rewrite set_itv_ge; first by rewrite -leNgt bnd_simp.
by rewrite closure0; exact: continuous_subspace0.
Qed.

Lemma solt_eq sol1 sol2 b : a < b ->
  {in `[a,b], sol1 =1 sol2} -> is_sol_cauchy_oo phi a b u0 sol1 ->
  is_sol_cauchy_oo phi a b u0 sol2.
Proof.
move => ab hs [init [solp1 solp2]].
split.
- rewrite -init.
  apply /esym.
  apply hs.
  by rewrite inE/= bound_itvE ltW.
- split.
    move=>t tab.
    split.
    + apply/near_eq_derivable/(solp1 _ tab).1 => //.
      near=>t'.
      apply hs.
      rewrite inE/=.
      apply: subset_itv_oo_cc.
      near:t'.
      by apply: near_in_itvoo.
    + have hs':  {in `]a, b[%R, sol1 =1 sol2}.
        move => t' tab'.
        apply hs.
        rewrite inE.
        by apply: subset_itv_oo_cc.
      rewrite -hs'//.
      rewrite -[LHS](@in_eq_derive1 _ _ `]a, b[ sol1) //.
      * by move=> x; rewrite inE; exact: hs'.
      * by rewrite inE.
      * by apply solp1.
  apply: subspace_eq_continuous solp2.
  by rewrite closure_itvoo.
Unshelve. all: by end_near. Qed.

Lemma all_sols_global_sol :
  (forall b, exists sol, is_sol_cauchy_oo phi a b u0 sol) ->
  exists sol, is_sol_cauchy phi a +oo%O u0 sol.
Proof.
move => H.
have [solt soltp] := (choice H).
exists (fun t => solt (t + 1) t).
apply/is_sol_cauchy_inftyP => b /=.
have [ab | ba]:= ltP a b; last first.
  split; first by apply soltp.
  split.
    move => t.
    rewrite in_itv/= => /andP[h1 h2].
    have h3:= lt_trans h1 h2.
    have := le_lt_trans ba h3.
    by rewrite ltxx.
  rewrite set_itv_ge; first by rewrite -leNgt bnd_simp.
  rewrite closure0.
  exact: continuous_subspace0.
suff heq : {in `[a,b],  solt b =1 (fun t => solt (t+1) t) }.
  by apply (solt_eq ab heq).
move => t tab.
have at1 : a < t + 1.
  rewrite inE in tab.
  by rewrite (@le_lt_trans _ _ t)// ?(itvP tab)// ltrDl.
suff -> : solt b t = solt (maxr (t + 1) b) t.
- apply: (locally_cauchy_lipschitz_unique  at1 _ (u0 := u0)).
  + have <- : solt (maxr (t + 1) b) a = u0.
      by apply (soltp (maxr (t + 1) b)).
    apply /is_sol_cauchy_oo_subset/(soltp _) => //=.
    by rewrite le_max lexx.
  + done.
    move => t0 at0 t0t.
    have [r [k [c1 l1]]] := phi_local_conds at1 (solt (maxr (t + 1) b) t0).
    exists r, k => t' at'; split => //=.
      exact: l1 t' at'.
    by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
  + rewrite inE in tab.
    by rewrite in_itv/= (itvP tab) lerDl/=.
apply: (locally_cauchy_lipschitz_unique  ab (u0 := u0)) => /=.
- exact: soltp.
- have <- : solt (maxr (t + 1) b) a = u0.
    by apply (soltp (maxr (t + 1) b)).
  apply/is_sol_cauchy_oo_subset/(soltp _) => //=.
  by rewrite le_max lexx orbT.
- move => t0 at0 t0t.
  have [r [k [c1 l1]]] := phi_local_conds ab (solt b t0).
  exists r, k => t' at'; split => /=.
    exact: l1 t' at'.
  by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
by move: tab; rewrite inE.
Qed.

Lemma max_sol : has_sup (valid_right_endpoints phi a u0) ->
  exists sol, forall b, b < sup (valid_right_endpoints phi a u0) -> is_sol_cauchy_oo phi a b u0 sol.
Proof.
move => hs.
have /choice[solt soltp] :
    forall b, exists sol, b < sup (valid_right_endpoints phi a u0) -> is_sol_cauchy_oo phi a b u0 sol.
  move => b.
  have [ab0 | ba0]:= ltP a b; last first.
    exists (cst u0).
    move => h.
    exact: empty_itv_is_sol_cauchy.
  suff : b < sup (valid_right_endpoints phi a u0) -> valid_right_endpoints phi a u0 b.
    have [ba | ab] := ltP b (sup (valid_right_endpoints phi a u0)).
    by move => []//h [f pf];exists f.
    by move => _; exists (cst u0).
  move=>hb.
  have [c bc1 bc2] := sup_gt valid_right_endpoints_nonempty hb.
  by apply: valid_right_endpoints_down bc1; exact: ltW.
set r := fun t => (t + (sup (valid_right_endpoints phi a u0) - t) / 2).
have rsup : forall t, t < sup (valid_right_endpoints phi a u0) -> r t < sup (valid_right_endpoints phi a u0).
  by move => t ts;rewrite -ltrBrDl ltr_pdivrMr ?ltr0n ?mulr2n // mulrDr mulr1 ltrDl subr_gt0.
have rt : forall t, t < sup (valid_right_endpoints phi a u0) -> t < r t.
  by move => t ts;rewrite /r ltrDl ltr_pdivlMr // mul0r subr_gt0.
have solt0 x :  x < sup (valid_right_endpoints phi a u0) -> (solt x a) = u0 by move /(soltp _) => [+ _].
exists (fun t => solt (r t) t).
move => b /= bs.
have [ab | ba]:= ltP a b; last first.
  split; first by apply soltp;apply rsup;apply: lt_sup_valid_right_endpoints.
  apply empty_itv_is_sol_cauchy => //.
  apply solt0 => //.
  by apply rsup;apply lt_sup_valid_right_endpoints.
suff heq : {in `[a,b],  solt b =1 (fun t => solt (r t) t) }.
  by apply: (solt_eq ab heq);apply soltp.
move => t tab.
have tsup : t < sup (valid_right_endpoints phi a u0).
  apply/le_lt_trans/bs.
  by move : tab; rewrite inE/=in_itv/= => /andP[].
have art : a < r t.
  apply /le_lt_trans/rt => //.
  by move : tab; rewrite inE/=in_itv/= => /andP[].
suff -> : solt b t = solt (maxr (r t) b) t.
  apply: (locally_cauchy_lipschitz_unique  (phi:=phi) art _ (u0 := (solt (maxr (r t) b) a))) => /=.
    apply /is_sol_cauchy_oo_subset/(soltp _) => //=.
      by rewrite le_max lexx.
      by rewrite gt_max bs andbT rsup//.
    rewrite solt0.
    by rewrite gt_max rsup.
    by apply: soltp; apply rsup.
    move => t0 at0 t0t.
    have [r0 [k [c1 l1]]] := phi_local_conds art (solt (maxr (r t) b) t0).
    exists r0, k => t' at'; split => //=.
    exact: l1 t' at'.
    by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
    move : tab.
    rewrite inE/=!in_itv/=  => /andP[-> _].
    by apply ltW; apply rt.
apply: (locally_cauchy_lipschitz_unique  (phi:=phi) ab _ (u0 := u0)) => /=.
- by apply soltp.
- rewrite -(solt0 (maxr (r t) b)).
  by rewrite gt_max rsup //=.
- apply /is_sol_cauchy_oo_subset/(soltp _) => //=.
    by rewrite le_max lexx;apply /orP;right.
  by rewrite gt_max bs andbT rsup//.
- move => t0 at0 t0t.
  have [r0 [k [c1 l1]]] := phi_local_conds ab (solt b t0).
  exists r0, k => t' at'; split => //=.
    exact: l1 t' at'.
  by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
- by move: tab; rewrite inE.
Qed.

Lemma no_ub_global_sol : ~ has_ubound (valid_right_endpoints phi a u0) ->
  exists sol, is_sol_cauchy phi a +oo%O u0 sol.
Proof.
move => h.
apply all_sols_global_sol.
move : h.
apply: contra_notP.
rewrite -existsNE.
case => M Mh.
have aM : a < M.
  move : Mh.
  apply: contra_notP.
  move => /negP;rewrite -leNgt.
  move => Ma.
  exists (cst u0).
  split=>//.
  split.
    move => t.
    rewrite in_itv/=.
    move=> /andP[at0 tM].
    by have := lt_trans at0 tM; rewrite ltNge Ma.
  suff -> : `]a, M[ = set0 by rewrite closure0; apply: continuous_subspace0.
  by rewrite set_itv_ge// bnd_simp -leNgt.
exists M.
move => x [ax [sol solp]].
move : Mh.
apply: contra_notP.
rewrite leNgt => /negP/negPn h.
exists sol.
have <- :  sol a = u0 by apply solp.
apply /is_sol_cauchy_oo_subset/solp => //.
by rewrite ltW.
Qed.

Lemma compact_containment_no_sup :
  (forall b sol, is_sol_cauchy_oo phi a b u0 sol -> sol @` `[a, b[ `<=` K) ->
  ~ has_sup (valid_right_endpoints phi a u0).
Proof.
move => H Hsup.
have [sol Hsol] := max_sol Hsup.
suff [d [sol' H1 _]] : exists (d : {posnum R}), exists2 sol' : R -> 'rV_n,
     is_sol_cauchy_oo phi a (sup (valid_right_endpoints phi a u0) + d%:num) u0 sol' &
     {in `[a, sup (valid_right_endpoints phi a u0)[%R, sol =1 sol'}.
  have Hb : valid_right_endpoints phi a u0 (sup (valid_right_endpoints phi a u0) + d%:num).
    split; last by exists sol'.
    by rewrite ltW// (lt_le_trans  (lt_sup_valid_right_endpoints Hsup))// lerDl.
  have := sup_upper_bound Hsup Hb.
  by apply/negP;rewrite -ltNge ltrDl.
apply: (solution_extends_from_compact (c := sup (valid_right_endpoints phi a u0) + 1) (K:=K)) => /=.
- exact: lt_sup_valid_right_endpoints.
- by rewrite ltrDl.
- by move => b'; rewrite in_itv/= => /andP[_ b'lt];apply Hsol.
- exact: compactK.
- move => _ [x /= + <-].
  rewrite in_itv/= => /andP[ha hb].
  apply: (H ((x + sup (valid_right_endpoints phi a u0)) / 2) sol).
    by apply Hsol;rewrite ltr_pdivrMr // mulr2n mulrDr mulr1 ltrD2r.
  exists x => //=.
  by rewrite in_itv/=ha/=ltr_pdivlMr // mulr2n mulrDr mulr1 ltrD2l.
- move =>  y Ky.
  have ac : a < sup (valid_right_endpoints phi a u0) + 1.
    apply: lt_trans; first exact: lt_sup_valid_right_endpoints Hsup.
    by rewrite ltrDl.
  have [r [k [hrk1 hrk2]]] := phi_local_conds ac y.
  exists r,k; split => //= y0 Hy0.
  apply: continuous_subspaceT.
  by apply hrk1.
- apply: phi_cont.
  rewrite ltr_pDr//.
  exact: lt_sup_valid_right_endpoints.
Qed.

(* Thm 3.3 in Khalil *)
Lemma compact_containment_global_is_sol_cauchy :
  (forall b f, is_sol_cauchy_oo phi a b u0 f -> f @` `[a, b[ `<=` K) ->
  exists2 f, is_sol_cauchy phi a +oo%O u0 f &
    (h^-1 *: (f (a + h) - f a)) @[h --> 0^'+] --> phi a (f a).
Proof.
move=> is_sol_K.
have [f [init [sol_is_deriv_f cont]]] : exists f, is_sol_cauchy phi a +oo%O u0 f.
  apply: no_ub_global_sol.
  suff : ~ has_sup (valid_right_endpoints phi a u0).
    by apply contra_not => hub; split=>//; exact: valid_right_endpoints_nonempty.
  exact: compact_containment_no_sup.
have allsol : forall b, is_sol_cauchy_oo phi a b u0 f.
   exact/is_sol_cauchy_inftyP.
exists f => //.
apply/cvgrPdist_le => eps eps0.
move: cont; rewrite closure_neitv_oy => /[dup] cont.
move/continuous_within_itvcyP => [_ cr].
have : a < a + 1 by rewrite ltrDl.
move=> /phi_cont /subspace_continuousP Hj.
have pa : (`[a, a + 1] `*` K) (a, f a).
  split; first by rewrite /= bound_itvE ltW ?ltrDl.
  by rewrite init; move/set_mem: u0K.
have ca : x @[x --> a^'+] --> a.
  move=> S [e /= e0 Be].
  exists e => // x0 bx0 _.
  exact: Be.
have pair_cvg : (fun t => (t, f t)) @ a^'+ --> (a, f a).
  exact: cvg_pair ca cr.
have hphi : phi t (f t) @[t --> a^'+] --> phi a (f a).
  apply/cvgrPdist_le => e e0.
  have /cvgrPdist_le /(_ _ e0) := Hj (a, f a) pa.
  rewrite near_withinE => /pair_cvg Hcomp.
  have Hdomain : \forall t \near a^'+,(`[a, a + 1] `*` K) (t, f t).
    near=> t; split.
      apply/andP; split.
        by near: t; exact: nbhs_right_ge.
      by near: t; apply: nbhs_right_le; rewrite ltrDl.
    apply: (is_sol_K (a + 2) f) => //; exists t => //.
    apply/andP; split.
      by near: t; exact: nbhs_right_ge.
    by near: t; apply: nbhs_right_lt; rewrite ltrDl.
  by move: Hcomp Hdomain; apply: filter_app.
have ? : 0 < eps / 2 by rewrite !divr_gt0.
move/cvgrPdist_le : hphi.
have : 0 < eps / 2 / 2 by rewrite !divr_gt0.
move=> /[swap] /[apply] => /nbhs_right0P hphi.
have [e e0 he] : exists2 e, 0 < e & forall e', e' < e -> 0 < e' ->
    `|phi a (f a) - phi (a + e') (f (a + e'))| <= eps / 2 / 2.
  move : hphi.
  rewrite nearE => -[e e0 ep].
  exists e => //= e' e'e e'0.
  apply ep => //=.
  by rewrite sub0r normrN gtr0_norm.
near=> h.
rewrite -(subrKA (phi (a+h) (f (a+h)))) (le_trans  (ler_normD _ _))//.
rewrite (splitr eps) lerD//.
   apply: (le_trans (he _ _ _)) => //.
   by rewrite ler_piMr ?invf_le1 ?ler1n// divr_ge0// ltW.
rewrite -(@ler_pM2l _ h)// -{1}(@gtr0_norm _ h)// -normrZ scalerBr scalerA.
rewrite divff// scale1r distrC.
rewrite /Num.norm/= !mx_normrE.
apply/bigmax_leP; split; first by rewrite ltW// mulr_gt0.
move=> /= [i j] _/=.
rewrite {i}ord1.
pose g t := (f t - f a - (t - a) *: phi (a + h) (f (a + h))) 0 j.
suff : `|g (a + h)| <= h * (eps / 2).
  by rewrite /g; apply le_trans; rewrite -(addrA a) subrKC.
have ah: a < a + h by rewrite ltrDl.
have fa0 : g a = 0 by rewrite /g !subrr scale0r subrr mxE.
have df x : x \in `]a, a + h[%R ->
    is_derive x 1 g ((phi x (f x) - phi (a + h) (f (a + h))) 0 j).
  move => xah.
  rewrite /g !mxE.
  under eq_fun do rewrite !mxE.
  apply: is_deriveB.
    rewrite -(subr0 (phi _ _)) !mxE.
    rewrite (_ : (fun x0 => _) = (fun x0 => f x0 0 j) - cst (f a 0 j)).
      exact/funext.
    have : is_derive x 1 (cst (f a 0 j)) 0 by exact: is_derive_cst.
    have : is_derive x 1 (fun x0 => f x0 0 j) (phi x (f x) 0 j).
      have [| deri1 d1] := sol_is_deriv_f x.
        by move : xah; rewrite !in_itv/= => /andP[-> _].
      have /derivable_mxP deri1' := deri1.
      split => //.
      have := d1.
      rewrite derive1E !derive_mx//=.
      move=> /rowP /(_ j).
      by rewrite mxE.
    exact: is_deriveB.
  under eq_fun do rewrite mulrBl.
  rewrite -{3}(subr0 (phi (a + h) _)) !mxE.
  apply: is_deriveB; last exact: is_derive_cst.
  set c := phi _ _  _ _.
  have {2}-> : c = x *: 0 + c *: 1 by rewrite scaler0 scaler1 add0r.
  exact: is_deriveM.
have [| c cah] := MVT ah df.
  rewrite /g.
  suff /within_continuous_coord :
    {within `[a, a + h], continuous fun t  => (f t - f a - (t - a) *: phi (a + h) (f (a + h)))}.
    by [].
  apply: within_continuousB => /=.
    apply: within_continuousB.
      apply/continuous_subspaceW/cont.
      exact: subset_itvl.
    exact/continuous_subspaceT/cst_continuous.
  under [X in {within _, continuous X}] eq_fun do rewrite scalerBl.
  apply: within_continuousB.
    exact/continuous_subspaceT/scalel_continuous.
  exact/continuous_subspaceT/cst_continuous.
rewrite -(addrA a) subrKC fa0 subr0 => ->.
rewrite mulrC normrM gtr0_norm// ler_pM//.
suff: `|phi c (f c) - phi (a + h) (f (a + h))| <= eps / 2.
  apply/le_trans.
  rewrite {2}/Num.norm/= !mx_normrE.
  exact: le_bigmax (ord0, _).
rewrite -(subrKA (phi a (f a))) (le_trans  (ler_normD _ _))//.
rewrite (splitr (eps / 2)) lerD//.
  rewrite distrC.
  have -> : c = a + (c - a) by ring.
  apply: he => //.
    apply (@lt_trans _ _ h) => //.
    by rewrite ltrBlDl (itvP cah).
  by rewrite subr_gt0 (itvP cah).
exact: he.
Unshelve. all: by end_near. Qed.

End max_solution.

Section compact_global_solution.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a : R) (u0 : U)
  (K : set U).

Hypothesis compactK : compact K.
Hypothesis u0K : u0 \in K.

Hypothesis phi_continuous : forall x, continuous (phi ^~ x).

Hypothesis phi_locally_lipschitz : forall b, a < b ->
  forall x, exists r k : {posnum R},
    {in `[a, b]%R, forall t, k%:num.-lipschitz_(closed_ball x r%:num) (phi t)}.

Hypothesis solutions_in_K : forall b sol,
  is_sol_cauchy_oo phi a b u0 sol -> sol @` `[a, b[ `<=` K.

Theorem compact_global_solution : exists2 sol,
  is_sol_cauchy phi a +oo%O u0 sol &
  (h^-1 *: (sol (a + h) - sol a)) @[h --> 0^'+] --> phi a (sol a).
Proof. exact: (compact_containment_global_is_sol_cauchy (K:=K)). Qed.

Lemma global_solution_unique f f' :
  is_sol_cauchy phi a +oo%O u0 f ->
  is_sol_cauchy phi a +oo%O u0 f' ->
  {in `[a, +oo[%R, f =1 f'}.
Proof.
move=> /is_sol_cauchy_inftyP h1 /is_sol_cauchy_inftyP h2 t tp.
apply: (@locally_cauchy_lipschitz_unique _ _ phi a (t + 1) u0) => //.
- by rewrite ltr_pwDr// (itvP tp).
- move => t0 at0 tt0.
  have at1 : a < t+1 by apply (le_lt_trans at0).
  have [r [k H]] := phi_locally_lipschitz at1 (f t0).
  exists r, k => t' at'.
  split; first by apply H; rewrite in_itv/=.
  move => y Hy.
  apply: continuous_subspaceT.
  exact: phi_continuous.
- by rewrite in_itv/= (itvP tp) lerDl ler01.
Qed.

End compact_global_solution.

(* Theorem 3.4 from Khalil (p. 96),
   specialized to g := 0,
   TODO: generalize *)
Section thm34.
Context {R : realType} {n : nat} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (k : R).
Let psi : R -> U -> U := cst 0.
Variables (u0 v0 : U) (r : {posnum R}) (*(r1 : r%:num < 1)*).

Hypothesis ab : a < b.
(* TODO: there seems to be no reason to have B being a closed ball
around u0 whereas the proof talks about an open W*)
Let B : set U := closed_ball u0 r%:num. (* open connected set? *)
Hypothesis (k0 : 0 < k)
  (lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)})
  (cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}).
Variables y z : R -> U.
Hypothesis soly : is_sol_cauchy_oo phi a b u0 y.
Hypothesis solz : is_sol_cauchy_oo (phi \+ psi) a b v0 z.
Hypothesis By : y @` `[a, b] `<=` B.
Hypothesis Bz : z @` `[a, b] `<=` B.
Variable mu : R.
Hypothesis mu_ub : forall t x, t \in `[a, b] -> x \in B ->
 `| psi t x | <= mu.

Let lm := @lebesgue_measure R.

Let mu0 : 0 <= mu.
Proof.
apply/le_trans/(@mu_ub a u0).
  exact: normr_ge0.
  by rewrite inE/=in_itv/= lexx ltW.
rewrite /B inE.
exact: closed_ballxx.
Qed.

Let gamma := `|u0 - v0|.

Lemma thm34 t : t \in `[a, b] ->
  `|y t - z t| <= gamma * expR (k * (t - a)) + mu/ k * (expR (k * (t - a)) - 1).
Proof.
move=> tab.
have k_neq0 : k != 0 by rewrite gt_eqF.
have yint t' : t' \in `[a, b]%R -> y t' = u0 + \vint[lm]_(s in `[a, t']) phi s (y s).
  move=> t'ab.
  suff: is_sol_integral phi a b u0 y by move=> [<-]; apply.
  apply/(@is_sol_cauchy_integral _ _ _ _ _ _ u0 r k) => //.
  case: soly => _ [_].
  by rewrite closure_itvoo. (* where we use By *)
have zint t' : t' \in `[a, b]%R ->
    z t' = v0 + \vint[lm]_(s in `[a, t']) (phi s (z s) + psi s (z s)).
  move=> t'ab.
  suff : is_sol_integral (phi \+ psi) a b v0 z by move=> [-> ->].
  apply/(@is_sol_cauchy_integral _ _ _ _ _ _ u0 r k).
  - move=> x xab.
    rewrite (_ : phi \+ psi = phi); first by apply/funext => s; rewrite /= addr0.
    exact: cont1.
  - move=> x xab.
    rewrite (_ : phi \+ psi = phi); first by apply/funext => s; rewrite /= addr0.
    exact: lip2.
  - case: solz => _ [_].
      by rewrite closure_itvoo.
    rewrite -/B.
    exact: Bz.
  - exact: solz.
pose gronwall_y t := `|y t - z t|.
rewrite -/(gronwall_y t).
have t'b t' : t' \in `[a,b] -> t' <= b.
  by rewrite inE/=in_itv/= => /andP[].
have contphiy j0 t'  : t' \in `[a,b] ->
    {within `[a,t'], continuous (fun x => (phi x (y x)) ord0 j0)}.
  move=> t'ab.
  apply: (@within_continuous_ODE _ _ _ _ _ u0 r k) => //.
  - move=> y0 y0b; apply/continuous_subspaceW/cont1 => //.
    by apply subset_itvl => //; exact: t'b.
  - move => t0 t0at; apply: lip2.
    by apply : subset_itv t0at => //; apply t'b.
  - have [_ [_ +]] := soly.
    apply: continuous_subspaceW.
    by rewrite closure_itvoo //; apply: subset_itvl => //; apply t'b.
  - move => x [y0 By0 <-].
    apply By.
    exists y0 => //.
    by apply: subset_itv By0 => //; apply t'b.
have contphiz j0 t' : t' \in `[a,b] ->
    {within `[a,t'], continuous (fun x => (phi x (z x)) ord0 j0)}.
  move => t'ab.
  apply: (@within_continuous_ODE _ _ _ _ _ u0 r k) => //.
  - move => y0 y0b; apply/continuous_subspaceW/cont1 => //.
    by apply subset_itvl => //; exact: t'b.
  - move => t0 t0at; apply: lip2.
    by apply : subset_itv t0at => //; exact: t'b.
  - have [_ [_ +]] := solz.
    apply: continuous_subspaceW.
    by rewrite closure_itvoo //; apply: subset_itvl => //; apply t'b.
  - move => x [y0 By0 <-].
    apply Bz.
    exists y0 => //.
    by apply : subset_itv By0 => //; exact: t'b.
have : gronwall_y t <= gamma + mu * (t - a) +
    \int[lm]_(s in `[a, t])
      (k * (gamma + mu * (s - a)) * expR (k * (t - s))).
  have H t' : t' \in `[a,b] ->  gronwall_y t' <= gamma + mu * (t' - a) +
      \int[lm]_(s in `[a, t']) (k * `|y s - z s|).
    move => t'ab.
    have contphiy' j0 : {within `[a,t'], continuous (fun x => (phi x (y x)) 0 j0)}.
      by apply contphiy.
    have contphiz' j0 : {within `[a,t'], continuous (fun x => (phi x (z x)) 0 j0)}.
      by apply contphiz.
    apply: (@le_trans _ _ (gamma +
      \int[lm]_(s in `[a, t']) `|phi s (y s) - phi s (z s)|)).
      rewrite /gronwall_y.
      rewrite yint//; first by rewrite inE in t'ab.
      rewrite zint//; first by rewrite inE in t'ab.
      under [in X in `|_ - X| <= _]eq_rowRintegral.
        move=> x xat.
        rewrite /psi/= addr0.
        over.
      rewrite /=.
      rewrite opprD.
      rewrite addrACA.
      rewrite (le_trans (ler_normD _ _))//.
      rewrite lerD2l// -/lm.
      rewrite [in leLHS]/Num.norm/= mx_normrE.
      apply/bigmax_le => /=.
        by apply : Rintegral_ge0 => ? _;apply normr_ge0.
      move=> [i j] _ /=.
      rewrite ord1{i}.
      rewrite !mxE.
      rewrite -RintegralB//=.
        by apply : continuous_compact_integrable; first exact: segment_compact.
        by apply : continuous_compact_integrable; first exact: segment_compact.
      apply: (le_trans (le_normr_Rintegral _ _)) => //=.
        rewrite /comp /=.
        under [X in _.-integrable _ X] eq_fun do rewrite EFinB.
        apply: integrableB => //.
        by apply : continuous_compact_integrable; first exact: segment_compact.
        by apply : continuous_compact_integrable; first exact: segment_compact.
      apply: le_Rintegral => //=.
        apply : continuous_compact_integrable; first exact: segment_compact.
        apply: within_continuous_comp_norm.
        apply : within_continuousB => //.
        apply : continuous_compact_integrable; first exact: segment_compact.
        apply: within_continuous_comp_norm.
        by apply: within_continuousB; exact/within_continuous_coord.
      move=> x xat.
      rewrite [in leRHS]/Num.norm/= mx_normrE.
      rewrite [X in `|X|](_ : _ = (phi x (y x) - phi x (z x)) 0 j).
        by rewrite !mxE.
      apply: (le_bigmax _ _ (ord0, j)).
      rewrite -addrA lerD2l.
      apply: ler_wpDl.
        apply: mulr_ge0 => //.
        by rewrite subr_ge0;move : t'ab; rewrite inE/=in_itv/= => /andP[].
     apply: le_Rintegral => //.
        apply : continuous_compact_integrable; first exact: segment_compact.
        apply: within_continuous_comp_norm.
        by apply : within_continuousB; apply /within_continuous_coord.
        apply : continuous_compact_integrable; first exact: segment_compact.
        apply : within_continuousMl.
        apply: within_continuous_comp_norm.
        apply : within_continuousB.
          have [_ [_ +]] := soly; apply: continuous_subspaceW.
          by rewrite closure_itvoo //; apply: subset_itvl => //; apply t'b.
          have [_ [_ +]] := solz; apply: continuous_subspaceW.
          by rewrite closure_itvoo //; apply: subset_itvl => //; apply t'b.
       move => x xat.
       have xab: x \in `[a,b]%R by apply: subset_itv xat => //; apply t'b.
       have := lip2 xab.
       move /(_ (y x, z x));apply.
       by split; [apply By | apply Bz]; exists x.
  pose lambda t := gamma + mu * (t - a).
  pose mu' (s : R) : R := k.
  have := @gronwall _ _ _ ab lambda mu' gronwall_y _ _ _ _ H t tab.
  rewrite /lambda/mu'/=/lm.
  rewrite -Rintegral_itvbo_itvbc => //.
    apply: (@integrableS _ _ _ lebesgue_measure `[a, t]%classic) => //=.
      exact: subset_itv_co_cc.
    apply : continuous_compact_integrable; first by apply segment_compact.
    apply: within_continuousM.
    apply : within_continuousMr.
    apply : within_continuousD; first exact: cst_continuous.
    apply: within_continuousMl.
    apply: within_continuousB; last exact: cst_continuous.
    apply: continuous_subspaceT => x; exact: cvg_id.
    apply: within_continuous_comp.
    by move=> x _; exact : continuous_expR.
    apply: parameterized_integralN_continuous.
      by rewrite inE in tab; rewrite (itvP tab).
    exact: cst_continuous.
  under eq_Rintegral.
    move => s sat.
    rewrite [ _ * k]mulrC.
    rewrite Rintegral_cst //= lebesgue_measure_itv/=.
   case: ifPn => //=; last first.
      rewrite lte_fin.
      by move: sat; rewrite inE => /itvP ->.
    over.
  rewrite Rintegral_itvbo_itvbc.
    apply: (@integrableS _ _ _ lebesgue_measure `[a, t]%classic) => //=.
      exact: subset_itv_co_cc.
    apply : continuous_compact_integrable; first exact: segment_compact.
    apply: within_continuousM.
    apply : within_continuousMl.
    apply : within_continuousD; first exact: cst_continuous.
    apply: within_continuousMl.
    apply: within_continuousB; last exact: cst_continuous.
    apply: continuous_subspaceT => x; exact: cvg_id.
    apply: within_continuous_comp.
    move => x _; exact: continuous_expR.
    apply: within_continuousMl.
    apply: within_continuousB; first exact: cst_continuous.
    by apply: continuous_subspaceT => x; exact: cvg_id.
  apply.
  apply: within_continuousD.
    exact: cst_continuous.
    apply: within_continuousMl.
    apply: within_continuousB; last exact: cst_continuous.
    by apply: continuous_subspaceT => x; exact: cvg_id.
  exact: cst_continuous.
  by move => _ _; exact: ltW.
  rewrite /gronwall_y.
  apply: within_continuous_comp_norm.
  apply: within_continuousB.
  have [_ [_ +]] := soly; apply: continuous_subspaceW.
  by rewrite closure_itvoo //; apply: subset_itvl => //; exact: t'b.
  have [_ [_ +]] := solz; apply: continuous_subspaceW.
  by rewrite closure_itvoo //; apply: subset_itvl => //; exact: t'b.
move/le_trans; apply.
apply: (@le_trans _ _
  (gamma + mu * (t - a) - gamma - mu * (t - a) +
    gamma * expR (k * (t - a)) +
    \int[lm]_(s in `[a, t]) (mu * expR (k * (t - s))))).
  rewrite -!addrA !lerD2l.
  move: (tab).
  rewrite inE/= in_itv/= => /andP[+ _].
  rewrite le_eqVlt => /predU1P[<-|altt].
    rewrite set_itv1 !Rintegral_set1 subrr !mulr0 expR0 mulr1 oppr0 add0r addr0.
    by rewrite addrC subrr.
  have -> := @Rintegration_by_parts _
    (fun s => (k * (gamma + mu * (s - a))))
    (fun s => - k^-1 * expR (k * (t - s)))
    (fun s => k * mu)
    (fun s => expR (k * (t - s))).
  - exact: altt.
  - apply: within_continuousMl.
    exact: cst_continuous.
  - split => //.
      apply: cvgM => //; apply: cvgD => //.
      apply: cvgM => //; apply: cvgD => //.
      exact: cvg_at_right_filter.
    apply: cvgM => //; apply: cvgD => //.
    apply: cvgM => //; apply: cvgD => //.
    exact: cvg_at_left_filter.
  - move=> x xat.
    by rewrite derive1E derive_val subr0 add0r mul1r scaler1.
  - apply: continuous_subspaceT.
    move=> x.
    apply: (@continuous_comp _ _ _ (fun s => k * (t - s)) expR); last exact: continuous_expR.
    apply: cvgM => //.
    by apply: cvgD => //; exact: cvgN.
  - split => //.
      apply: cvgM => //.
      apply: cvg_at_right_filter.
      apply: continuous_comp; last exact: continuous_expR.
      by apply: cvgM => //; exact: cvgB.
    apply: cvgM => //.
    apply: cvg_at_left_filter.
    apply: continuous_comp; last exact: continuous_expR.
    by apply: cvgM => //; exact: cvgB.
  - move=> x xat.
    rewrite derive1E derive_val add0r mul1r.
    rewrite -mulr_algl scaler1.
    rewrite mulrCA mulrC !mulrA.
    by rewrite mulNr (mulrC k^-1) divff// mulrNN !mul1r.
  rewrite !subrr !mulr0 addr0 expR0 mulr1.
  rewrite mulrAC mulrN divff// mulN1r opprD.
  rewrite -(addrA (- gamma)).
  rewrite mulrACA mulrN divff// mulN1r opprK.
  rewrite !addrA.
  rewrite (lerD2l (- gamma - mu * (t - a) + gamma * expR (k * (t - a)))).
  rewrite -mulN1r -RintegralZl//=.
    apply: continuous_compact_integrable; first exact: segment_compact.
    apply: within_continuousMl.
    apply: within_continuousMl.
    apply: continuous_subspaceT => x.
    apply: (@continuous_comp _ _ _ (fun s => k * (t - s)) expR); last exact: continuous_expR.
    by apply: cvgM => //; exact: cvgB.
  apply: le_Rintegral => //.
  - apply: continuous_compact_integrable; first exact: segment_compact.
    apply: within_continuousMl.
    apply: within_continuousMl.
    apply: within_continuousMl.
    apply: continuous_subspaceT => x.
    apply: (@continuous_comp _ _ _ (fun s => k * (t - s)) expR); last exact: continuous_expR.
    by apply: cvgM => //; exact: cvgB.
  - apply: continuous_compact_integrable; first exact: segment_compact.
    apply: within_continuousMl.
    apply: continuous_subspaceT => x.
    apply: (@continuous_comp _ _ _ (fun s => k * (t - s)) expR); last exact: continuous_expR.
    by apply: cvgM => //; exact: cvgB.
  move=> s sat.
  by rewrite mulrAC mulN1r -!mulNr mulrA mulrNN divff// mul1r mulrC.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
rewrite (addrC gamma) addrK subrr add0r; congr +%R.
(* TODO: generalize FTC2 for a <= b so that we avoid this step *)
have : a <= t by rewrite inE in tab; rewrite (itvP tab).
rewrite le_eqVlt => /predU1P[->|ta].
  by rewrite set_itv1 Rintegral_set1 subrr mulr0 expR0 subrr mulr0.
rewrite /Rintegral (@continuous_FTC2 _ _ (fun x => - mu / k * expR (k * (t - x))))//=.
- apply/within_continuousMl => //=; apply: within_continuous_comp => //=.
    by move=> ? ?; exact: continuous_expR.
  apply/within_continuousMl => //=; apply/within_continuousB => //=.
    exact: cst_within_continuous.
  by apply: continuous_subspaceT => x; exact: cvg_id. (* TODO: id_continuous lemma *)
- split => //=.
  + apply: cvg_at_right_filter; apply: cvgMl_tmp.
    apply: (@cvg_comp _ _ _ _ expR _ (nbhs (k * (t - a)))) => //; last first.
      exact: continuous_expR.
    by apply: cvgM => //; apply: cvgB => //; exact: cvgMl_tmp.
  + apply: cvg_at_left_filter; apply: cvgMl_tmp.
    apply: (@cvg_comp _ _ _ _ expR _ (nbhs (k * (t - t)))) => //; last first.
      exact: continuous_expR.
    by apply: cvgMl_tmp; exact: cvgB.
  + move=> x xat.
    rewrite derive1E deriveZ//= -derive1E derive1_comp//.
    rewrite 2!derive1E deriveZ// deriveD// derive_cst//.
    rewrite deriveN// derive_id sub0r scalerN scaler1.
    rewrite (mulrC _ (- k)) scalerA -mulrA mulrN mulVf// mulrN1 opprK; congr *%R.
    by rewrite -[in RHS]derive_expR.
- rewrite subrr mulr0 expR0 -mulrBr.
  by rewrite !mulNr -mulrN opprB.
Qed.

End thm34.

Section continuous_dependence.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 v0 : U) (r : {posnum R}) (k : {posnum R}).
Let B : set U := closed_ball u0 r%:num.

Hypothesis ab : a < b.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall t, k%:num.-lipschitz_B (phi t)}.

Variables y z : R -> U.
Hypothesis soly : is_sol_cauchy_oo phi a b u0 y.
Hypothesis solz : is_sol_cauchy_oo phi a b v0 z.
Hypothesis By : y @` `[a, b] `<=` B.
Hypothesis Bz : z @` `[a, b] `<=` B.

Let lm := @lebesgue_measure R.

Lemma continuous_dependence t : t \in `[a, b] ->
  `|y t - z t| <= `|u0 - v0| * expR (k%:num * (t - a)).
Proof.
move=>tab.
have := @thm34 _ _ phi a b k%:num u0 v0 r ab _ lip2 cont1 _ _ soly _ By Bz 0.
rewrite (_ : phi \+ cst 0 = phi); first by apply/funext => s; rewrite /= addr0.
move /(_ _ solz).
move /(_ _ _ t).
rewrite !mul0r addr0.
apply => //.
by move => ? ? ? ?; rewrite normr0 lexx.
Qed.

End continuous_dependence.
