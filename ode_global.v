From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum matrix interval.
From mathcomp Require Import poly archimedean generic_quotient ring_quotient.
From mathcomp Require Import interval_inference.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import contra functions constructive_ereal reals.
From mathcomp Require Import topology prodnormedzmodule tvs normedtype.
From mathcomp Require Import landau ereal sequences derive numfun measure.
From mathcomp Require Import realfun measurable_realfun lebesgue_measure.
From mathcomp Require Import lebesgue_integral ftc.
Require Import tilt_mathcomp tilt_analysis ode_common ode_contseg ode.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.


(* Extending to infinite time *)

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


(* Goal: if the rhs function is bounded, it is Lipschitz *)
Section bounded_rhs_lipschitz.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.

Variables (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U).
Variable M : R.

Hypothesis M0 : 0 <= M.

Hypothesis int_phi_sol : forall i,
  mu.-integrable `[a, b]
    (EFin \o (fun x : R => phi x (sol x) ord0 i)).

Hypothesis rhs_bound :
  {in `[a, b]%R, forall x, `| phi x (sol x) | <= M}.

(* TODO: PR? *)
Lemma integrable_cst D (c : R) : measurable D ->   (mu D < +oo)%E
 ->  mu.-integrable D (EFin \o cst c).
Proof.
  move => h1 h2.
  apply: measurable_bounded_integrable => //=.
  exact: bounded_cst.
Qed.

(*Todo: PR? *)
Lemma norm_rowRintegral_le_cst s t :
  s \in `[a, b]%R ->
  t \in `[s, b]%R ->
  `| \vint[mu]_(x in `[s, t]) phi x (sol x) | <= M * (t - s).
Proof.
move => sab tsb.
have as' : a <= s by move: sab; rewrite in_itv /= => /andP[].
have st : s <= t by move: tsb; rewrite in_itv /= => /andP[].
have tb : t <= b by move: tsb; rewrite in_itv /= => /andP[].
have st_ab : `[s, t] `<=` `[a, b].
  move=> x.
  rewrite /= !in_itv /=.
  move=> /andP[sx xt].
  by rewrite (le_trans as' sx) (le_trans xt tb).
rewrite /Num.norm /= mx_normrE.
apply: bigmax_le => //=.
  by rewrite mulr_ge0 // subr_ge0.
move=> -[i j] _ /=.
rewrite {i}(ord1 i) /=.
rewrite rowRintegralE.
rewrite (le_trans (le_normr_Rintegral _ _)) //=.
  by apply: (@integrableS _ _ _ mu `[a, b] `[s, t]) => //.
apply (@le_trans _ _ (\int[mu]_(x in `[s, t]) M)) => //=.
  apply (le_Rintegral ) => //=.
    apply: (@integrableS _ _ _ mu `[a, b] `[s, t]) => //; first by apply integrable_norm.
    apply integrable_cst => //=.
      by rewrite lebesgue_measure_itv /=; case: ifPn => //=;rewrite  ltry.
    move => x xst.
    apply (@le_trans _ _ `| phi x (sol x) |); last by apply (rhs_bound (st_ab _ xst)).
    rewrite {2}/Num.norm /= mx_normrE /=.
    by apply: (le_bigmax _ _ (ord0, j)).
rewrite Rintegral_cst //= lebesgue_measure_itv /= ler_wpM2l//.
case: ifPn => //= _.
by rewrite subr_ge0.
Qed.

(* where is this needed? *)
Lemma is_integral_sol_lipschitz :
  is_integral_sol phi u0 a b sol ->
  forall s t,
    s \in `[a, b]%R ->
    t \in `[s, b]%R ->
    `| sol t - sol s | <= M * (t - s).
Proof.
move=> Hsol s t sab tsb.
rewrite (@integral_sol_between R n phi u0 a b sol int_phi_sol Hsol s t sab tsb).
rewrite addrC addrA (addrC _ (sol s)) subrr add0r. 
exact: norm_rowRintegral_le_cst.
Qed.
End bounded_rhs_lipschitz.

Section lipschitz_left_limit.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (a b k : R) (f : R -> U).
Hypothesis ab : a < b.
Hypothesis k0 : 0 <= k.
Hypothesis f_lip :
  forall s t,
    s \in `[a, b[%R ->
    t \in `[a, b[%R ->
    `| f t - f s | <= k * `|t - s|.

Lemma lipschitz_has_left_limit :
  exists y : U, f @ b^'- --> y.
Proof.
Admitted.

End lipschitz_left_limit.

(*todo: replace iff by both directions in previous parts *)
Section sol_integral_sol2.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U).
(* Variables (r : {posnum R}). *)
(* Let B := closed_ball u1 r%:num. *)
Hypothesis ab : a < b.
Lemma sol_integral_sol :
  is_sol_oo phi u0 a b sol -> is_integral_sol phi u0 a b sol.
Proof.
move => [hinit h]; split => // t tab.
have /= := tab; rewrite in_itv/= => /andP[ta tb].
apply/rowP => i.
rewrite mxE rowRintegralE.
move: ta; rewrite le_eqVlt => /predU1P[<-|ta].
  by rewrite set_itv1 Rintegral_set1 addr0.
rewrite /Rintegral.
have cont_soli : {within `[a, b], continuous (fun x => sol x ord0 i)}.
  move: i.
  apply /within_continuous_coord.
  rewrite -closure_neitv_oo //.
rewrite (@continuous_FTC2 _ (fun x => phi x (sol x) ord0 i) (fun x => sol x ord0 i) _ _ ta).
- by rewrite -EFinB subrKC.
- admit. 
- split.
  + move=> t' tx'.
    by have /h[/derivable_mxP] : t' \in `]a, b[%R by exact/subset_itvl/tx'.
  + by move /(continuous_within_itvP _ ab) : cont_soli => [_ + _].
  + have cont_phii' : {within `[a, t], continuous fun x0 : R => sol x0 ord0 i}.
      apply: continuous_subspaceW; last exact: cont_soli.
      exact: subset_itvl.
    by move/(continuous_within_itvP _ ta) : cont_phii' => [_ _ +].
- move=> x xt.
  have /h[? +] : x \in `]a, b[%R by exact/subset_itvl/xt.
  by rewrite !derive1E derive_mx//= => <-; rewrite mxE.
Unshelve. all: by end_near. Admitted.

End sol_integral_sol2.


Section safe_dist_sym_props.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 : U) (a b c k : R) (sol : R -> U) (r : {posnum R}).

Local Notation safe_dist := (@safe_dist_sym R n phi k u0 r a c b).

Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis k0 : 0 < k.

Lemma safe_dist_sym_gt0 : 0 < safe_dist.
Proof.
by rewrite lt_min subr_gt0 bc /= lt_min !safe_dist_gt0 // ltrNl opprK.
Qed.

Lemma safe_dist_sym_itv1 : safe_dist <= b-a.
Proof.
rewrite addrC -{2}(opprK b).
by rewrite 2!ge_min safe_dist_itv !orbT.
Qed.

Lemma safe_dist_sym_itv2 : safe_dist <= c-b.
Proof.
by rewrite 2!ge_min safe_dist_itv orbT.
Qed.

End safe_dist_sym_props.

Section extend_integral_sol.
Local Notation mu := lebesgue_measure.

Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.
Variables (phi : R -> U -> U) (u0 u1 : U) (a b c k : R) (sol : R -> U) (r : {posnum R}).
Let B := closed_ball u1 r%:num.
Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis k0 : 0 < k.
Hypothesis cont1 : {in B, forall y, {within `[a, c], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, c]%R, forall x, k.-lipschitz_B (phi x)}.

(* solution on max interval [a, b) *)
Hypothesis is_integral_sol_co : forall b', b' \in `[a,b[%R -> is_integral_sol phi u0 a b' sol.

Hypothesis int_phi_sol : 
 forall b', b' \in `[a,b[%R -> forall i, mu.-integrable `[a, b]
    (EFin \o (fun x : R => phi x (sol x) ord0 i)).

(* limit at the right boundary is u1 and u1 is in safe area *)
Hypothesis has_left_limit : sol @ b^'- --> u1.

Variable rho : {posnum R}. 
Hypothesis rho1 : (rho%:num < 1).

(* solution exists in (b-safe_dist, b+safe_dist ) *)
Local Notation safe_dist := (@safe_dist_sym R n phi k u1 r a c b).
Local Lemma bac : b \in `]a,c[%R.
Proof.
by rewrite in_itv /= ab bc.
Qed.

(* give local solution (symmetric) starting at b *)
Let sol2 := cauchy_lipschitz_f_sym k0 cont1 lip2 bac.

Lemma sol2_integral_sol : is_integral_sol phi (sol2 (b-safe_dist/2)) (b-safe_dist/2) (b+safe_dist/2) sol2.
Proof.
apply/(sol_integral_sol).
rewrite ltrBlDr -addrA ltrDl -splitr safe_dist_sym_gt0 //.
have [init1 dsol] := cauchy_lipschitz_sym k0 cont1 lip2 bac.
split => //.
  move => t th.
  apply dsol.
  move  : th.
  rewrite !in_itv /=.
  move => /andP [th1 th2].
  apply /andP; split.
    apply /lt_trans/th1.
    rewrite ler_ltB // ltr_pdivrMr // ltr_pMr ?safe_dist_sym_gt0 // ltr1n //.  
  by rewrite (lt_le_trans th2)// lerD2l ger_pMr ?safe_dist_sym_gt0 // invf_le1// ler1n.
rewrite closure_neitv_oo; last by rewrite ltrD2l gtrN // divr_gt0//safe_dist_sym_gt0.
apply: derivable_within_continuous.
move => x xb.
apply dsol.
move : x xb.
apply /subitvP.
by rewrite subitvE !bnd_simp !ltrD2l ltrN2 andbb gtr_pMr // ?safe_dist_sym_gt0 // invf_lt1 // ltr1n.
Qed.

Let sol_extended := (patch sol2 `[a, b-safe_dist/2] sol).

Lemma solutions_coincide : sol (b-safe_dist/2) = sol2 (b-safe_dist/2).
Proof.
apply : locally_cauchy_lipschitz_unique.
have b0b : b-safe_dist \in `[a, b[%R.
admit.

have bt := (integral_sol_between (int_phi_sol b0b)).
Admitted.

Lemma solution_extends : is_integral_sol phi u0 a (b+safe_dist/2) sol_extended. 
Proof.
have safe_dist2_ab :   a < b - safe_dist / 2 .
  by rewrite ltrBrDl -ltrBrDr (@lt_le_trans _ _ safe_dist) // ?safe_dist_sym_itv1 // ltr_pdivrMr // ltr_pMr ?safe_dist_sym_gt0 // ltr1n.
apply is_integral_sol_patch => //.
-  
admit.
admit.
- exact: solutions_coincide.
- apply is_integral_sol_co.
  by rewrite in_itv/= ltW// gtrBl divr_gt0 // safe_dist_sym_gt0.
rewrite solutions_coincide.
exact: sol2_integral_sol.
Admitted.

End extend_integral_sol.

(* todo: clean *)
Section sol_to_integral_sol.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.

Variables (phi : R -> U -> U) (u0 : U) (a b : R) (sol : R -> U).
Hypothesis ab : a < b.

Hypothesis rhs_cont :
  {within `[a, b], continuous (fun t => phi t (sol t))}.

Lemma sol_to_integral_sol :
  is_sol_oo phi u0 a b sol ->
  is_integral_sol phi u0 a b sol.
Proof.
move=> [hinit hder hcont].
split=> // t tab.
have /= := tab; rewrite in_itv /= => /andP[ta tb].
apply/rowP=> i.
rewrite mxE rowRintegralE.

move: ta; rewrite le_eqVlt => /predU1P[<-|ta].
  by rewrite set_itv1 Rintegral_set1 addr0.

rewrite /Rintegral.
have rhs_cont_i :
  {within `[a, b], continuous (fun x => phi x (sol x) ord0 i)}.
  by move: i; apply/within_continuous_coord.

have rhs_cont_i_at :
  {within `[a, t], continuous (fun x => phi x (sol x) ord0 i)}.
  apply: continuous_subspaceW; last exact: rhs_cont_i.
  exact: subset_itvl.

have sol_cont_i :
  {within `[a, b], continuous (fun x => sol x ord0 i)}.
  admit.
  (* by move: i; apply/within_continuous_coord. *)

(* rewrite (@continuous_FTC2 _ (fun x => phi x (sol x) ord0 i) *)
(*     (fun x => sol x ord0 i) _ _ ta). *)
(* - by rewrite -EFinB subrKC hinit. *)
(* - exact: rhs_cont_i_at. *)
(* - split. *)
(*   + move=> t' tx'. *)
(*     have /hder [/derivable_mxP Hder _] : *)
(*       t' \in `]a, b[%R. *)
(*       exact/subset_itvl/tx'. *)
(*     by exact: Hder. *)
(*   + have /(continuous_within_itvP _ ab) := sol_cont_i. *)
(*     by case=> _ + _. *)
(*   + have sol_cont_i_at : *)
(*       {within `[a, t], continuous (fun x => sol x ord0 i)}. *)
(*       apply: continuous_subspaceW; last exact: sol_cont_i. *)
(*       exact: subset_itvl. *)
(*     have /(continuous_within_itvP _ ta) := sol_cont_i_at. *)
(*     by case=> _ _ +. *)
(* - move=> x xt. *)
(*   have /hder [_ H] : x \in `]a, b[%R. *)
(*     exact/subset_itvl/xt. *)
(*   by rewrite !derive1E derive_mx //= H mxE. *)
(* Unshelve. all: by end_near. *)
Admitted.

End sol_to_integral_sol.
