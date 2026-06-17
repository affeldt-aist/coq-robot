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


(*todo: move *)
Lemma safe_dist_r_le {R : realType} {n : nat} phi (a b : R) k (u0 : 'rV[R]_n) r r' rho : 0 < k -> r <= r' -> safe_dist phi a b k u0 r rho <= safe_dist phi a b k u0 r' rho.
Proof.
move => k0 rhorho'.
rewrite unlock/=!le_min !ge_min !lexx /= !orbT /= ler_pdivlMr. 
Admitted.

Lemma safe_dist_rho_le {R : realType} {n : nat} phi (a b : R) k (u0 : 'rV[R]_n) r rho rho': 0 < k -> rho%:num <= rho'%:num -> safe_dist phi a b k u0 r rho <= safe_dist phi a b k u0 r rho'.
Proof.
move => k0 rhorho'.
by rewrite unlock/=!le_min !ge_min !lexx /= !orbT /= ler_pdivlMr // ler_pM2r ?rhorho' ?orbT// invr_gt0.
Qed.

Lemma is_sol_oo_subset {R: realType} {n : nat} phi (u0 : 'rV[R]_n) (a b c d : R) sol : c < d -> a <= c -> d <= b-> is_sol_oo phi u0 a b sol -> is_sol_oo phi (sol c) c d sol.
Proof.
move => cd ac bd isSol.
split=>//.
move => x xcd.
apply isSol.
move : xcd.
rewrite !in_itv/= => /andP[cx xd].
  apply /andP;split.
  by apply /le_lt_trans/cx.
  by apply /lt_le_trans/bd.
have [_ _ +] := isSol.
apply /continuous_subspaceW.
rewrite !closure_neitv_oo//.
by apply: subset_itv.
apply /lt_le_trans/bd.
by apply /le_lt_trans/cd.
Qed.

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

Hypothesis cont_sol :   {within `[a, b], continuous sol}.


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

Section extend_sol.
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

Let cont1_restr : {in B, forall y, {within `[b, c], continuous phi ^~ y}}.
Proof.
move => x xb.
apply /continuous_subspaceW/cont1 => //.
apply: subset_itvr.
by rewrite ltW.
Qed.

Let lip2_restr : {in `[b, c]%R, forall x, k.-lipschitz_B (phi x)}.
Proof.
move => x xb.
apply lip2.
move : xb.
by rewrite !in_itv/= => /andP[h ->]; rewrite (le_trans _ h) // ltW.
Qed.

(* (* solution on max interval [a, b) *) *)
(* Hypothesis is_integral_sol_co : forall b', b' \in `[a,b[%R -> is_integral_sol phi u0 a b' sol. *)

Hypothesis sol_oo : forall b', b' \in `[a,b[%R -> is_sol_oo phi u0 a b' sol.

Hypothesis int_phi_sol : 
 forall b', b' \in `[a,b[%R -> forall i, mu.-integrable `[a, b]
    (EFin \o (fun x : R => phi x (sol x) ord0 i)).

(* limit at the right boundary is u1 and u1 is in safe area *)
Hypothesis has_left_limit : sol @ b^'- --> u1.

Let rho : {posnum R} := 2^-1%:pos.

Let rho1 : rho%:num < 1.
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.


Let sol0 : sol a = u0.
Proof.
have h0 : a \in `[a, b[%R.
  by rewrite in_itv/= lexx.
have [+ _ _] :=  (sol_oo h0).
apply.
Qed.


Let sol_deriv t : t \in `]a,b[%R -> derivable sol t 1 /\  sol^`() t = phi t (sol t).
Proof.
move => tab.
have [t' [tt' t'ab]] : exists t', t < t' /\ t' \in `[a, b[%R.
  move : tab.
  rewrite in_itv/= => /andP[at0 tb0].
  exists ((t + b) / 2); split.
   by rewrite ltr_pdivlMr // mulr2n mulrDr mulr1 ltrD2l.
  rewrite in_itv /=; apply/andP; split.
      by rewrite ltW // (lt_trans at0) // ltr_pdivlMr // mulr2n mulrDr mulr1 ltrD2l.
      by rewrite ltr_pdivrMr // mulr2n mulrDr mulr1 ltrD2r.
have [_ + _ ] := (sol_oo t'ab).
apply.
move : tab.
by rewrite !in_itv/= => /andP[-> +].
Qed.

Let sol_continuous t : t \in `]a,b[%R -> continuous_at t sol.
Proof.
move=>tab.
have [t' [tt' t'ab]] : exists t', t < t' /\ t' \in `[a, b[%R.
  move : tab.
  rewrite in_itv/= => /andP[at0 tb0].
  exists ((t + b) / 2); split.
   by rewrite ltr_pdivlMr // mulr2n mulrDr mulr1 ltrD2l.
  rewrite in_itv /=; apply/andP; split.
      by rewrite ltW // (lt_trans at0) // ltr_pdivlMr // mulr2n mulrDr mulr1 ltrD2l.
      by rewrite ltr_pdivrMr // mulr2n mulrDr mulr1 ltrD2r.
have [_ _ + ] := (sol_oo t'ab).
have at' : a < t'.
  apply/lt_trans/tt'.
  move : tab.
  by rewrite in_itv/= => /andP[].
rewrite closure_neitv_oo//.
move /(continuous_within_itvP _ at')=>[+ _ _];apply.
rewrite in_itv/= tt'.
move : tab.
by rewrite in_itv/= => /andP[-> _].
Qed.

Let sol_continuous_left : sol x @[x --> a^'+] --> sol a.
Proof.
have [t' [t'a t'ab]] : exists t', a < t' /\ t' \in `[a, b[%R.
  exists ((a + b) / 2).
  suff : (a+b)/2 \in `]a,b[%R by rewrite !in_itv/= => /andP[h1 h2];split => //;rewrite ltW//.
  rewrite in_itv/=.
  by rewrite ltr_pdivlMr // ltr_pdivrMr // mulr2n !mulrDr !mulr1  ltrD2l ab ltrD2r.
have [_ _  +] := sol_oo t'ab.
rewrite closure_neitv_oo//.
by move /(continuous_within_itvP _ t'a) => [_ + _].
Qed.

Let sol_extended0 := (patch sol [set b] (cst u1)).

Lemma sol_extends_pt : is_sol_oo phi u0 a b sol_extended0.
Proof.
rewrite /sol_extended0.
split; first by rewrite patchC // in_setC in_set1 lt_eqF //.
  move => t tab.
  have := tab.
  rewrite in_itv/= => /andP[at0 tb0].
  have  hn:   {near t, sol =1 patch sol [set b] (cst u1)}.
    near=>x.
    rewrite patchC //in_setC in_set1 lt_eqF //.
    near:x.
    by apply: lt_nbhsl.
  split; first by apply/(near_eq_derivable (f:=sol) ) => //; apply sol_deriv.
  rewrite derive1E.
  rewrite (near_eq_derive (g:=sol)).
    by rewrite patchC // ?in_setC ?in_set1 ?lt_eqF // -derive1E; apply sol_deriv.
  by near=>t0;symmetry;near:t0.
rewrite closure_neitv_oo//.
apply/continuous_within_itvP => //; split.
- move=> x xab.
  have := xab; rewrite in_itv/= => /andP[ax xb].
  apply : cvg_trans.
    apply: (near_eq_cvg (f:=sol)).
    near=>t.
    rewrite patchC // ?in_setC ?in_set1 ?lt_eqF //.
    near:t.
    by apply: lt_nbhsl.
  by rewrite patchC // ?in_setC ?in_set1 ?lt_eqF //;apply sol_continuous.
- rewrite patchC // ?in_setC ?in_set1 ?lt_eqF //.
  apply: cvg_trans; last by apply sol_continuous_left.
  apply: (near_eq_cvg (f:=sol)).
  near=>t.
  rewrite patchC // ?in_setC ?in_set1 ?lt_eqF //.
- rewrite patch_in ?in_set1 //.
  apply: cvg_trans; last by apply has_left_limit.
  apply: (near_eq_cvg (f:=sol)).
  near=>t.
  rewrite patchC // in_setC in_set1 //.
 Unshelve. all: by end_near. Qed.

(* Local Notation safe_dist := (@safe_dist R n phi b c k u1 (r%:num / 2)%:pos rho). *)
Local Notation safe_dist_fwd := (@safe_dist R n phi b c k u1 (r%:num / 2)%:pos rho). 
Local Notation safe_dist := (@safe_dist_sym R n phi k  u1 r a c b). 
Let safe_dist_fwd_gt : safe_dist <= safe_dist_fwd.
Proof.
rewrite /safe_dist /= /rho.
rewrite !ge_min.
rewrite safe_dist_r_le//= ?orbT// .
change (((r%:num / 4 / 2) <= (r%:num / 2))%R).
by rewrite  -mulrA ler_wpM2l // ler_pdivrMr // mulVf // invf_le1 // ler1n.
Qed.


Local Lemma bac : b \in `]a,c[%R.
Proof.
by rewrite in_itv /= ab bc.
Qed.

Let sol2 := cauchy_lipschitz_f_sym  k0 cont1 lip2 bac.

Let sol2_sol : is_sol_oo phi (sol2 (b-safe_dist)) (b-safe_dist) (b + safe_dist) sol2.
Proof. by apply cauchy_lipschitz_sym_oo. Qed.

(* Let sol2_sol_fwd : is_sol_oo phi (sol2 (b-safe_dist_fwd)) (b-safe_dist_fwd) (b + safe_dist_fwd) sol2. *)
(* Proof.  *)
(* apply /is_sol_oo_subset/sol2_sol. *)
(* by rewrite ltrD2 gtrN// safe_dist_gt0. *)
(* rewrite lerB //. *)
Let sol2_init : sol2 b = u1.
Proof. by apply cauchy_lipschitz_sym. Qed.

Let sol_extended := patch sol2 `[a,b] sol_extended0.
Let ac : a < c.
Proof. by apply (lt_trans ab). Qed.

Lemma sol_extended_continuous : {within `[a, b+safe_dist], continuous sol_extended}.
Proof.
apply: within_continuous_patch => //; first by rewrite ltrDl safe_dist_sym_gt0 //.
  by have [_ _ +] := sol_extends_pt; rewrite closure_neitv_oo//.
  have [_ _ +] := sol2_sol.
  apply /continuous_subspaceW.
  rewrite closure_neitv_oo ?ler_ltD ?gtrN ?safe_dist_sym_gt0 //.
  apply: subset_itvr.
  by rewrite bnd_simp gerBl ltW // safe_dist_sym_gt0.
by rewrite /sol_extended0 patch_in ?in_set1.
Qed.

Let sol_extended_init : sol_extended a = u0.
Proof.
rewrite /sol_extended /sol_extended0 patch_in ?patchC ?in_setC ?in_set1 ?lt_eqF //.
by rewrite inE /=in_itv/= lexx ltW.
Qed.

Let sol_extended_near_b : {near b, sol2 =1 sol_extended  }.
Proof.
near=>t.
rewrite /sol_extended/patch.
case: ifP => //.
move => tab.
Admitted.

Lemma solution_extends : is_sol_oo phi u0 a (b + safe_dist) sol_extended.
Proof.
split => //; last first.
   by rewrite closure_neitv_oo ?(lt_trans ab) // ?ltrDl ?safe_dist_sym_gt0//; apply sol_extended_continuous.
 move => x xab.
 have := xab.
 rewrite in_itv/= => /andP[xa _].
 case: (ltgtP x b) => Hxb.
   have xab' : x \in `]a,b[%R.
     by rewrite /=in_itv/=;apply /andP;split.
   split.
   apply:(near_eq_derivable (f:=sol)).
   near=>x0.
   rewrite /sol_extended patch_in /sol_extended0 ?patchC// ?in_setC ?in_set1 ?lt_eqF//.
   near:x0.
   by apply: lt_nbhsl.
   rewrite inE/=in_itv/=;apply /andP;split; rewrite ltW//.
   by near:x0;apply: lt_nbhsr.
   by near:x0;apply: lt_nbhsl.
   by apply sol_deriv; rewrite in_itv/= xa.
   rewrite derive1E.
   rewrite (near_eq_derive (g:=sol)).
   rewrite -derive1E.
   rewrite /sol_extended patch_in /sol_extended0 ?patchC// ?in_setC ?in_set1 ?lt_eqF//.
   apply sol_deriv => //.
   by rewrite inE;apply: subset_itv_oo_cc.
   near=>x0.
   rewrite /sol_extended patch_in /sol_extended0 ?patchC// ?in_setC ?in_set1 ?lt_eqF//.
   by near:x0; apply: lt_nbhsl.
   rewrite inE/=in_itv/=;apply /andP;split; rewrite ltW//.
   by near:x0;apply: lt_nbhsr.
   by near:x0;apply: lt_nbhsl.

   split.
   apply:(near_eq_derivable (f:=sol2)).
   near=>x0.
   rewrite /sol_extended ?patchC// ?in_setC ?notin_setE ?inE /= ?in_itv /= .
   rewrite !leNgt;apply /negP; rewrite negb_and;apply /orP;right;apply /negPn.
   near: x0; by apply: lt_nbhsr.
   have [_ + _]:= sol2_sol.
   move /(_ x) => []//.
   move : xab.
   rewrite !in_itv/= => /andP[_ ->].
   rewrite andbT.
   apply /lt_trans/Hxb.
   by rewrite gtrBl safe_dist_sym_gt0.
   rewrite derive1E.
   rewrite (near_eq_derive (g:=sol2)).
   rewrite -derive1E.
   rewrite /sol_extended ?patchC// ?in_setC ?notin_setE ?inE /= ?in_itv /= .
   apply sol2_sol.
   move : xab.
   rewrite !in_itv/= => /andP[_ ->].
   rewrite andbT.
   apply /lt_trans/Hxb.
   by rewrite gtrBl safe_dist_sym_gt0.
   by rewrite !leNgt;apply /negP; rewrite negb_and;apply /orP;right;apply /negPn.
   near=>x0.
   rewrite /sol_extended ?patchC// ?in_setC ?notin_setE ?inE /= ?in_itv /= .
   rewrite !leNgt;apply /negP; rewrite negb_and;apply /orP;right;apply /negPn.
   by near:x0; apply: lt_nbhsr.

rewrite Hxb.
split.
apply:(near_eq_derivable (f:=sol2)).
apply: sol_extended_near_b.
have [_ + _]:= sol2_sol.
move /(_ b) => []//.
rewrite in_itv/=; apply /andP;split.
by rewrite gtrBl safe_dist_sym_gt0.
by rewrite ltrDl safe_dist_sym_gt0.
rewrite {2}/sol_extended patch_in /sol_extended0 ?patch_in ?in_set1 //=.
rewrite -sol2_init derive1E (near_eq_derive (g:=sol2)).
rewrite -derive1E.
have [_ + _]:= sol2_sol.
move /(_ b) => []//.
rewrite in_itv/=; apply /andP;split.
by rewrite gtrBl safe_dist_sym_gt0.
by rewrite ltrDl safe_dist_sym_gt0.
near=>t;symmetry;near:t.
apply: sol_extended_near_b.
by rewrite inE/=in_itv/=lexx//=andbT ltW //.
Unshelve. all: by end_near. Qed.

End extend_sol.

