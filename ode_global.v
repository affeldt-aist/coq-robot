From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg ssrnum matrix interval.
From mathcomp Require Import poly archimedean generic_quotient ring_quotient.
From mathcomp Require Import interval_inference.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import contra functions constructive_ereal reals.
From mathcomp Require Import topology prodnormedzmodule tvs normedtype.
From mathcomp Require Import landau ereal sequences exp derive numfun measure.
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


Lemma closure_neitv_coo {R : realType} (a : R) :
  closure `]a, +oo[%classic = `[a, +oo[%classic.
Proof.
set x := a + 1.
have -> : (`]a, +oo[ = `]a, x[ `|` `[x, +oo[)%classic.
  by apply: itv_bndbnd_setU => //; rewrite bnd_simp ltrDl.
rewrite closureU -((closure_id _).1 (@rray_closed _ _ _)).
rewrite closure_neitv_oo; last by rewrite ltrDl.
rewrite -(setUitv1 true) ?bnd_simp; last by rewrite lerDl.
rewrite -setUA [[set x] `|` _]setUidr; last first.
  by rewrite -set_itv1; apply: subset_itvl.
apply/esym.
by apply: itv_bndbnd_setU => //; rewrite bnd_simp lerDl.
Qed.

Lemma safe_dist_rho_le {R : realType} {n : nat} phi (a b : R) k (u0 : 'rV[R]_n) r rho rho': 0 < k -> rho%:num <= rho'%:num -> safe_dist phi a b k u0 r rho <= safe_dist phi a b k u0 r rho'.
Proof.
move => k0 rhorho'.
by rewrite unlock/=!le_min !ge_min !lexx /= !orbT /= ler_pdivlMr // ler_pM2r ?rhorho' ?orbT// invr_gt0.
Qed.


Lemma is_sol_oo_rev {R : realType} {n : nat}
    (phi : R -> 'rV[R]_n -> 'rV[R]_n)
    (a b : R) (f : R -> 'rV[R]_n) :
  a < b ->
  is_sol_oo phi (f a) a b f ->
  is_sol_oo (fun t x => - phi (- t) x) (f b) (- b) (- a) (f \o -%R).
Proof.
move => ab [_ hd].
split => /=; first by rewrite opprK.
  move => x.
  rewrite -oppr_itvoo => -xba.
  have [Df Hf] := hd _ xba.
  have D : derivable (f \o -%R) x 1.
    apply/derivable1_diffP.
    apply differentiable_comp => //.
    by apply /derivable1_diffP.
  split => //.
  apply/rowP=> i.
  rewrite mxE derive1E derive_mx //= mxE -derive1E /=.
   have -> : (fun t0 : R => f (- t0) ord0 i) = ((fun t => f t ord0 i) \o -%R) by apply funext.
   rewrite  derive1_comp//=.
   rewrite !derive1N//=derive1_id/=.
   move /rowP : Hf =>  /(_ i).
      rewrite !derive1E /=!derive_mx.
      rewrite /=!mxE => ->.
      by rewrite mulrN1.
      apply Df.
  by move /derivable_mxP: Df.
  rewrite closure_neitv_oo; last by rewrite ltrN2.
  apply: within_continuous_compN.
  rewrite !opprK.
  rewrite -closure_neitv_oo//.
Qed.

Lemma is_sol_oo_rev_iff {R : realType} {n : nat}
    (phi : R -> 'rV[R]_n -> 'rV[R]_n)
    (a b : R) (f : R -> 'rV[R]_n) :
  a < b ->
  is_sol_oo phi (f a) a b f <->
  is_sol_oo (fun t x => - phi (- t) x) (f b) (- b) (- a) (f \o -%R).
Proof.
move => ab.
split; first by apply is_sol_oo_rev.
move => h.
suff : is_sol_oo (fun t x => - - (phi (- - t) x)) ((f \o -%R) (- a)) (- - a) (- - b) ((f \o -%R) \o -%R).
  rewrite /= !opprK.
  have -> : ((f \o -%R) \o -%R) = f by rewrite -compA; apply/funext=> x; rewrite /= opprK.
  suff -> : (fun t x => - - (phi (- - t) x)) = phi by [].
  by apply /funext => t; apply funext => x; rewrite !opprK.
by apply (@is_sol_oo_rev _ _ (fun t x => (-(phi (-t) x)))); rewrite ?ltrN2 //= opprK.
Qed.

Lemma bounded_derivative_lipschitz {R : realType} {n : nat}
    (a b M : R) (f : R -> 'rV[R]_n) :
  0 <= M ->
  {within `[a, b], continuous f} ->
  {in `]a, b[%R, forall x,
     derivable f x 1 /\ `| f^`() x | <= M} ->
   {in `]a, b[%R&, forall s t,
  `| f t - f s | <= M * `|t - s|}.
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
have [ | |c cst ->]:= @MVT_segment _ (fun t => f t ord0 i) ('D_1 (fun t => f t ord0 i)) _ _ st.
  move => x xst.
  have xab : x \in `]a,b[%R.
    move : xst.
    apply : subset_itv; rewrite bnd_simp ltW //.
    by move : sab;rewrite in_itv/= => /andP[].
    by move : tab;rewrite in_itv/= => /andP[].
  apply /derivableP.
  have [/derivable_mxP + _] := (deri x xab).
  apply.

  move /within_continuous_coord : cont.
  move /(_ i).
  apply: continuous_subspaceW.
  apply : subset_itv; rewrite bnd_simp ltW//.
  by move : sab;rewrite in_itv/= => /andP[].
  by move : tab;rewrite in_itv/= => /andP[].
rewrite -derive1E/= normrM ler_wpM2r //.
have cab: c \in `]a,b[%R.
  move : cst.
  apply : subset_itv; rewrite bnd_simp.
  by move : sab;rewrite in_itv/= //= => /andP[].
  by move : tab;rewrite in_itv/= => /andP[].
have [_  + ] := (deri c cab).
rewrite {1}/Num.norm /= mx_normrE.
apply: le_trans.
suff -> : (fun t0 : R => f t0 ord0 i)^`() c =  f^`() c ord0 i by exact: (le_bigmax _ _ (ord0, i)).
rewrite !derive1E !derive_mx //= ?mxE //.
by apply deri.                                    
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
Hypothesis k0 : 0 < k.
Hypothesis f_lip sol: 
  forall s t,
    s \in `]a, b[%R ->
    t \in `]a, b[%R ->
    `| f t - f s | <= k * `|t - s|.

Lemma lipschitz_has_left_limit :
  f @ b^'- --> lim (f @ b^'-).
Proof.
apply /cauchy_cvgP.
apply /cauchyP => eps eps0 /=.
have e2k0 : 0 < eps / k / 2.
  by rewrite divr_gt0 // divr_gt0.
near b^'- => s.
exists (f s).
near=>t. 
rewrite /= -ball_normE /=.
 apply: le_lt_trans; first apply f_lip.
  rewrite in_itv/=;apply /andP;split.
  near:t.
  apply: cvg_at_left_filter; first by apply cvg_id.
  by apply: lt_nbhsr.
  by near:t;exact: nbhs_left_lt.

  rewrite in_itv/=;apply /andP;split.
  near:s.
  apply: cvg_at_left_filter; first by apply cvg_id.
  by apply: lt_nbhsr.
  by near:s;exact: nbhs_left_lt.
rewrite mulrC -ltr_pdivlMr //.
rewrite -(subrKA b) (le_lt_trans  (ler_normD _ _)) // (splitr (eps / k)) ltrD //.
  suff: ball b (eps/ k /2) s by rewrite -ball_normE /ball_ /= distrC.
  near:s.
  apply: cvg_at_left_filter; first by apply cvg_id.
  by apply: nbhsx_ballx.
suff: ball b (eps/ k /2) t by rewrite -ball_normE /ball_ /= distrC.
near:t.
apply: cvg_at_left_filter; first by apply cvg_id.
by apply: nbhsx_ballx.
Unshelve. all: by end_near. Qed.
End lipschitz_left_limit.


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

Definition sol_extended := patch sol2 `[a,b] sol_extended0.
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
have := tab; rewrite inE /= in_itv/= => -/andP[_ tb].
have :=  sol_extends_pt.
have <- : sol_extended0 a = u0 by apply sol_extends_pt.
move /(is_sol_oo_rev ab) => hext0.
rewrite /sol2 cauchy_lipschitz_sym_left /=.
have -> : sol_extended0 t = (sol_extended0 \o -%R) (-t) by rewrite /= opprK.
apply: cauchy_lipschitz_unique.
have <- : (sol_extended0 \o -%R) (- b) = u1 by rewrite /= opprK /sol_extended0 patch_in //= in_set1.
apply /is_sol_oo_subset/hext0=>//.
  by rewrite ltrDl safe_dist_gt0 // ltrN2.
  by rewrite -lerBDl;apply safe_dist_itv.
  rewrite oppr_itv/= opprD !opprK in_itv/= tb andbT.
  apply ltW.
  near:t.
  apply: lt_nbhsr.
  by rewrite gtrBl safe_dist_gt0 // ltrN2.
rewrite in_itv/=tb andbT ltW //=.
near:t.
apply: lt_nbhsr.
by rewrite gtrBl safe_dist_sym_gt0 // ltrN2.
Unshelve. all: by end_near. Qed.


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

(* maybe not useful? *)
Section extend_from_lipschitz.

Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.

Variables (phi : R -> U -> U) (u0 : U) (a b c : R) (sol : R -> U).

Hypothesis ab : a < b.
Hypothesis bc : b < c.

Hypothesis sol_oo :
  forall b', b' \in `[a, b[%R -> is_sol_oo phi u0 a b' sol.

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
  forall s t,
    s \in `]a, b[%R ->
    t \in `]a, b[%R ->
    `| sol t - sol s | <= k * `|t - s|.


Let has_left_limit : sol @ b^'- --> u1.
Proof.
rewrite /u1.
by apply /lipschitz_has_left_limit/sol_lip.
Qed.

Local Notation sol_extended := (sol_extended sol ab bc k0 cont1 lip2 ).
Local Notation safe_dist := (@safe_dist_sym R n phi k u1 r a c b).

Lemma solution_extends_from_lipschitz : is_sol_oo phi u0 a (b + safe_dist) sol_extended.
Proof. by apply : solution_extends. Qed.

End extend_from_lipschitz.


Section extend_from_compact_containment.

Context {R : realType} {n : nat}.
Notation U := 'rV[R]_n.

Variables (phi : R -> U -> U) (u0 : U) (a b c : R) (sol : R -> U).

Variable K : set U.

Hypothesis ab : a < b.
Hypothesis bc : b < c.

Hypothesis sol_oo :
  forall b', b' \in `[a, b[%R -> is_sol_oo phi u0 a b' sol.

Hypothesis compactK : compact K.

Hypothesis solK :
  sol @` `[a, b[ `<=` K.


Hypothesis phi_loc_lip :
  forall y0, y0 \in K ->
    exists r k : {posnum R}, 
          {in `[a, c]%R, forall t,
         k%:num.-lipschitz_(closed_ball y0 r%:num) (phi t)} /\
         {in closed_ball y0 r%:num, forall y,
            {within `[a, c], continuous phi ^~ y}}.

(* should be derivable from the previous *)
Hypothesis phi_cont :
  {within `[a,c] `*` K,
    continuous (fun p : (R * U)%type => phi p.1 p.2)}.

Let u1 :=  lim (sol @ b^'-).


Lemma rhs_bounded_on_solution :
  bounded_set [set `| phi t (sol t) | | t in `[a, b[].
Proof.
suff [M [h1 h2]] :   bounded_set [set `| phi p.1 p.2 | | p in (`[a, c] `*` K)].
  exists M;split=>// x Mx /= x0 [t tab h].
  apply h2 => //.
  exists (t, sol t) => //=.
  split; first by move : tab;apply: subset_itvl; rewrite bnd_simp ltW.
  by apply solK.
apply compact_bounded.
apply continuous_compact;last by apply compact_setX => //; exact: segment_compact.
apply : within_continuous_comp.
  by move=> ? ?; apply: norm_continuous.
simpl.
exact: phi_cont.
Qed.

Lemma sol_is_lipschitz :  exists M, 0 < M /\ forall s t : R, s \in `]a, b[%R -> t \in `]a, b[%R -> `|sol t - sol s| <= M * `|t - s|.
Proof.
have [M [mr h]] := rhs_bounded_on_solution;exists (`| M|+1); split => [ | s t asb tab].
  apply (@lt_le_trans _ _ 1) => //.
  by rewrite lerDr normr_ge0.
wlog st : s t asb tab / s <= t.
  move => H.
  have [st|ts] := leP s t.
  exact: H.
  rewrite distrC (distrC t).
  apply H => //.
  by apply ltW.
set b' := t + (b-t)/2.
have bb' : b' < b.
  rewrite /b' -ltrBrDl ltr_pdivrMr // mulr2n mulrDr mulr1 ltrDl subr_gt0.
  by move: tab; rewrite in_itv /= => /andP[_ ->].
have tb' : t < b'.
  rewrite /b' ltrDl divr_gt0 // subr_gt0.
  by move: tab; rewrite in_itv /= => /andP[_ +].
have b'ab : b' \in `[a,b[%R.
  rewrite in_itv/= bb' andbT.
  move : tab.
  rewrite in_itv/= => /andP[/ltW + _].
  move /le_trans;apply.
  by rewrite ltW.
have atb' : t \in `]a,b'[%R.
  move : tab.
  by rewrite !in_itv/= tb' andbT => /andP[].
have sab' : s \in `]a,b'[%R.
  move : asb.
  rewrite !in_itv/= => /andP[-> _]/=.
  by apply (le_lt_trans st).
apply/bounded_derivative_lipschitz/atb'/sab'.
  by rewrite addr_ge0 //.
  have [_ _ +] := sol_oo b'ab.
  rewrite closure_neitv_oo//.
  apply /lt_trans/tb'.
  by move : tab;rewrite in_itv/= => /andP[].
move => x xab.
have [_ + _] := sol_oo b'ab.
move /(_ _ xab) => [hd ->].
split=>//.
have MM' : M < `|M| + 1.
  apply: (le_lt_trans (ler_norm _)).
  by rewrite ltrDl.
have:= h _ MM' `|phi x (sol x)| .
rewrite /=normr_id;apply.
exists x => //.
move : xab.
rewrite !in_itv/= => /andP[/ltW -> /=].
by move /lt_trans;apply.
Qed.

Lemma sol_has_left_limit : sol @ b^'- --> u1.
Proof.
rewrite /u1.
have [/= M [M0 lip]]:= sol_is_lipschitz. 
by apply/lipschitz_has_left_limit/lip.
Qed.


Lemma left_limit_in_K : u1 \in K.
Proof.
rewrite inE.
apply: closed_cvg sol_has_left_limit.
by exact: compact_closed.
near=>t.
apply solK => /=.
exists t => //.
  rewrite in_itv/=;apply /andP;split.
  apply ltW; near:t.
  apply: cvg_at_left_filter; first by apply cvg_id.
  by apply: lt_nbhsr.
  by near:t;exact: nbhs_left_lt.
Unshelve. all: by end_near. Qed.

Lemma solution_extends_from_compact :
  exists d : {posnum R}, exists sol' : R -> U,
    is_sol_oo phi u0 a (b + d%:num) sol' /\
    {in `[a, b[%R, sol =1 sol'}.
Proof.
have [r [k [lip2 cont1]]]:= (phi_loc_lip  left_limit_in_K).
have k0 : 0 < k%:num by [].
exists (PosNum (safe_dist_sym_gt0 phi u1 r ab bc k0)).
exists (sol_extended sol ab bc k0 cont1 lip2).
split.
  apply: solution_extends => //.
  exact: sol_has_left_limit.
move => t tab.
rewrite /sol_extended patch_in; last by rewrite inE;apply: subset_itv_co_cc.
by rewrite patchC // in_setC in_set1 /= lt_eqF //; move : tab; rewrite in_itv/= => /andP[].
Qed.

End extend_from_compact_containment.


Section max_solution.
Context {R : realType} {n : nat} (a : R).
Notation U := 'rV[R]_n.
Variable phi : R -> U -> U.

Variable K : set U.
Variables (u0 : U).
Hypothesis compactK : compact K.
Hypothesis u0K : u0 \in K.

(* Hypothesis solK : *)
(*   forall sol @` `[a, b[ `<=` K. *)


Hypothesis phi_loc_lip :
  forall y0, 
    exists r k : {posnum R}, 
          (forall t,
         k%:num.-lipschitz_(closed_ball y0 r%:num) (phi t)) /\
         {in closed_ball y0 r%:num, forall y,
            continuous (phi ^~ y)}.


Local Lemma phi_cont :
  {within setT `*` K,
    continuous (fun p : (R * U)%type => phi p.1 p.2)}.
Proof.
apply: continuous_subspaceT.
move => [/= t0 y0].
apply/cvg_ballP => eps eps0 /=.
have [r [k [Hlip Hcont]]] := phi_loc_lip y0.
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
  \forall p \near (t0, y0),
    `| phi p.1 y0 - phi p.1 p.2 | < eps / 2.
  near=>p.
  have  B0 : ((closed_ball y0 r%:num `*` closed_ball y0 r%:num) (y0, p.2)).
    split; first by apply closed_ballxx.
    near:p.
    exists ([set:R], ball y0 r%:num) => /=.
    split => //=.
    exact: filterT.
    by apply: nbhsx_ballx.
    move => [t1 t2] [b1 b2 /=].
    by apply subset_closed_ball.
  move : (Hlip p.1 (y0, p.2) B0).
  move/le_lt_trans;apply.
  rewrite -ltr_pdivlMl//= mulrC.
  suff : ball y0 (eps/2/k%:num) p.2 by rewrite -ball_normE.
  near:p.
  exists ([set:R], ball y0 (eps/2/k%:num)) => /=.
  split => //=.
  exact: filterT.
  apply: nbhsx_ballx.
  by rewrite divr_gt0.
  move => [t1 t2] [b1 b2 /=].
  exact b2.
near=> t.
rewrite -ball_normE/=.
rewrite -(subrKA (phi t.1 y0 ) (phi t0 y0)) (le_lt_trans (ler_normD _ _))  // (splitr eps) ltrD//.
by near:t;exact: c1.
by near:t;exact: c2.
Unshelve. all: end_near. Qed.

Definition bset := [set b | b >= a /\ exists sol, is_sol_oo phi u0 a b sol].

Let rho : {posnum R} := 2^-1%:pos.

Let rho1 : rho%:num < 1.
Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Lemma bset_min : exists x, bset x /\ a < x.
Proof.
have a1 : a < a+1 by rewrite ltrDl.
have [r [k [l2 c1]]] := phi_loc_lip u0.
have lip1: {in `[a, a + 1]%R, forall x , k%:num.-lipschitz_(closed_ball u0 r%:num) (phi x)} by [].
have cont1 : {in closed_ball u0 r%:num, forall y : 'rV_n, {within `[a, a + 1], continuous phi^~ y}}.
  by move => x xb; apply: continuous_subspaceT; apply c1.
have k0 : 0 < k%:num by [].
exists (a+safe_dist phi a (a+1) k%:num u0 (r%:num/2)%:pos rho).
split; last by rewrite ltDl_safe_dist.
split; first by rewrite leDl_safe_dist.
exists  (cauchy_lipschitz_f a1 k0 lip1 cont1 rho1).
apply: is_sol_cauchy_lipschitz_f.
Qed.

Lemma bset_nonempty : bset !=set0.
Proof.
have [x [bx ax]]:= bset_min.
by exists x.
Qed.

Lemma is_sol_empty sol b : b <= a ->sol a = u0 -> is_sol_oo phi u0 a b sol.
Proof.
move => ba sol0.
split=>//.
move => t.
rewrite in_itv/= => /andP[h1 h2].
 have h3:= lt_trans h1 h2.
 have := le_lt_trans ba h3.
 by rewrite ltxx.
 rewrite set_itv_ge;last by rewrite -leNgt bnd_simp.
 rewrite closure0.
 by apply: continuous_subspace0.
 Qed.

Lemma sol_inftyP sol :  is_sol_obnd phi u0 a (BInfty R false) sol <-> (forall b, is_sol_oo phi u0 a b sol). 
Proof.
split.
- move => [h1 h2 h3] b.
   split => //.
   move => t tab.
   apply h2.
   move : tab.
   by rewrite !in_itv/= => /andP[-> _].
   apply /continuous_subspaceW/h3.
   apply closure_subset.
   by apply: subset_itvl.
- move => h; split.
  by apply h.
  move => t tab.
  apply (h (t+1)).
  move : tab.
  by rewrite /=!in_itv/= ltrDl ltr01 => /andP[-> _].
  rewrite closure_neitv_coo.
  apply /continuous_within_itvcyP.
  split=>//.
  move => /= t tab.
  have at1: a < t+1.
    move: tab.
    rewrite /=in_itv/= => /andP[/lt_trans+ _].
    apply.
    by rewrite ltrDl.
  have := (And33 (h (t+1))).
  rewrite closure_neitv_oo => //.
  move /(continuous_within_itvP _ at1) => [+ _ _].
  apply.
  move : tab.
  by rewrite !in_itv/= ltrDl => /andP[-> _]/=.
have := (And33 (h (a+1))).
rewrite closure_neitv_oo => //.
move /(continuous_within_itvP ). 
rewrite ltrDl.
move /(_ ltr01).
by case => [_ + _].
by rewrite ltrDl.
Qed.

Lemma solt_eq  sol1 sol2 b: a < b ->  {in `[a,b], sol1 =1 sol2} -> is_sol_oo phi u0 a b sol1 -> is_sol_oo phi u0 a b sol2. 
Proof.
move => ab hs [init solp1 solp2].
split=>//.
- rewrite -init.
  apply /esym.
  apply hs.
  by rewrite inE/= bound_itvE ltW.
- move=>t tab.
  split.
  + apply/near_eq_derivable/(solp1 _ tab).1 => //.
    near=>t'.
    apply hs.
    rewrite inE/=.
    apply: subset_itv_oo_cc.
    near:t'.
    apply: near_in_itvoo.
    move : tab.
    by rewrite inE.
  + have hs':  {in `]a, b[%R, sol1 =1 sol2}.
      move => t' tab'.
      apply hs.
      rewrite inE.
      apply: subset_itv_oo_cc.
      move : tab'.
      by rewrite inE.
      rewrite -hs'//.
    rewrite -(eq_on_itv_deriv hs') //.
    by apply solp1.
  + apply: subspace_eq_continuous solp2.
    by rewrite closure_neitv_oo.
Unshelve. all: by end_near. Qed.

Lemma all_sols_global_sol : (forall b,  exists sol, is_sol_oo phi u0 a b sol) ->  exists sol, is_sol_obnd phi u0 a (BInfty R false) sol.
Proof.
  move => H.
  have [solt soltp] := (choice H).
  exists (fun t => solt (t+1) t).
  apply /sol_inftyP.
  move => b /=.
  have [ab | ba]:= ltP a b; last first.
    split; first by apply soltp.
    move => t.
    rewrite in_itv/= => /andP[h1 h2].
    have h3:= lt_trans h1 h2.
    have := le_lt_trans ba h3.
    by rewrite ltxx.
    rewrite set_itv_ge;last by rewrite -leNgt bnd_simp.
    rewrite closure0.
    by apply: continuous_subspace0.
  suff heq : {in `[a,b],  solt b =1 (fun t => solt (t+1) t) }.
    by apply (solt_eq ab heq).
  move => t tab.
  have at1 : a < (t+1).
    move : tab.
    rewrite !inE/=!in_itv/=  => /andP[h _].
    apply: (le_lt_trans h).
    by rewrite ltrDl.
  suff -> : solt b t = solt (maxr (t+1) b) t.
    apply: (locally_cauchy_lipschitz_unique  at1 _ (u0 := u0) ) => //.
    have <- :  solt (maxr (t+1) b) a = u0.
      by apply (soltp (maxr (t+1) b)).
    apply /is_sol_oo_subset/(soltp _) => //=.
      by rewrite le_max lexx.
    move => t0 at0 t0t.
    have [r [k [l1 c1]]] := (phi_loc_lip (solt (maxr (t + 1) b) t0)). 
    exists r, k => t' _; split => //=.
    by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
    move : tab.
    by rewrite inE/=!in_itv/= lerDl ler01 => /andP[-> _].
    apply: (locally_cauchy_lipschitz_unique  ab (u0 := u0) ) => //=.
    have <- :  solt (maxr (t+1) b) a = u0.
      by apply (soltp (maxr (t+1) b)).
    apply /is_sol_oo_subset/(soltp _) => //=.
   by rewrite le_max lexx;apply /orP;right.
    move => t0 at0 t0t.
    have [r [k [l1 c1]]] := (phi_loc_lip (solt b t0)). 
    exists r, k => t' _; split => //=.
    by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
by move : tab;rewrite inE.
Qed.

Lemma bset_down b c :
   a < b -> b <= c -> bset c -> bset b.
Proof.
move=>ab bc [ac [sol solp]].
split=>//.
rewrite ltW//.
exists sol.
have <- : sol a = u0 by apply solp.
by apply /is_sol_oo_subset/solp.
Qed.

Let asup_lt : has_sup bset -> a < sup bset.
Proof.
move => h.  
have [x [bx ax]] := bset_min.
apply (lt_le_trans ax).
by apply sup_upper_bound.
Qed.

Lemma max_sol : has_sup bset -> exists sol,  forall b, b < sup bset -> is_sol_oo phi u0 a b sol.
Proof.
move => hs.
have /choice [solt soltp]: forall b, exists sol,b < sup bset -> is_sol_oo phi u0 a b sol.
  move => b.
  have [ab0 | ba0]:= ltP a b; last first.
    exists (cst u0).
    move => h.
    apply is_sol_empty => //.
  suff : b < sup bset -> bset b.
    have [ba | ab] := ltP b (sup bset).
    by move => []//h [f pf];exists f.
    by move => _; exists (cst u0).
  move=>hb.
  have [c bc1 bc2] := sup_gt bset_nonempty hb.
  by apply /bset_down/bc1/ltW.
set r := fun t => (t + (sup bset - t)/2).
have rsup : forall t, t < sup bset -> r t < sup bset.
  by move => t ts;rewrite -ltrBrDl ltr_pdivrMr ?ltr0n ?mulr2n // mulrDr mulr1 ltrDl subr_gt0.
have rt : forall t, t < sup bset -> t < r t. 
  by move => t ts;rewrite /r ltrDl ltr_pdivlMr // mul0r subr_gt0.
have solt0 x :  x < sup bset -> (solt x a) = u0 by move /(soltp _) => [+ _ _].
exists (fun t => solt (r t) t).
move => b /= bs.
have [ab | ba]:= ltP a b; last first.
  split; first by apply soltp;apply rsup;apply asup_lt.
  apply is_sol_empty => //.
  apply solt0 => //.
  by apply rsup;apply asup_lt.
  apply is_sol_empty => //.
  apply solt0 => //.
  by apply rsup;apply asup_lt.
suff heq : {in `[a,b],  solt b =1 (fun t => solt (r t) t) }.
  by apply: (solt_eq ab heq);apply soltp.
move => t tab.
have tsup :   t < sup bset.
  apply /le_lt_trans/bs.
  by move : tab; rewrite inE/=in_itv/= => /andP[].
have art : a < r t.
  apply /le_lt_trans/rt => //.
  by move : tab; rewrite inE/=in_itv/= => /andP[].
suff -> : solt b t = solt (maxr (r t) b) t.
  apply: (locally_cauchy_lipschitz_unique  (phi:=phi) art _ (u0 := (solt (maxr (r t) b) a))) => //.
    apply /is_sol_oo_subset/(soltp _) => //=.
      by rewrite le_max lexx.
      by rewrite gt_max bs andbT rsup//.
    rewrite solt0.
    by apply: soltp; apply rsup.
    rewrite gt_max rsup //=.
    move => t0 at0 t0t.
    have [r0 [k [l1 c1]]] := (phi_loc_lip (solt (maxr (r t) b) t0)).
    exists r0, k => t' _; split => //=.
    by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
    move : tab.
    rewrite inE/=!in_itv/=  => /andP[-> _].
    by apply ltW; apply rt. 
apply: (locally_cauchy_lipschitz_unique  (phi:=phi) ab _ (u0 := u0)) => //.
  apply soltp=>//.
  rewrite -(solt0 (maxr (r t) b)).
  apply /is_sol_oo_subset/(soltp _) => //=.
   by rewrite le_max lexx;apply /orP;right.
   by rewrite gt_max bs andbT rsup//.
  rewrite gt_max rsup //=.
  move => t0 at0 t0t.
  have [r0 [k [l1 c1]]] := (phi_loc_lip (solt b t0)). 
  exists r0, k => t' _; split => //=.
  by move => y hy; apply: continuous_subspaceT; apply: c1; rewrite inE.
by move : tab;rewrite inE.
Qed.

Lemma no_ub_global_sol : ~ has_ubound bset ->
  exists sol, is_sol_obnd phi u0 a +oo%O sol.
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
  move => t.
  rewrite in_itv/=.
  move=> /andP[at0 tM].
  by have := lt_trans at0 tM; rewrite ltNge Ma.
  suff ->:   `]a, M[ = set0 by rewrite closure0; apply: continuous_subspace0.
  by rewrite set_itv_ge// bnd_simp -leNgt.
exists M.
move => x [ax [sol solp]].
move : Mh.
apply: contra_notP.
rewrite leNgt => /negP/negPn h.
exists sol.
have <- :  sol a = u0 by apply solp.
apply /is_sol_oo_subset/solp => //.
by rewrite ltW.
Qed.

Lemma compact_containment_no_sup :
  (forall b sol, is_sol_oo phi u0 a b sol -> sol @` `[a,b[ `<=` K) ->
                                                  ~ has_sup bset.
Proof.
move => H Hsup.
have [sol Hsol] := max_sol Hsup.
suff [d [sol' [H1 _]]]:  exists (d : {posnum R}) (sol' : R -> 'rV_n),
     is_sol_oo phi u0 a (sup bset + d%:num) sol' /\ {in `[a, sup bset[%R, sol =1 sol'}.
  have Hb : bset (sup bset + d%:num).
    split; last by exists sol'.
    by rewrite ltW// (lt_le_trans  (asup_lt Hsup))// lerDl.
  have := sup_upper_bound Hsup Hb.
  by apply/negP;rewrite -ltNge ltrDl.

apply: (solution_extends_from_compact (c := sup bset + 1) (K:=K)) => //.
  by apply asup_lt.
  by rewrite ltrDl.
  by move => b'; rewrite in_itv/= => /andP[_ b'lt];apply Hsol.
  move => _ [x /= + <-].
  rewrite in_itv/= => /andP[ha hb].
  apply: (H ((x+sup bset)/2) sol).
    by apply Hsol;rewrite ltr_pdivrMr // mulr2n mulrDr mulr1 ltrD2r.
    exists x => //=.
    by rewrite in_itv/=ha/=ltr_pdivlMr // mulr2n mulrDr mulr1 ltrD2l.
  move =>  y Ky.
  have [r [k [hrk1 hrk2]]]:= (phi_loc_lip y).
  exists r,k;split => //.
  move => /= y0 Hy0.
  apply: continuous_subspaceT.
  by apply hrk2.
by apply /continuous_subspaceW/phi_cont;apply setSX.
Qed.

(* Thm 3.3 in Khalil *)
Lemma compact_containment_global_sol :
  (forall b sol, is_sol_oo phi u0 a b sol -> sol @` `[a,b[ `<=` K) ->
  exists sol, is_sol_obnd phi u0 a (BInfty R false) sol.
Proof.
move => H.
apply no_ub_global_sol.
suff : ~ has_sup bset.
  by apply contra_not => hub;split=>//;apply bset_nonempty.
exact: compact_containment_no_sup.
Qed.

End max_solution.

Lemma within_continuousM {T : topologicalType} {K : (*numFieldType*)realType}
    (V := (*pseudoMetricNormedZmodType*) K) (A : set T) (f g : T -> V) :
  {within A, continuous f} -> {within A, continuous g} ->
  {within A, continuous (f \* g)}.
Proof. by move=> cf cg x; apply: cvgM; [exact: cf|exact: cg]. Qed.


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

(* TODO: PR *)
Lemma parameterized_integralr_continuous a b (f : R -> R) : a <= b ->
  {within `[a, b], continuous f} ->
  {within `[a, b], continuous (fun x => int x b f)}.
Proof.
move=> ab abf.
rewrite /int.
suff:
  {within `[a, b], continuous ((fun x => parameterized_integral lebesgue_measure (-b) x (f \o -%R)) \o -%R) }.
  apply: continuous_within_ext => x /[!inE] xab/=.
  rewrite -parameterized_integralN//.
    by rewrite (itvP xab).
  apply: continuous_subspaceW abf.
  by apply: subset_itvr; rewrite bnd_simp (itvP xab).
apply: within_continuous_compN.
have := @parameterized_integral_continuous _ (- b) (- a) (f \o -%R).
apply.
  by rewrite lerN2.
apply: continuous_compact_integrable => //.
  exact: segment_compact.
apply: within_continuous_compN.
by rewrite !opprK.
Qed.

End parameterized_integral_continuous.

Section gronwall.
Context {R : realType} (a b : R) (ab : a < b) (lambda : R -> R) (mu : R -> R)
  (lambda_cont : {within `[a, b], continuous lambda})
  (mu_cont : {within `[a, b], continuous mu})
  (mu_ge0 : forall x, x \in `[a, b] -> 0 <= mu x)
  (y : R -> R)
  (y_cont : {within `[a, b], continuous y}).

Let lm := @lebesgue_measure R.

From mathcomp Require Import ring.

Lemma solve_diff_equa (z f : R -> R) : z a = 0 ->
  {in `]a, b[, forall x, derivable z x 1} ->
  (forall t, t \in `]a, b[ -> 'D_1 z t = mu t * z t + f t) ->
  let phi t s := expR (\int[lm]_(tau in `[s, t]) mu tau) in
  forall t, t \in `]a, b[ ->
    z t = \int[lm]_(s in `[a, t]) (phi t s * f s).
Proof.
move=> za0 derivable_z eqn phi t /[!inE] tab.
rewrite /Rintegral integral_itv_bndoo//=; last first.
  apply/measurable_EFinP/measurable_funM => //.
    apply/measurableT_comp => //=.
    apply: subspace_continuous_measurable_fun => //.
    apply: (@continuous_subspaceW _ _ _ `[a, t]) => //.
      exact: subset_itv_oo_cc.
    apply: parameterized_integralr_continuous.
      by rewrite (itvP tab).
    apply: continuous_subspaceW mu_cont.
    by apply: subset_itvl; rewrite bnd_simp (itvP tab).
  admit.
have {}eqn : forall t : R, t \in `]a, b[ ->
    ('D_1 z t - mu t * z t) * (phi t a)^-1 = f t * (phi t a)^-1.
  move=> x xab.
  by rewrite eqn// addrAC subrr add0r.
have derivable_int_mu u : u \in `]a, b[ ->
    derivable (fun x => \int[lm]_(tau in `[a, x]) mu tau) u 1.
  move=> uab.
  apply: (@continuous_FTC1 _ mu (BLeft a) u b _ _ _ _).1 => /=.
  - by move: uab; rewrite inE => /itvP ->.
  - by apply: continuous_compact_integrable mu_cont; exact: segment_compact.
  - by rewrite lte_fin; move: uab; rewrite inE => /itvP ->.
  - by move: uab; rewrite inE; exact: within_continuous_continuous.
have derivablephiV u : u \in `]a, b[ ->
    derivable (fun x : R => (phi x a)^-1) u 1.
  move=> uab.
  apply: derivableV => //; first by rewrite expR_eq0.
  apply: diff_derivable. (* TODO: lemma derivable_comp *)
  apply: differentiable_comp => /=; last first.
    exact/derivable1_diffP/derivable_expR.
  exact/derivable1_diffP/derivable_int_mu.
have H u : u \in `]a, b[ ->
  ('D_1 z u - mu u * z u) * (phi u a)^-1 =
  'D_1 (fun t0 => z t0 * (phi t0 a)^-1) u.
  move=> uab/=.
  rewrite [in RHS]deriveM//=; last 2 first.
    exact: derivable_z.
    exact: derivablephiV.
  rewrite [in RHS]addrC.
  rewrite [in LHS]mulrBl [X in X - _]mulrC; congr (_ + _).
  rewrite mulrAC mulrC -mulrN; congr (_ * _).
  rewrite [X in 'D_1 X u](_ : _ =
    (fun x => expR (- \int[lm]_(tau in `[a, x]) mu tau))); last first.
    by apply/funext => w; rewrite expRN.
  rewrite -derive1E derive1_comp//; last first.
    exact/derivableN/derivable_int_mu.
  rewrite derive1E derive1_comp//; last exact: derivable_int_mu.
  rewrite derive1N// derive1_id mulN1r/=.
  rewrite (@continuous_FTC1 _ _ (BLeft a) _ b _ _ _ _).2 //=; first last.
  - by move: uab; rewrite inE; exact: within_continuous_continuous.
  - by rewrite lte_fin; move: uab; rewrite inE => /itvP ->.
  - by apply: continuous_compact_integrable mu_cont; exact: segment_compact.
  - by move: uab; rewrite inE => /itvP ->.
  rewrite -mulNr [in RHS]mulrC; congr (_ * _).
  by rewrite -expRN -[in LHS]derive_expR.
have {}eqn u : u \in `]a, b[ ->
    'D_1 (fun t0 => z t0 / phi t0 a) u = f u / phi u a.
  move=> uab.
  rewrite -eqn//.
  rewrite deriveM/=; last 2 first.
    exact: derivable_z.
    exact: derivablephiV.
  rewrite [in RHS]mulrBl.
  rewrite [in LHS]addrC [X in X + _ = _]mulrC; congr (_ + _).
  rewrite -[in RHS]mulrA [in RHS]mulrCA -[in RHS]mulrN; congr (_ * _).
  rewrite [X in 'D_1 X u](_ : _ =
      (fun x => expR (- \int[lm]_(tau in `[a, x]) mu tau))); last first.
    by apply/funext => w; rewrite expRN.
  rewrite -derive1E derive1_comp//; last exact/derivableN/derivable_int_mu.
  admit.
suff: z t / phi a t =
     fine (\int[lm]_(z0 in `]a, t[) (phi t z0 * f z0)%:E) / phi t a.
  admit.
transitivity (\int[lm]_(z0 in `]a, t[)
    'D_1 (fun t0 => z t0 / phi t0 a) z0) => /=.
  admit.
transitivity ((\int[lm]_(z0 in `]a, t[)
    ((phi t z0 * f z0) / phi t a))); last first.
  rewrite RintegralZr//=.
  admit.
apply: eq_Rintegral => u uat.
rewrite eqn; last first.
  rewrite 2!inE in uat *.
  by apply: subset_itvl uat; rewrite bnd_simp (itvP tab).
rewrite mulrAC mulrC; congr (_ * _).
rewrite /phi -expRB -expRN; congr expR.
rewrite -opprB; congr (- _).
apply/esym/eqP; rewrite subr_eq.
rewrite [in X in _ + X]/Rintegral -integral_itv_obnd_cbnd//=; last first.
  apply/measurable_EFinP.
  admit.
rewrite -[X in _ + X]/(Rintegral lm _ _) -Rintegral_setU//.
- rewrite inE in uat.
  by rewrite -itv_bndbnd_setU// ?bnd_simp// (itvP uat).
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
Admitted.

Lemma gronwall :
  (forall t, t \in `]a, b[ ->
    y t <= lambda t + \int[lm]_(s in `[a, t]) (mu s * y s)) ->
  forall t, t \in `]a, b[ ->
    y t <= lambda t +
      \int[lm]_(s in `[a, t])
        (lambda s * mu s * expR (\int[lm]_(tau in `[s, t]) mu tau)).
Proof.
move=> lambdamuy t tab.
pose z t := \int[lm]_(s in `[a, t]) (mu s * y s).
pose v t := z t + lambda t - y t.
have v_ge0 : forall x, x \in `]a, b[ -> 0 <= v x.
  move=> x xab.
  rewrite /v subr_ge0 (le_trans (lambdamuy _ _))//.
  by rewrite  addrC lerD2l.
have FTC1z : forall x, x \in `]a, b[ ->
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
  apply: continuousM.
    apply: (@within_continuous_continuous _ _ _ a b) => //.
    by rewrite inE in xab.
  apply: (@within_continuous_continuous _ _ _ a b) => //.
  by rewrite inE in xab.
have derivez : forall x, x \in `]a, b[ ->
    derive z x 1 = mu x * z x + mu x * lambda x - mu x * v x.
  move=> x xab.
  rewrite -derive1E.
  rewrite (FTC1z _ _).2//.
  rewrite /v.
  by field.
pose phi (t s : R) := expR (\int[lm]_(tau in `[s, t]) mu tau).
have za0 : z a = 0 by rewrite /z set_itv1// Rintegral_set1.
have zE : forall x, x \in `]a, b[ ->
    z x = \int[lm]_(s in `[a, x]) (phi x s * (mu s * lambda s - mu s * v s)).
  move=> x xab.
  apply: solve_diff_equa => //.
  admit.
  by move=> u uab; rewrite derivez// addrA.
have phimuv : forall x, x \in `]a, b[ ->
      0 <= \int[lm]_(s in `[a, x]) (phi t s * mu s * v s).
  move=> x xab.
  rewrite /Rintegral integral_itv_bndoo//=; last first.
    admit.
  apply: Rintegral_ge0 => //= u uab.
  rewrite -mulrA mulr_ge0// ?expR_ge0// mulr_ge0 ?v_ge0//.
    rewrite mu_ge0// inE; apply: subset_itv uab; rewrite bnd_simp//.
    rewrite inE in xab; move/itvP in xab.
    by rewrite xab.
  rewrite inE.
  apply: subset_itvl uab; rewrite bnd_simp.
  rewrite inE in xab; move/itvP in xab.
  by rewrite xab.
rewrite (le_trans (lambdamuy _ _))// lerD2l -/(z t).
rewrite zE//.
apply: (@le_trans _ _ (\int[lm]_(s in `[a, t]) (phi t s * mu s * lambda s)
                   - \int[lm]_(s in `[a, t]) (phi t s * mu s * v s))).
  rewrite -RintegralB//=; last 2 first.
    admit.
    admit.
  apply: le_Rintegral => //=.
    admit.
    admit.
  move=> u uat.
  rewrite mulrBr.
  rewrite le_eqVlt; apply/orP; left; apply/eqP.
  by field.
rewrite lerBlDl.
rewrite ler_wpDl//.
  by apply: phimuv.
rewrite le_eqVlt; apply/orP; left; apply/eqP.
apply: eq_Rintegral => //= u uat.
rewrite -/(phi t u).
by field.
Admitted.

Lemma gronwall_LAMBDA LAMBDA :
  (forall t, t \in `]a, b[ ->
    y t <= LAMBDA + \int[lm]_(s in `[a, t]) (mu s * y s)) ->
  forall t, t \in `]a, b[ ->
    y t <= LAMBDA * expR (\int[lm]_(tau in `[a, t]) mu tau).
Proof.
Abort.

Lemma gronwall_MU LAMBDA MU :
  (forall t, t \in `]a, b[ ->
    y t <= LAMBDA + \int[lm]_(s in `[a, t]) (MU * y s)) ->
  forall t, t \in `]a, b[ ->
    y t <= LAMBDA * expR (MU * (t - a)).
Proof.
Abort.

End gronwall.

Section thm34.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variables (phi psi : R -> U -> U) (a b : R) (ab : a < b) (k : R).
Variables (u0 v0 : U) (r : {posnum R}) (r1 : r%:num < 1) .
Let B : set U := closed_ball u0 r%:num. (* open connected set? *)
Hypothesis (k0 : 0 < k)
  (lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)})
  (cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}).
Variables y z : R -> U.
Hypothesis soly : is_sol_oo phi u0 a b y.
Hypothesis solz : is_sol_oo (phi \+ psi) v0 a b z.
Hypothesis By : y @` `[a, b] `<=` B.
Hypothesis Bz : z @` `[a, b] `<=` B.
Variable mu : {posnum R}.
Hypothesis mu_ub : forall t x, t \in `[a, b] -> x \in B ->
 `| psi t x | <= mu%:num.

Let gamma := `|u0 - v0|.
Lemma thm34 t : t \in `[a, b] ->
  `|y t - z t| <= gamma * expR (k * (t - a)) + mu%:num / k * (expR (k * (t - a)) - 1).
Proof.
move=> tab.
have yint : forall t, y t = u0 + \vint[lebesgue_measure]_(s in `[a, t]) phi s (y s).
  admit.
have zint : forall t, z t = v0 +
    \vint[lebesgue_measure]_(s in `[a, t]) (phi s (z s) + psi s (z s)).
  admit.
pose gronwall_y t := `|y t - z t|.
rewrite -/(gronwall_y t).
have : gronwall_y t <= gamma + mu%:num * (t - a) +
    \int[lebesgue_measure]_(s in `[a, t])
      (k * (gamma + mu%:num * (s - a)) * expR (k * (t - s))).
  have H : gronwall_y t <= (gamma + mu%:num * (t - a) +
      \int[lebesgue_measure]_(s in `[a, t]) (k * `|y s - z s|)).
    apply: (@le_trans _ _ (gamma +
      \int[lebesgue_measure]_(s in `[a, t]) `|phi s (y s) - psi s (z s)| +
      \int[lebesgue_measure]_(s in `[a, t]) `|psi s (z s)|)).
      admit.
    admit.
  pose lambda t := gamma + mu%:num * (t - a).
  pose mu' (s : R) : R := k.
  have := @gronwall _ _ _ ab lambda mu' _ _ _ gronwall_y.
  admit.
move/le_trans; apply.
apply: (@le_trans _ _
  (gamma + mu%:num * (t - a) - gamma - mu%:num * (t - a) +
    gamma * expR (k * (t - a)) +
    \int[lebesgue_measure]_(s in `[a, t]) (mu%:num * expR (k * (t - s))))).
  admit. (* ipp *)
rewrite le_eqVlt; apply/orP; left; apply/eqP.
admit.
Admitted.

End thm34.
