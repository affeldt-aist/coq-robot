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
  ode_contseg picard_contraction.

(**md**************************************************************************)
(* # Proof of the Cauchy-Lipschitz theorem                                    *)
(*                                                                            *)
(* The main purpose of this file is to formalized the (local)                 *)
(* Cauchy-Lipschitz theorem (a.k.a. Picard-Lindelof).                         *)
(*                                                                            *)
(* We consider an ODE defined by phi : K -> 'rV[K]_n -> 'rV[K]_n.             *)
(* The idea of the proof is to define a function                              *)
(* picard := fun t => u0 + \vint[mu]_(x in `[a, t]) phi x (g x)               *)
(* and to study the solution of the integral equation g t = picard t.         *)
(*                                                                            *)
(* `sol_is_deriv phi A f`                                                     *)
(* : f satisfies the ODE phi over the interval A                              *)
(*                                                                            *)
(* `is_sol phi A f`                                                           *)
(* : `sol_is_deriv phi A` and `f` continuous within `closure A`               *)
(*                                                                            *)
(* `is_sol_cauchy phi a b u0 f`                                               *)
(* : f is a solution of the Cauchy problem `(phi, a, u0)` over the interval   *)
(* : `]a,b|`, `b` can be closed, open, or $+\infty$                           *)
(*                                                                            *)
(* `is_sol_cauchy_oo`                                                         *)
(* : specialization of `is_sol_cauchy` to an open interval                    *)
(*                                                                            *)
(* `is_sol_integral phi a b u0 f`                                             *)
(* : f(a) = u0 and f(t) = f(a) + \int_(s in [a,t]) phi s (f s) on [a,b]       *)
(*                                                                            *)
(* `picard_fix`                                                               *)
(* : fixpoint of the integral equation defined by picard                      *)
(*                                                                            *)
(* `is_sol_cauchy_sym phi t0 d u0 f`                                          *)
(* : f is a solution of of the Cauchy problem `(phi, t0, u0)` over the        *)
(* : interval `]t0 - d, t0 + d[`                                              *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Definition row_vector {R : realType} (n : nat) := 'rV[R]_n.

HB.instance Definition _ {R : realType} n :=Complete.on (@row_vector R n).
HB.instance Definition _ {R : realType} n := NormedModule.on (@row_vector R n).
(*HB.instance Definition _ {R : realType} (n : nat) := CompleteNormedModule.on (@row_vector R n).*)

Section is_sol_itv.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U).

Definition sol_is_deriv (A : interval R) (f : R -> U) :=
  {in A, forall t, derivable f t 1 /\ f^`() t = phi t (f t)}.

Definition is_sol (A : interval R) (f : R -> U) :=
  sol_is_deriv A f /\ {within (closure [set` A]), continuous f}.

End is_sol_itv.

Section is_sol.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U).

Definition sol_is_deriv_cbnd (a : R) (b : itv_bound R) (f : R -> U) :=
  sol_is_deriv phi (Interval (BLeft a) b) f.

Definition sol_is_deriv_co a b := sol_is_deriv_cbnd a (BLeft b).

Lemma sol_is_deriv_cy_co a b : sol_is_deriv phi `[a, +oo[%R `<=`
  sol_is_deriv_cbnd a (BLeft b).
Proof.
move=> f + t tab; apply.
exact: subset_itvl tab.
Qed.

Definition sol_is_deriv_obnd (a : R) (b : itv_bound R) (f : R -> U) :=
  sol_is_deriv phi (Interval (BRight a) b) f.

(*Definition sol_is_deriv_oo a b := sol_is_deriv_obnd a (BLeft b).*)

(*NB: b = (BLeft r) is open,
      b = (BRight r) is closed,
      b = +oo%R is +oo *)
Definition is_sol_cauchy (a : R) (b : itv_bound R) (u0 : U) (f : R -> U) :=
  f a = u0 /\ is_sol phi (Interval (BRight a) b) f.

Definition is_sol_cauchy_oo a b u0 := is_sol_cauchy a (BLeft b) u0.

End is_sol.

Section is_sol_cauchy_oo_lemmas.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U).

Lemma empty_itv_is_sol_cauchy (a b : R) u0 f : b <= a -> f a = u0 ->
  is_sol_cauchy_oo phi a b u0 f.
Proof.
move=> ba f0; split; first by [].
split.
  move => t; rewrite in_itv/= => /andP[ta tb].
  by have := lt_trans ta tb; rewrite ltNge ba.
rewrite set_itv_ge; first by rewrite -leNgt bnd_simp.
by rewrite closure0; exact: continuous_subspace0.
Qed.

Lemma is_sol_cauchy_oo_subset (a b c d : R) u0 f : a <= c -> d <= b ->
  is_sol_cauchy_oo phi a b u0 f -> is_sol_cauchy_oo phi c d (f c) f.
Proof.
move=> ac bd is_sol_f; split; first reflexivity.
split.
- move=> x xcd; apply is_sol_f.
  by apply: subset_itv xcd; rewrite bnd_simp.
- have [_ [_ +]] := is_sol_f.
  exact/continuous_subspaceW/closureS/subset_itv.
Qed.

Lemma eq_is_sol_cauchy_oo (a b : R) u0 f1 f2 :
  a <= b -> {in `[a, b]%R, f1 =1 f2} ->
  is_sol_cauchy_oo phi a b u0 f1 -> is_sol_cauchy_oo phi a b u0 f2.
Proof.
move => ab hs [f1a [derf1 cont1]]; split.
- by rewrite -f1a hs// bound_itvE.
- split.
  + move=> t tab; split.
    * apply/near_eq_derivable/(derf1 _ tab).1 => //.
      near=> t'.
      apply hs.
      apply: subset_itv_oo_cc.
      by near: t'; exact: near_in_itvoo.
    * have f1f2 :  {in `]a, b[%R, f1 =1 f2}.
        move=> t' tab'.
        apply hs.
        exact: subset_itv_oo_cc.
      rewrite -f1f2// -[LHS](@in_eq_derive1 _ _ `]a, b[ f1) //.
      - by move=> x; rewrite inE; exact: f1f2.
      - by rewrite inE.
      - by apply derf1.
  + apply: subspace_eq_continuous cont1.
    move: ab; rewrite le_eqVlt => /predU1P[->|ab].
      by rewrite set_itv_ge ?bnd_simp// => x; rewrite closure0 inE.
    rewrite closure_itvoo// => x.
    by rewrite inE => /hs.
Unshelve. all: by end_near. Qed.

End is_sol_cauchy_oo_lemmas.

Section is_sol_integral.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U).

(* TODO: is this a good way to define it with the extra sol a = u0G?  *)
Definition is_sol_integral (f : R -> U) := f a = u0 /\
  {in `[a, b]%R, forall t, f t = f a + \vint[mu]_(s in `[a, t]) phi s (f s)}.

End is_sol_integral.

Section integral_sol_between.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (f : R -> U).

Import MeasurableR.

Hypothesis int_phi_f : forall i,
  mu.-integrable `[a, b] (EFin \o (fun x => phi x (f x) ord0 i)).

(* NB: not used *)
Lemma integral_sol_between : is_sol_integral phi a b u0 f ->
  forall s t,
    s \in `[a, b]%R ->
    t \in `[s, b]%R ->
    f t = f s + \vint[mu]_(x in `[s, t]) phi x (f x).
Proof.
move=> [fau0 fE] s t sab tsb.
have as' : a <= s by rewrite (itvP sab).
have st : s <= t by rewrite (itvP tsb).
have tb : t <= b by rewrite (itvP tsb).
have tab : t \in `[a, b]%R by rewrite in_itv /= (le_trans as' st) tb.
have ast : a <= s <= t by rewrite as' st.
have int_phi_f' i :
    mu.-integrable `[a, t] (EFin \o (fun x => phi x (f x) ord0 i)).
  apply: (@integrableS _ _ _ _ `[a, b]) => //.
  exact: subset_itvl.
by rewrite (fE t tab) (fE s sab) -addrA -rowRintegral_itv_split.
Qed.

End integral_sol_between.

(* NB: not used *)
(* if the rhs function is bounded, it is Lipschitz *)
Section bounded_rhs_lipschitz.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
 (u0 : U) (f : R -> U) (M : R).
Hypothesis M0 : 0 <= M.

Import MeasurableR.

Hypothesis int_phi_f : forall i,
  mu.-integrable `[a, b] (EFin \o (fun x => phi x (f x) 0 i)).

Hypothesis rhs_bound : {in `[a, b]%R, forall x, `| phi x (f x) | <= M}.

(* TODO: PR? *)
Lemma norm_rowRintegral_le_cst s t : s \in `[a, b]%R -> t \in `[s, b]%R ->
  `| \vint[mu]_(x in `[s, t]) phi x (f x) | <= M * (t - s).
Proof.
move=> sab tsb.
have st_ab : `[s, t] `<=` `[a, b].
  by apply/subset_itv; rewrite bnd_simp; rewrite ?(itvP sab) ?(itvP tsb).
rewrite /Num.norm /= mx_normrE; apply: bigmax_le => //=.
  by rewrite mulr_ge0 // subr_ge0 (itvP tsb).
move=> -[i j] _ /=.
rewrite {i}(ord1 i) /= rowRintegralE (le_trans (le_normr_Rintegral _ _))//=.
  exact: (@integrableS _ _ _ _ `[a, b]).
apply: (@le_trans _ _ (\int[mu]_(x in `[s, t]) M)) => //=.
  apply: le_Rintegral => //=.
  - by apply: (@integrableS _ _ _ _ `[a, b] ) => //; first exact: integrable_norm.
  - apply: integrable_cst => //=.
    by rewrite lebesgue_measure_itv /=; case: ifPn => //=;rewrite  ltry.
  - move=> x xst.
    apply (@le_trans _ _ `| phi x (f x) |); last exact: (rhs_bound (st_ab _ xst)).
    by rewrite {2}/Num.norm /= mx_normrE /= (le_bigmax _ _ (ord0, j)).
rewrite Rintegral_cst //= lebesgue_measure_itv /= ler_wpM2l//.
by case: ifPn => //= _; rewrite subr_ge0 (itvP tsb).
Qed.

Lemma is_sol_integral_lipschitz : is_sol_integral phi a b u0 f ->
  forall s t, s \in `[a, b]%R -> t \in `[s, b]%R ->
    `| f t - f s | <= M * (t - s).
Proof.
move=> Hsol s t sab tsb.
rewrite (@integral_sol_between _ _ phi a b u0 f int_phi_f Hsol s t sab tsb).
rewrite addrC addrA (addrC _ (f s)) subrr add0r.
exact: norm_rowRintegral_le_cst.
Qed.

End bounded_rhs_lipschitz.

(* is_sol_cauchy_oo -> is_sol_integral *)
Section is_sol_cauchy_integral.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 u0' : U) (r : {posnum R}) (k : R) (f : R -> U).

Hypothesis ab : a <= b.
Let B := closed_ball u0' r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.

Hypothesis cont_f : {within `[a, b], continuous f}.
Hypothesis f_bound : f @` `[a, b] `<=` B.

Lemma within_continuous_ODE i :
  {within `[a, b], continuous (fun x => phi x (f x) 0 i)}.
Proof.
apply/within_continuous_coord : i => /=.
exact: (within_continuous_lipschitz cont1 lip2 cont_f).
Qed.

Lemma is_sol_cauchy_integral :
  is_sol_cauchy_oo phi a b u0 f -> is_sol_integral phi a b u0 f.
Proof.
move => [hinit h]; split => // t tab.
have /= := tab; rewrite in_itv/= => /andP[ta tb].
apply/rowP => i.
rewrite mxE rowRintegralE.
move: ta; rewrite le_eqVlt => /predU1P[<-|ta].
  by rewrite set_itv1 Rintegral_set1 addr0.
rewrite /Rintegral.
have cont_fi : {within `[a, b], continuous (fun x => f x 0 i)}.
  by move: i; exact/within_continuous_coord.
rewrite (@continuous_FTC2 _ (fun x => phi x (f x) 0 i)
    (fun x => f x 0 i) _ _ ta).
- apply: continuous_subspaceW; last exact: within_continuous_ODE.
  exact: subset_itvl.
- split.
  + move=> t' tx'.
    by have /h.1[/derivable_mxP] : t' \in `]a, b[%R by exact/subset_itvl/tx'.
  + have ab' : a < b by rewrite (lt_le_trans ta).
    by move /(continuous_within_itvP _ ab') : cont_fi => [_ + _].
  + have cont_phii' : {within `[a, t], continuous fun x0 => f x0 0 i}.
      apply: continuous_subspaceW; last exact: cont_fi.
      exact: subset_itvl.
    by move/(continuous_within_itvP _ ta) : cont_phii' => [_ _ +].
- move=> x xt.
  have /h.1[? +] : x \in `]a, b[%R by exact/subset_itvl/xt.
  by rewrite !derive1E derive_mx//= => <-; rewrite mxE.
- by rewrite -EFinB subrKC.
Unshelve. all: by end_near. Qed.

End is_sol_cauchy_integral.

(* is_sol_integral -> is_sol_cauchy_oo *)
Section is_sol_integral_cauchy.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (f : R -> U).

Hypothesis ab : a <= b.
Hypothesis k0 : k != 0.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.

Hypothesis cont_f : {within `[a, b], continuous f}.
Hypothesis f_bound : f @` `[a, b] `<=` closed_ball u0 r%:num.

Lemma continuous_ODE i t : t \in `]a, b[%R ->
  {for t, continuous (fun x => phi x (f x) ord0 i)}.
Proof.
move/within_continuous_continuous_new; apply => //.
exact: (within_continuous_ODE cont1 lip2).
Qed.

Import MeasurableR.

Lemma integrable_ODE i :
  mu.-integrable `[a, b] (EFin \o (fun x => phi x (f x) 0 i)).
Proof.
apply: continuous_compact_integrable; first exact: segment_compact.
exact: (within_continuous_ODE cont1 lip2).
Qed.

Lemma is_sol_integral_cauchy :
  is_sol_integral phi a b u0 f -> is_sol_cauchy_oo phi a b u0 f.
Proof.
move => [hinit h].
split; first by [].
split; last first.
  apply: continuous_subspaceW cont_f.
  exact: itv_closure (* TODO: why not equality? *).
move=> t tab.
move: (tab).
have -> : f^`() t  = (fun x => f a + \vint[mu]_(s in `[a, x]) phi s (f s))^`() t.
  apply: (@in_eq_derive1 _ _ `]a, b[) => //; last by rewrite inE.
  move=> x xab; apply: h.
  by rewrite inE in xab; exact: subset_itv_oo_cc xab.
suff hi : forall i, derivable (fun x => f x 0 i) t 1 /\
  (fun x => (f a + \vint[mu]_(s in `[a, x]) phi s (f s))%R)^`() t 0 i =
    phi t (f t) 0 i.
  split.
    apply /derivable_mxP => i j.
    have [? _] := hi j.
    by rewrite ord1.
  apply/rowP => j.
  by have [_ ?] := hi j.
move => j.
move: (tab); rewrite in_itv => /= /andP[ta tb].
have [H1 H2] := @continuous_FTC1_closed _ (fun x => phi x (f x) 0 j)
  a t b tb (integrable_ODE j) ta (continuous_ODE tab).
have Hderivable : derivable (fun x => \vint[mu]_(x0 in `[a, x]) phi x0 (f x0)) t 1.
  apply/(@derivable_mxP R R) => i0 i; rewrite (ord1 i0){i0}/=.
  have [?] := @continuous_FTC1_closed _ (fun x => phi x (f x) 0 i)
    a t b tb (integrable_ODE i) ta (continuous_ODE tab).
  rewrite /rowRintegral.
  rewrite [X in derivable X t 1](_ : _ =
    (fun x => \int[mu]_(y in `[a, x]) phi y (f y) 0 i))//.
  by apply/funext => x; rewrite mxE.
rewrite derive1E deriveD /=.
- exact: derivable_cst.
- exact: Hderivable.
split.
   apply: (near_eq_derivable
       (f := fun x => (f a + \vint[mu]_(s in `[a, x]) phi s (f s)) 0 j)) => /=.
     near=> t'.
     rewrite (h t')//= in_itv/=.
     apply/andP; split.
     - by apply: ltW; near: t'; exact: lt_nbhsr.
     - by apply: ltW; near: t'; exact: lt_nbhsl.
  have -> : (fun x => (f a + \vint[mu]_(s in `[a, x]) phi s (f s)) 0 j) =
            cst (f a 0 j) +
            (fun x => (\vint[mu]_(s in `[a, x]) (phi s (f s))) 0 j).
    by apply funext => x; rewrite mxE.
  apply: derivableD.
    exact: derivable_cst.
  move/derivable_mxP : Hderivable.
  by apply.
rewrite -!derive1E derive1_cst add0r -H2 !derive1E derive_mx//= mxE/=.
congr ('D_1 _ t).
by apply/funext => t'; rewrite mxE.
Unshelve. all: by end_near. Qed.

End is_sol_integral_cauchy.

Section picard_fix.
Local Notation mu := lebesgue_measure.
Context {R : realType} {n} (U := @row_vector R n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).

Hypothesis ab : a <= b.
Hypothesis k0 : 0 <= k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis rho1 : rho%:num < 1.

Import ContSeg_quot.

Check U : completeType.
Check U : completePseudoMetricType R.
Check U : normedModType R.
Check U : completeNormedModType R.

Local Notation safe_dist := (safe_dist phi a b u0 r%:num k rho%:num).
Local Notation V := (@quot_contSeg R a (a + safe_dist) U).

Check V : completeNormedModType _.

Local Notation img_cball := (@img_cball R n phi a b u0 r k rho).
Local Notation img_cball_nonempty := (img_cball_nonempty phi a b u0 r k rho).
Local Notation closed_img_cball := (@closed_img_cball R n phi a b u0 r k rho k0 ab).

Local Notation picard := (@picard _ _ _ a b u0 r k rho cont1 lip2 k0).

Definition picard_fix : V :=
  sval (cid2 (@banach_fixed_point R V img_cball
    picard
    (@is_contraction_picard _ n phi a b u0 r k rho ab k0 cont1 lip2 rho1)
    closed_img_cball
    img_cball_nonempty)).

Let picard_fixE : picard_fix = picard picard_fix.
Proof. by rewrite {}/picard_fix; case: cid2. Qed.

Lemma img_cball_picard_fix : img_cball picard_fix.
Proof.
by apply (svalP (cid2 (@banach_fixed_point R V img_cball _
  (@is_contraction_picard _ _ _ _ _ u0 r k _ ab k0 cont1 lip2 rho1)
  closed_img_cball img_cball_nonempty))).
Qed.

Lemma picard_fix_init : picard_fix a = u0.
Proof.
rewrite picard_fixE eval_mod_on_itv.
  by rewrite in_itv/= lexx leDl_safe_dist// ltW.
by rewrite /picard_fun /= picard_fun_init//; exact: img_cball_picard_fix.
Qed.

Lemma picardE g t : img_cball g -> t \in `[a, a + safe_dist]%R ->
  picard g t = u0 + \vint[mu]_(x in `[a, t]) phi x (g x).
Proof.
by move=> Hg taad; rewrite eval_mod_on_itv//; exact: picard_funE.
Qed.

Lemma cauchy_lipschitz_integral_version :
  is_sol_integral phi a (a + safe_dist) u0 picard_fix.
Proof.
split; first exact: picard_fix_init.
move=> t tad.
rewrite {1}picard_fixE// eval_mod_on_itv//.
rewrite picard_fix_init.
exact: picard_funE img_cball_picard_fix.
Qed.

Theorem picard_fix_unique (picard_fix' : V) : img_cball picard_fix' ->
  (forall t, t \in `[a, a + safe_dist]%R ->
  picard_fix' t = u0 + \vint[mu]_(x in `[a, t]) phi x (picard_fix' x)) ->
  picard_fix = picard_fix'.
Proof.
move=> imgpicard_fix'_cball h.
apply: (contraction_fixpoint_unique
  (@is_contraction_picard _ _ _ a b u0 r k rho ab k0 cont1 lip2 rho1)
  img_cball_picard_fix imgpicard_fix'_cball) => //=.
rewrite -(reprK picard_fix').
apply/eqquotP.
rewrite /Quotient.equiv/=.
rewrite inE.
apply/funext => x.
rewrite /patch mem_setE; case: ifPn => [xK|xKnot]; last by [].
rewrite /fun_of_quot_contSeg/=.
rewrite !fctE.
rewrite !reprK.
rewrite picard_funE//=.
rewrite (_ : repr picard_fix' x = picard_fix' x)//.
by rewrite h// subrr.
Qed.

Import MeasurableR.

Lemma cauchy_lipschitz_quot_ex : picard_fix a = u0 /\
  {in `]a, a + safe_dist[%R, forall x, picard_fix^`() x = phi x (picard_fix x)}.
Proof.
split; first exact: picard_fix_init.
move => t tad.
rewrite {1}picard_fixE.
apply/rowP => j.
suff -> : (picard picard_fix)^`() t =
          (fun t => u0 + \vint[mu]_(x in `[a, t]) phi x (picard_fix x))^`() t.
  move: (tad); rewrite in_itv /= => /andP[ta tadelta].
  have Fint i : mu.-integrable `[a, a + safe_dist]
      (EFin \o (fun x => phi x (picard_fix x) ord0 i)).
    apply: integrable_comp => //.
      by rewrite in_itv /= lexx andbT leDl_safe_dist// ltW.
    exact: img_cball_picard_fix.
  have Fcont i : {for t, continuous (fun x => phi x (picard_fix x) ord0 i)}.
    move: tad; rewrite inE.
    apply/within_continuous_continuous_new => //=.
     by rewrite leDl_safe_dist// ltW.
    clear Fint.
    move: i; apply/within_continuous_coord.
    apply: (@within_continuous_lipschitz _ _ _ a _ u0 r k).
    + exact: cont1_safe_dist.
    + exact: lip2_safe_dist.
    + exact: continuous_fun.
    + exact: img_cball_picard_fix.
  have [H1 H2] := @continuous_FTC1_closed _ (fun x => phi x (picard_fix x) 0 j)
                  a t _ tadelta (Fint j) ta (Fcont j).
  have Hderivable : derivable (fun x => \vint[mu]_(y in `[a, x]) phi y (picard_fix y)) t 1.
    apply/derivable_mxP => i0 i; rewrite (ord1 i0){i0}/=.
    have [?] := @continuous_FTC1_closed _ (fun x => phi x (picard_fix x) 0 i)
                a t _ tadelta (Fint i) ta (Fcont i).
    rewrite /rowRintegral.
    rewrite [X in derivable X t 1](_ : _ =
        (fun x => \int[mu]_(y in `[a, x]) phi y (picard_fix y) 0 i))//.
    by apply/funext => x; rewrite mxE.
  rewrite derive1E deriveD /=.
    exact: derivable_cst.
    exact: Hderivable.
  rewrite -!derive1E derive1_cst add0r -H2 !derive1E derive_mx// mxE/=.
  congr ('D_1 _ t).
  by apply/funext => t0; rewrite mxE.
rewrite /picard /picard_fun.
apply: (@in_eq_derive1 _ _ `]a, a + safe_dist[) => //; last by rewrite inE.
move=> {}t {}tad.
rewrite -(@picard_funE _ _ _ a b _ r k rho cont1 lip2)//=.
  exact: img_cball_picard_fix.
rewrite eval_mod_on_itv// inE; apply: subset_itv_oo_cc.
by rewrite inE in tad.
Qed.

Lemma cauchy_lipschitz_in_cball (t : R) : `[a, a + safe_dist] t ->
  closed_ball u0 r%:num (picard_fix t).
Proof. by move=> taad; apply: img_cball_picard_fix => /=; exists t. Qed.

End picard_fix.

Section picard_extension.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b c : R)
  (u0 : U) (f1 f2 : R -> U).
Notation mu := lebesgue_measure.

Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis cont1 : {within `[a, b], continuous (fun x => phi x (f1 x))}.
Hypothesis cont2 : {within `[b, c], continuous (fun x => phi x (f2 x))}.
Hypothesis matchb : f1 b = f2 b.

Lemma is_sol_integral_patch :
  is_sol_integral phi a b u0 f1 ->
  is_sol_integral phi b c (f1 b) f2 ->
  is_sol_integral phi a c u0 (patch f2 `[a, b] f1).
Proof.
move => [p0a p0s ] [p1a p1s].
have h0 : patch f2 `[a, b] f1 a = u0.
  rewrite /patch.
  case: ifPn => [xK | xKnot] => //.
  move /negP : xKnot.
  by rewrite inE/=in_itv/=lexx ltW.
split=> //.
move=> t tac.
rewrite /patch mem_setE bound_itvE (ltW ab).
case: ifPn => [xK | xKnot] => /=.
  rewrite p0s // p0a.
  apply/rowP => i.
  rewrite !mxE.
  congr (_ + _)%R.
  apply eq_Rintegral => /= x xat.
  suff -> : x \in `[a, b]%R by [].
  move : xat xK.
  rewrite mem_setE /= !in_itv /= => /andP [xat1 xat2] /andP [tab1 tab2].
  apply/andP; split => //.
  exact/le_trans/tab2.
have tbc : t \in `[b, c]%R.
  move : tac.
  move/negP : xKnot.
  rewrite !in_itv /=.
  have /orP := le_total b t.
  case => // -> h1 /andP [h2 ->] //.
  by move: h1; rewrite h2.
transitivity (f1 a + \vint[mu]_(s in `[a, t])
    phi s (if (s \in `[a, b])%classic then f1 s else f2 s))%R; last first.
  by under eq_rowRintegral do rewrite mem_setE.
rewrite (rowRintegral_itv_split (c := b) (F := (fun x => phi x (patch f2 `[a, b] f1 x)))).
- by rewrite ltW //=; move : tbc; rewrite in_itv/= => /andP [-> _].
- move=> i.
  have cont' : {within `[a, t], continuous (fun x => phi x (patch f2 `[a, b] f1 x) ord0 i)}.
    have -> : `[a, t] = `[a, b] `|` `[b, t].
      rewrite (@itv_bndbnd_setU _ _ _ (BRight b))// ?bnd_simp//=.
        exact: ltW.
        by rewrite (itvP tbc).
      apply/seteqP; split => x.
        move=> []; [by left|right].
        exact: subset_itv_oc_cc b0.
      move=> []; [by left|].
      rewrite -(setU1itv false) ?bnd_simp//.
        by rewrite (itvP tbc).
      case; [|by right].
      move=> ->; left => /=.
      by rewrite bound_itvE ltW.
    apply: (withinU_continuous (@itv_closed _ _ a b) (@itv_closed _ _ b t)).
      move : i.
      apply /within_continuous_coord.
      have eq1 : {in `[a, b], (fun x0 => phi x0 (f1 x0)) =1
                              (fun x0 => phi x0 (patch f2 `[a, b] f1 x0))}.
        move => x0 x0ab.
        by rewrite /patch x0ab.
      apply: (subspace_eq_continuous eq1).
      exact: cont1.
    move : i.
    apply /within_continuous_coord.
    have eq2 : {in `[b, c], (fun x0 => phi x0 (f2 x0)) =1
                            (fun x0 => phi x0 (patch f2 `[a,b] f1 x0))}.
      move => x0 x0ab.
      rewrite /patch mem_setE;case: ifPn => [xab | xabnot] => //.
      suff -> : x0 = b by rewrite matchb.
      apply: le_anti.
      move: x0ab xab.
      by rewrite inE/= !in_itv/= => /andP [-> _] /andP [_ ->].
    apply: (@continuous_subspaceW _ _ _ `[b, c]).
      by apply: subset_itvl; rewrite bnd_simp (itvP tbc).
    exact: (subspace_eq_continuous eq2).
  apply: continuous_compact_integrable => //.
  exact: segment_compact.
- rewrite p1s//.
  suff : f2 b = u0 + \vint[mu]_(s in `[a, b]) phi s (patch f2 `[a, b] f1 s).
    move=> ->.
    rewrite -p0a [in RHS]addrA; congr +%R.
    apply: eq_rowRintegral => /= x xbt.
    rewrite /patch; case: ifPn => //.
    rewrite inE/= in_itv/= => /andP [_ xb].
    move: xbt.
    rewrite inE /= in_itv/= => /andP[bx _].
    suff -> : x = b by rewrite p1a.
    by apply/eqP; rewrite eq_le xb/=.
  rewrite p1a p0s; first by rewrite in_itv/= ltW/=.
  rewrite p0a; congr (u0 + _)%R.
  rewrite /patch.
  by apply eq_rowRintegral => /= x ->.
Qed.

End picard_extension.

Section cauchy_lipschitz_local.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho : {posnum R}).

Hypothesis ab : a <= b.
Hypothesis k0 : 0 <= k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis rho1 : rho%:num < 1.

Let r2 := (r%:num/2)%:pos.
Let B2 := closed_ball u0 r2%:num.

Let ler2 : r2%:num <= r%:num.
Proof. by rewrite /r2/= ler_pdivrMr // ler_pMr // lerDl. Qed.

Let lip2' :  {in `[a, b]%R, forall x, k.-lipschitz_B2 (phi x)}.
Proof.
move => x abx /= y By.
apply: lip2.
by move : abx; rewrite !inE/=; apply subset_itvr.
split.
by apply /le_closed_ball/By.1.
by apply /le_closed_ball/By.2.
Qed.

Let cont1':  {in B2, forall y, {within `[a, b], continuous phi ^~ y}}.
Proof.
move => /= x Bx.
apply /continuous_subspaceW/cont1.
by [].
apply mem_set.
apply set_mem in Bx.
by apply /le_closed_ball/Bx.
Qed.

(* Let rho : {posnum R} := (2^-1)%:pos. *)

(* Let rho1 : rho%:num < 1. *)
(* Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed. *)

Local Notation safe_dist := (safe_dist phi a b u0 r2%:num k rho%:num).

Definition cauchy_lipschitz_f :
    continuousSubspaceType `[a, a + safe_dist] [set: 'rV[R]_n] :=
  repr (picard_fix ab k0 cont1' lip2' rho1).

Lemma is_sol_cauchy_lipschitz_f :
  is_sol_cauchy_oo phi a (a + safe_dist) u0 cauchy_lipschitz_f.
Proof.
apply/(@is_sol_integral_cauchy _ _ _ _ _ _ r k).
- by rewrite leDl_safe_dist// ltW.
- move=> /= x xB; apply/continuous_subspaceW/cont1 => //.
  by apply: subset_itvl => //=; rewrite bnd_simp -lerBrDl safe_dist_itv.
- move=> t td; apply: lip2.
  by apply: subset_itvl td; rewrite bnd_simp -lerBrDl safe_dist_itv.
- exact: continuous_fun.
- apply (subset_trans (B:=B2)).
    by move => _ [t tad] <-; exact: cauchy_lipschitz_in_cball.
  exact: le_closed_ball.
- exact: cauchy_lipschitz_integral_version.
Qed.

Lemma solution_stays_in_ball2 : {in `[a, a + safe_dist]%R,
  forall t, closed_ball u0 r2%:num (cauchy_lipschitz_f t)}.
Proof. by move=> t; move => /cauchy_lipschitz_in_cball; exact. Qed.

Lemma solution_stays_in_ball : {in `[a, a + safe_dist]%R,
  forall t, closed_ball u0 r%:num (cauchy_lipschitz_f t)}.
Proof. by move=> t ta; apply/le_closed_ball/solution_stays_in_ball2. Qed.

Lemma solution_continuous :
  {within `[a, a + safe_dist], continuous cauchy_lipschitz_f}.
Proof. exact: continuous_fun. Qed.

Let f := cauchy_lipschitz_f.

Theorem cauchy_lipschitz_ex : is_sol_cauchy_oo phi a (a + safe_dist) u0 f.
Proof.
apply/(@is_sol_integral_cauchy _ _ _ _ _ _ r k).
- by rewrite leDl_safe_dist.
- move=> /= x xB; apply/continuous_subspaceW/cont1 => //.
  apply: subset_itvl => //=.
  by rewrite bnd_simp -lerBrDl safe_dist_itv.
- move=> t td; apply: lip2.
  by apply: subset_itvl td; rewrite bnd_simp -lerBrDl safe_dist_itv.
- exact: continuous_fun.
- apply: (@subset_trans _ B2).
  by move => _ [t tad] <-; apply: cauchy_lipschitz_in_cball.
  by apply le_closed_ball.
- exact: cauchy_lipschitz_integral_version.
Qed.

Local Notation V := (@ContSeg_quot.quot_contSeg R a (a + safe_dist) U).

Lemma cauchy_lipschitz_unique_restr f' :
  {within `[a, a + safe_dist], continuous f'} ->
  {in `[a, a + safe_dist]%R, forall t, closed_ball u0 r2%:num (f' t)}
    (* i.e., other solutions also stay in the ball B *) ->
  is_sol_cauchy_oo phi a (a + safe_dist) u0 f' ->
  {in `[a, a + safe_dist]%R, f =1 f'}.
Proof.
move=> cont bnd.
move/(@is_sol_cauchy_integral _ _ _ _ _ u0 u0 r k) => [].
- move=> /= x xB.
  apply/continuous_subspaceW/cont1 => //.
  by apply: subset_itvl => //=; rewrite bnd_simp -lerBrDl safe_dist_itv.
- move=> t td; apply: lip2.
  by apply: subset_itvl td; rewrite bnd_simp -lerBrDl safe_dist_itv.
- exact: cont.
- apply: (@subset_trans _ B2).
    by move => _ [t tad] <-; exact: bnd.
  exact: le_closed_ball.
move=> f'au0 h1 t tab.
have fc : contseg `[a, a + safe_dist] f' by exact: mem_set.
have pieq : \pi_V%qT f = \pi_V%qT (contseg_Sub fc).
  rewrite reprK.
  apply: picard_fix_unique.
    move => /= _ [t' tad' ] <- /=.
    rewrite /ContSeg_quot.fun_of_quot_contSeg.
    suff -> : (repr (\pi_V%qT (contseg_Sub fc))) t' = f' t'.
      by apply: bnd; rewrite inE.
    by apply: ContSeg_quot.eval_mod_on_itv; rewrite inE.
  move=> t0 t0ad.
  rewrite ContSeg_quot.eval_mod_on_itv //=.
  rewrite h1//.
  rewrite f'au0; congr (u0 + _).
  apply: eq_rowRintegral => t' tad'.
  rewrite ContSeg_quot.eval_mod_on_itv //=.
  move: tad'; rewrite !inE/=;  apply: subset_itvl; rewrite bnd_simp.
  rewrite inE/= in t0ad.
  by move/itvP : t0ad => ->.
suff -> : f t = (ContSeg_quot.fun_of_quot_contSeg (\pi_V%qT (contseg_Sub fc))) t.
  rewrite /ContSeg_quot.fun_of_quot_contSeg/=.
  exact: ContSeg_quot.eval_mod_on_itv.
rewrite -pieq.
by rewrite ContSeg_quot.eval_mod_on_itv.
Qed.

End cauchy_lipschitz_local.

(* TODO: move *)
Section continuous_confined.
Context {R : realType} {n} (U := 'rV[R]_n) (a b : R) (u0 : U) (r : {posnum R}).
Hypothesis ab : a < b.
Let B := closed_ball u0 r%:num.

Local Lemma continuous_confined (g : R -> U) : {within `[a, b], continuous g} ->
  g a = u0 ->
  exists Delta : {posnum R}, {in `[a, a + Delta%:num], forall t, g t \in B}.
Proof.
move/(continuous_within_itvP _ ab)  => [cc cl cr] g0.
have : {within `[a,b], continuous (fun t => `| u0 - g t |) }.
  apply: within_continuous_comp_norm.
  apply/continuous_within_itvP => //=.
  split.
  - move => t tab.
    exact: (cvgB (cvg_cst _) (cc _ tab)).
  - exact: (cvgB (cvg_cst _) cl).
  - exact: (cvgB (cvg_cst _) cr).
move/(continuous_within_itvP _ ab) => [_ /cvgrPdist_le + _].
move=> /(_ r%:num ltac:(by []))[Delta /= Delta0].
rewrite /ball_/= g0 subrr normr0/= => H.
have D20 : 0 < Delta / 2 by rewrite divr_gt0.
exists (PosNum D20) => t.
rewrite inE/= in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<-|ta td].
  by rewrite g0 /B inE => _; exact: closed_ballxx.
have /= := H t.
rewrite add0r normrN normr_id.
rewrite inE /B closed_ballE /closed_ball_//=; apply => //.
rewrite ltr0_norm ?subr_lt0// opprB ltrBlDl.
by rewrite (le_lt_trans td)// ltrD2l gtr_pMr// invf_lt1// ltr1n.
Qed.

End continuous_confined.

Section solution_locally_unique.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R) (rho_max : {posnum R} := 2^-1%:pos)
  (f : R -> U).

Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.

Hypothesis cf : {within `[a, b], continuous f}.
Hypothesis sol1 : is_sol_cauchy_oo phi a b u0 f.

Let r2 := (r%:num/2)%:pos.
Let dmax (rho : {posnum R}) := safe_dist phi a b u0 r2%:num k rho%:num.
Let fc (rho : {posnum R}) :=
  cauchy_lipschitz_f (ltW ab) (ltW k0) lip2 cont1 (rho := rho).

Lemma initial_solution_unique f' : {within `[a, b], continuous f'} ->
  is_sol_cauchy_oo phi a b u0 f' ->
  exists D : {posnum R}, {in `[a, a + D%:num]%R, f =1 f'} /\
    {in `[a, a + D%:num]%R, forall t, closed_ball u0 r2%:num (f t)}.
Proof.
move => cf' sol2.
suff [rho [D [Hrho [Db P1 P2]]]] : exists rho D : {posnum R},
    exists (Hrho : rho%:num < 1),
    [/\ D%:num <= dmax rho,
        {in `[a, a + D%:num]%R, f =1 fc Hrho } &
        {in `[a, a + D%:num]%R, f' =1 fc Hrho} ].
  exists D; split => t tab; first by rewrite P1// P2.
  rewrite P1//.
  apply: solution_stays_in_ball2.
  by move: tab; rewrite !inE; apply: subset_itvl; rewrite bnd_simp lerD2l.
have [d1 D1] := continuous_confined r2 ab cf sol1.1.
have [d2 D2] := continuous_confined r2 ab cf' sol2.1.
have [rho drho1 drho2] : exists2 rho : {posnum R},
    dmax rho <= (Num.min d1%:num d2%:num) & rho%:num < 1.
  rewrite /dmax.
  pose k' := Num.min rho_max%:num
            (Num.min (k * rho_max%:num)
                     (k * (Num.min d1%:num d2%:num))).
  have posk : 0 < k'.
    rewrite lt_min//= invr_gt0/= ltr0n/=.
    by rewrite lt_min/= divr_gt0// mulr_gt0.
  exists (PosNum posk) => //=.
    rewrite unlock/=.
    rewrite minA !ge_min/=; apply/orP; right.
    rewrite !minr_pMl//=; [by rewrite ltW// invr_gt0..|].
    do 2 rewrite ge_min; apply/orP; right.
    apply/orP; right.
    by rewrite mulrAC divff ?mul1r// gt_eqF//.
  by rewrite gt_min invf_lt1// ltr1n.
have drho_pos : 0 < dmax rho by exact: safe_dist_gt0.
exists rho, (PosNum drho_pos), drho2; split => //.
- move => t tad.
  apply/esym; apply: cauchy_lipschitz_unique_restr.
  + apply/continuous_subspaceW/cf => //.
    apply: subset_itvl => //=.
    by rewrite bnd_simp -lerBrDl; apply safe_dist_itv.
  + move=> t0 t0ad.
    suff : f t0 \in closed_ball u0 r2%:num by rewrite inE.
    apply D1.
    move: t0ad; rewrite !inE/=; apply: subset_itvl; rewrite bnd_simp/=.
    by rewrite lerD2l// (le_trans drho1)// ge_min lexx.
  + split; first by apply sol1.
    split.
    * move=> t0 t0ad.
      have [_ [+ _]] := sol1; apply.
      by move: t0ad; rewrite !inE/=; apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
    * apply: continuous_subspaceW cf.
      apply: subset_trans; first exact: itv_closure.
      by apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
  + exact: tad.
move => t tad.
apply/esym; apply: cauchy_lipschitz_unique_restr.
- apply/continuous_subspaceW/cf' => //.
  by apply: subset_itvl => /=; rewrite bnd_simp -lerBrDl;apply safe_dist_itv.
- move=> t0 t0ad.
  suff : f' t0 \in closed_ball u0 r2%:num by rewrite inE.
  apply D2.
  move: t0ad; rewrite !inE; apply: subset_itvl; rewrite bnd_simp lerD2l.
  by rewrite (le_trans drho1)// ge_min lexx orbT.
- split; first by apply sol2.
  split.
  + move=> t0 t0ad.
    have [_ [+ _]] := sol2; apply.
    by move: t0ad; apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
  + apply/continuous_subspaceW/cf' => //.
    apply: subset_trans; first exact: itv_closure.
    by apply: subset_itvl; rewrite bnd_simp -lerBrDl safe_dist_itv.
- exact: tad.
Qed.

End solution_locally_unique.

Section loc_lip_uniqueness.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r0 : {posnum R}) (f f' : R -> U).
Hypothesis ab : a < b.
Let B := closed_ball u0 r0%:num.

Hypothesis sol1 : is_sol_cauchy_oo phi a b u0 f.
Hypothesis sol2 : is_sol_cauchy_oo phi a b u0 f'.
Hypothesis sol1B : forall t, a <= t -> t < b -> B (f t).
Hypothesis phi_local_conds : forall t, a <= t -> t < b ->
  exists r k : {posnum R},
    forall t', a <= t' <= b ->
    (k%:num.-lipschitz_(closed_ball (f t) r%:num) (phi t') /\
    forall y, closed_ball (f t) r%:num y ->
       {within `[a, b], continuous phi ^~ y}).

Local Lemma cauchy_lipschitz_unique_right_extension t : a <= t < b ->
  f' t = f t ->
  exists Delta : {posnum R}, {in `[t, t + Delta%:num]%R, f =1 f'}.
Proof.
move=> /andP[ta tb] eq.
have [r [k L]] := phi_local_conds ta tb.
have taab : `[t, b] `<=` `[a, b].
  by move=> ?/=; apply: subset_itvr; rewrite bnd_simp.
have cf0 : {within `[t, b], continuous f}.
  have := sol1.2.2.
  by rewrite closure_itvoo//; exact: continuous_subspaceW.
have cf'0 : {within `[t, b], continuous f'}.
  have := sol2.2.2.
  by rewrite closure_itvoo//; exact: continuous_subspaceW.
have sol10 : is_sol_cauchy_oo phi t b (f t) f.
  split; [by []| split; [| by rewrite closure_itvoo]].
  move=> t0 tab.
  apply sol1.
  by apply: subset_itvr tab; rewrite bnd_simp.
have sol20 : is_sol_cauchy_oo phi t b (f t) f'.
  split; [by []| split; [|by rewrite closure_itvoo]].
  move=> t0 tab.
  apply sol2.
  by apply: subset_itvr tab; rewrite bnd_simp.
have lip20 : {in `[t, b]%R, forall x,
    k%:num.-lipschitz_(closed_ball (f t) r%:num) (phi x)}.
  move=> t0 tab; apply L.
  by rewrite (le_trans ta)/= (itvP tab).
have cont1' : {in closed_ball (f t) r%:num,
  forall y : 'rV_n, {within `[t, b], continuous  phi^~ y}}.
    move => y ytb.
    have : {within `[a,b], continuous phi^~ y}.
      have [| _ +] := L t.
        by rewrite ta ltW.
     apply.
     exact/set_mem.
   exact/continuous_subspaceW/subset_itvr.
have k0 : 0 < k%:num by [].
have [D [P1 P2]] := initial_solution_unique tb k0 cont1' lip20 cf0 sol10 cf'0 sol20.
by exists D.
Qed.

Let in1_eq1 : {in `[a, a]%R, f =1 f'}.
Proof.
move=> t; rewrite in_itv/= -eq_le => /eqP <-.
by rewrite sol1.1 sol2.1.
Qed.

Lemma locally_cauchy_lipschitz_unique : {in `[a, b]%R, f =1 f'}.
Proof.
set E := `[a, b]%classic `&` [set t | {in `[a, t]%R, f =1 f'}].
suff : E b by case.
have Ea : E a by split=> //=; rewrite bound_itvE/= ltW.
have Enonempty : E !=set0 by exists a.
have mon c : E c -> forall d, d \in `[a, c]%R -> E d.
  move=> [/= cab] acff' d dac; split => /=.
    by apply: subset_itvl dac; rewrite bnd_simp (itvP cab).
  move=> t tad; apply: acff'.
  by apply: subset_itvl tad; rewrite bnd_simp (itvP dac).
have monC c d : a <= d -> E c -> ~ E d -> c < d.
  move=> ad Ec nEd.
  rewrite ltNge; apply/negP => cd.
  apply/nEd/(mon c) => //.
  by rewrite in_itv/= ad.
have [hP|/(has_supPn Enonempty)] := lem (has_sup E); last first.
  move=> /(_ b)[x Ex bx].
  by apply/(mon x) => //; rewrite in_itv/= !ltW.
have Eclosed : closed E.
  rewrite closedE/= => p pn.
  suff : forall x, ~ E x -> \forall y \near x, ~ E y.
    by apply: contraPP => Ep /(_ _ Ep).
  move=> x notEx.
  have [xab|xnab] := boolP (x \in `[a, b]%R); last first.
    suff : \forall y \near x, ~ (y \in `[a, b]%R).
      by move=> ?; near do (rewrite not_andP; left).
    move: xnab; rewrite in_itv/= negb_and/= -!ltNge => /orP[xa|xb].
    - near do (apply/negP; rewrite in_itv negb_and/= -!ltNge; apply/orP; left).
      exact: lt_nbhsl.
    - near do (apply/negP; rewrite in_itv negb_and/= -!ltNge; apply/orP; right).
      exact: lt_nbhsr.
  move: notEx; rewrite not_andP => -[//|notEx].
  have [t Et] : exists t, t \in `[a, x]%R /\ f t != f' t.
     rewrite not_existsP => h.
     apply: notEx => t tax.
     have := h t.
     by rewrite not_andP => -[//|/negP/negPn/eqP].
  have [xt|xt]:= eqVneq x t.
    subst t.
    set g := fun x => `|f x - f' x|.
    have contg : {within `[a, b], continuous g}.
      apply/within_continuous_comp_norm/within_continuousB.
      - by have := sol1.2.2; rewrite (closure_itvoo ab).
      - by have := sol2.2.2; rewrite (closure_itvoo ab).
    have g0x : g x > 0 by rewrite normr_gt0 subr_eq0; case: Et.
    have g0 t : t \in `[a, b]%R -> g t > 0 -> ~ {in `[a, t]%R, f =1 f'}.
      move=> tab + atff'.
      suff -> : g t = 0 by rewrite ltxx.
      apply/normr0P; rewrite atff' ?subrr//.
      by move: tab; rewrite !in_itv/= lexx => /andP[->].
    suff hgx: \forall y \near x^'-, 0 < g y.
      near=> y.
      have [yx|xy Ey] := ltP y x; last first.
        have := mon _ Ey x.
        move: xab.
        by rewrite !in_itv/= xy => /andP[-> _] /(_ isT)[].
      apply/not_andP; rewrite -implyE => yab.
      apply: g0 => //.
      by move: yx; near: y.
    apply: (@cvgr_gt _ (x^'-) _ _ g (g x)) => //.
    have xa : a < x.
      rewrite ltNge.
      contra: notEx.
      move: xab; rewrite in_itv/= => /andP[+ _] ax.
      by move/(conj ax) => /andP; rewrite -eq_le => /eqP ->.
    have /(continuous_within_itvP _ ab)[cg _ gbb] := contg.
    move: xab; rewrite in_itv/= => /andP[_].
    rewrite le_eqVlt => /predU1P[-> //|xb].
    apply/cvg_at_left_filter/cg.
    by rewrite in_itv/= xb xa.
  have tx : t < x.
    by case: Et; rewrite in_itv/= lt_neqAle (eq_sym t) xt => /andP[_ ->].
  near=> y.
  move=> Ey.
  have ta : a <= t by case: Et; rewrite in_itv/= => /andP[].
  have /(monC _ _ ta Ey) : ~ E t.
    rewrite not_andP; right => /(_ t).
    by rewrite bound_itvE/= ta => /(_ isT); apply/eqP; case: Et.
  apply/negP; rewrite -leNgt.
  by near: y; exact: lt_le_nbhsr.
have supE : E (sup E).
  by rewrite {1}(closure_id E).1//; apply: closure_sup => //; apply hP.
have sup_itv : a <= sup E by rewrite sup_upper_bound.
have supeq : f' (sup E) = f (sup E).
  apply/esym; apply supE.
  by rewrite  in_itv/= lexx sup_itv.
have [h|h] := leP b (sup E).
  apply: (mon _ supE) => //.
  by rewrite in_itv/= (ltW ab).
have [|Delta Hdelta] := cauchy_lipschitz_unique_right_extension _ supeq.
  exact/andP.
have Delta0 : 0 < Delta%:num by [].
suff : Num.min b (sup E + Delta%:num) <= sup E.
  rewrite ge_min => /orP[/(lt_le_trans h)|].
    by rewrite ltxx.
  by rewrite gerDl leNgt Delta0.
apply: sup_upper_bound => //.
split.
  by rewrite /= in_itv/= le_min (ltW ab)/= ler_wpDr//= ge_min lexx.
move=> t ta.
have [ht|ht] := leP t (sup E).
  by apply supE; rewrite in_itv/= (itvP ta).
apply: Hdelta; rewrite in_itv/= ltW//=.
by move: ta; rewrite in_itv/= le_min => /and3P[_].
Unshelve. all: by end_near. Qed.

End loc_lip_uniqueness.

Section cauchy_lipschitz_uniqueness.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R).
Hypothesis ab : a < b.
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis lip2 : {in `[a, b]%R, forall x : R, k.-lipschitz_B (phi x)}.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.

Let r2 := (r%:num/2)%:pos.
Variable rho : {posnum R}. (* rho < 1 *)
Hypothesis rho1 : (rho%:num < 1).
Local Notation safe_dist := (safe_dist phi a b u0 r2%:num k rho%:num).
Let f := cauchy_lipschitz_f (ltW ab) (ltW k0) lip2 cont1 rho1.

Theorem cauchy_lipschitz_unique f' :
  is_sol_cauchy_oo phi a (a + safe_dist) u0 f' ->
  {in `[a, a + safe_dist]%R, f =1 f'}.
Proof.
move=> sol1.
have cont1' y : B y -> {within `[a, a + safe_dist], continuous phi^~ y}.
  move=> By.
  apply/continuous_subspaceW/cont1.
    apply/subset_itvl.
    by rewrite bnd_simp -lerBrDl; apply safe_dist_itv.
  by apply mem_set.
apply: (locally_cauchy_lipschitz_unique _ _ (u0 := u0) sol1).
- exact: ltDl_safe_dist.
- exact: is_sol_cauchy_lipschitz_f.
move => t tad tbd.
have [r' rp] : exists r' : {posnum R},
    closed_ball (f t) r'%:num `<=` closed_ball u0 r%:num.
  exists r2.
  move => x x0.
  have sb: closed_ball u0 (r%:num / 2) (f t).
    apply solution_stays_in_ball2=> //.
    by rewrite in_itv/= tad//= ltW.
  exact/closed_ball_split/sb.
exists r', (PosNum k0).
move => t' /andP[at' bt'].
split.
  move => /=[x1 x2] [Bx1 Bx2].
  apply: lip2.
    rewrite in_itv/= at' //=.
    by rewrite (le_trans bt')// -lerBrDl safe_dist_itv.
  by split => /=; apply rp.
move => y By.
have h : y \in B by exact/mem_set/rp.
have := cont1 h.
apply/continuous_subspaceW.
apply: subset_itvl.
by rewrite bnd_simp -lerBrDl; apply safe_dist_itv.
Qed.

End cauchy_lipschitz_uniqueness.

(* TODO: move? *)
Lemma patch_in {R X : Type} (f g : R -> X) S x : x \in S -> patch f S g x = g x.
Proof. by move => xs; rewrite /patch xs. Qed.

Section cauchy_lipschitz_symmetric_def.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U).

Definition is_sol_cauchy_sym t0 d u0 (f : R -> U):=
  f t0 = u0 /\ sol_is_deriv phi `]t0 - d, t0 + d[%R f.

End cauchy_lipschitz_symmetric_def.

Section cauchy_lipschitz_symmetric.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b : R)
  (u0 : U) (r : {posnum R}) (k : R).
Hypothesis k0 : 0 < k.
Let B := closed_ball u0 r%:num.
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous phi ^~ y}}.
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (phi x)}.
Definition phi_ (t : R) x := phi x.

Let rho : {posnum R} := 2^-1%:pos.

Let rho1 : rho%:num < 1. Proof. by rewrite /rho/= invf_lt1// ltr1n. Qed.

Let r2 := (r%:num / 2)%:pos.

Let r4 := (r%:num / 4)%:pos.

Let ler4 : r4%:num <= r%:num.
Proof. by rewrite /r4/= ler_pdivrMr // ler_pMr // lerDl. Qed.

Let ler42 : r4%:num <= r2%:num.
Proof.
rewrite /r4/r2/= ler_pdivrMr// -mulrA ler_pMr// ler_pdivlMl// mulr1 lerD//.
by rewrite lerDl.
Qed.

Let B4 := closed_ball u0 r4%:num.

Let phi_lip2 t : t \in `[a, b]%R ->
  {in `[t, b]%R, forall x, k.-lipschitz_B4 (phi x)}.
Proof.
move=> tab x xab /= y By; apply: lip2.
  move: xab; rewrite !inE/=; apply: subset_itvr.
  by rewrite bnd_simp (itvP tab).
by split; [exact/le_closed_ball/By.1|exact/le_closed_ball/By.2].
Qed.

Let phi_cont1 t : t \in `[a, b]%R ->
  {in B4, forall y, {within `[t, b], continuous phi ^~ y}}.
Proof.
move=> /= tab u Bx; apply/continuous_subspaceW/cont1.
  by apply: subset_itvr; rewrite bnd_simp (itvP tab).
apply/mem_set.
by move/set_mem : Bx; exact: le_closed_ball.
Qed.

Let phi_sym x y := - phi (- x) y.

Let phi_sym_lip2 t : t \in `[a, b]%R ->
  {in `[- t, - a]%R, forall t0, k.-lipschitz_B4 (phi_sym t0)}.
Proof.
move => tab /= y yta x Bx.
rewrite /= -normrN opprD !opprK.
have /lip2 : (B `*` B) x.
  by split; [exact/le_closed_ball/Bx.1|exact/le_closed_ball/Bx.2].
apply.
rewrite oppr_itvcc in_itv/= (itvP yta) andbT.
by rewrite (@le_trans _ _ (- t)) ?lerN2 ?(itvP tab)// (itvP yta).
Qed.

Local Lemma phi_sym_cont1 t : t \in `[a,b]%R ->
  {in B4, forall y, {within `[- t, - a], continuous (phi_sym ^~ y)}}.
Proof.
move=> tab /= y By t'; apply: continuousN.
suff : {within `[- (- a), - (- t)], continuous phi^~ y}.
  by move/within_continuous_compN; exact.
rewrite !opprK.
apply/continuous_subspaceW/cont1.
  by apply: subset_itvl; rewrite bnd_simp (itvP tab).
apply/mem_set.
by move/set_mem : By; exact/le_closed_ball.
Qed.

Let dplus t := safe_dist phi t b u0 (r4%:num / 2) k rho%:num.

Let dminus t := safe_dist phi_sym (- t) (- a) u0 (r4%:num / 2) k rho%:num.

Let dboth t := Num.min (b - t) (Num.min (dplus t) (dminus t)).

Section cauchy_lipschitz_sym.
Context (t0 : R).
Hypothesis t0ab : t0 \in `]a, b[%R.

Let amin1 : - t0 < - a. Proof. by rewrite ltrN2 (itvP t0ab). Qed.

Let dminus_gt0 : 0 < dminus t0. Proof. exact: safe_dist_gt0. Qed.

Let t0ab' : t0 \in `[a, b]%R. Proof. exact: subset_itv_oo_cc. Qed.

Let fminus0 := @cauchy_lipschitz_f R n phi_sym (- t0) (- a) u0
  r4 k rho (ltW amin1) (ltW k0) (phi_sym_lip2 t0ab') (phi_sym_cont1 t0ab') rho1.

Let fminus := fminus0 \o -%R.

Let t0b : t0 < b. Proof. by rewrite (itvP t0ab). Qed.

Let dboth_gt0 : 0 < dboth t0.
Proof.
rewrite lt_min subr_gt0 (itvP t0ab)/=.
by rewrite lt_min safe_dist_gt0//= lt_min dminus_gt0.
Qed.

Let fplus := @cauchy_lipschitz_f R n phi t0 b u0
  r4 k rho (ltW t0b) (ltW k0) (phi_lip2 t0ab') (phi_cont1 t0ab') rho1.

Definition safe_dist_sym := dboth t0.

Definition cauchy_lipschitz_f_sym :=
  patch fplus `[t0 - safe_dist_sym, t0] fminus.

Lemma cauchy_lipschitz_f_sym_left t : t \in `[t0 - safe_dist_sym, t0]%R ->
  cauchy_lipschitz_f_sym t = fminus t.
Proof.
move=> ht.
by rewrite /cauchy_lipschitz_f_sym patch_in // inE.
Qed.

Lemma cauchy_lipschitz_sym_oo : is_sol_cauchy_oo phi
  (t0 - safe_dist_sym)
  (t0 + safe_dist_sym)
  (cauchy_lipschitz_f_sym (t0 - safe_dist_sym))
  cauchy_lipschitz_f_sym.
Proof.
have solplus := cauchy_lipschitz_ex (ltW t0b) (ltW k0) (phi_lip2 t0ab')
  (phi_cont1 t0ab') rho1.
have cplus := solution_stays_in_ball.
have solminus := cauchy_lipschitz_ex (ltW amin1) (ltW k0) (phi_sym_lip2 t0ab')
  (phi_sym_cont1 t0ab') rho1.
have cminus := solution_stays_in_ball.
have adplus : t0 < t0 + dplus t0 by rewrite ltrDl safe_dist_gt0.
have cfplus := solplus.2.2.
rewrite closure_itvoo in cfplus; first by rewrite ltrDl safe_dist_gt0.
have amind : -t0 < -t0 + dminus t0 by rewrite ltrDl dminus_gt0.
have cfminus' := solminus.2.2.
rewrite closure_itvoo in cfminus'; first by rewrite ltrDl.
have cfminus : {within `[t0 - dminus t0, t0], continuous fminus}.
  rewrite /fminus.
  apply: within_continuous_compN.
  apply/continuous_subspaceW/cfminus'.
  apply: subset_itvl; rewrite bnd_simp -/dminus.
  by rewrite opprD opprK.
set uneg := cauchy_lipschitz_f_sym (t0 - dboth t0).
have Buneg : closed_ball uneg (r%:num / 2) `<=` closed_ball u0 r%:num.
  rewrite /uneg/cauchy_lipschitz_f_sym patch_in /cauchy_lipschitz_f_sym/=.
    by rewrite inE/=in_itv/= gerBl lexx ltW.
  move=> /= x xb.
  apply: (closed_ball_split _ xb) => //.
  suff : fminus (t0 - dboth t0) \in closed_ball u0 (r%:num/4).
    rewrite !inE.
    apply: le_closed_ball.
    rewrite ler_wpM2l// lef_pV2 ?posrE//.
    by rewrite (natrD _ 2 2) lerDl ler0n.
  apply/mem_set/cminus.
  rewrite in_itv/= opprB lerDr ltW //= addrC lerD//.
  by rewrite /dboth /dplus !ge_min lexx !orbT.
have f01intersect : fminus t0 = fplus t0.
  by rewrite /fminus/= solminus.1 solplus.1.
have fa : cauchy_lipschitz_f_sym t0 = u0.
  rewrite /cauchy_lipschitz_f_sym patch_in /fminus /=.
    by rewrite inE/= in_itv/= lexx gerBl ltW.
  by apply solminus.
set B' := closed_ball uneg r2%:num.
have lip2' : {in `[t0 - dboth t0, t0 + dboth t0]%R, forall x, k.-lipschitz_B' (phi x)}.
  move => /= t tab [x1 x2] [Bx1 Bx2].
  apply: lip2 => //.
    move: tab.
    apply: subset_itv; rewrite bnd_simp.
      rewrite lerBrDl -lerBrDr /dboth /dplus /dminus/= unlock/=.
      by rewrite !ge_min opprK (addrC t0) lexx /= !orbT.
    by rewrite -lerBrDl !ge_min lexx.
  by split; exact: Buneg.
have contf_minus : {within `[t0 - dboth t0, t0], continuous fminus}.
  apply /continuous_subspaceW/cfminus.
  apply: subset_itvr; rewrite bnd_simp.
  by rewrite lerD2l lerN2 /dboth /dminus !ge_min lexx !orbT.
have contf_plus : {within `[t0, t0 + dboth t0], continuous fplus}.
  apply/continuous_subspaceW/cfplus.
  by apply: subset_itvl; rewrite bnd_simp/= lerD2l /dboth 2!ge_min lexx !orbT.
have contf : {within `[t0 - dboth t0, t0 + dboth t0],
    continuous cauchy_lipschitz_f_sym}.
  apply: (within_continuous_patch _ _ contf_minus contf_plus) => //.
  - by rewrite gerBl// ltW.
  - by rewrite lerDl// ltW.
have r42 : r4%:num = r2%:num / 2 by rewrite /r4 /r2/= -mulrA -invfM -natrM.
have fc : {in `[t0-dboth t0, (t0 + dboth t0)], forall t,
    closed_ball (fminus (t0 - dboth t0)) r2%:num (cauchy_lipschitz_f_sym t)}.
  move=> t tad.
  rewrite /cauchy_lipschitz_f_sym/= /patch/=.
   have : (closed_ball (fminus (t0 - dboth t0)) r4%:num) u0.
     suff: (fminus (t0 - dboth t0)) \in closed_ball u0 (r4%:num).
       by rewrite inE/= !closed_ballE/closed_ball_/= // distrC .
     apply/mem_set/cminus.
     rewrite !in_itv/= lerNr lerNl opprD !opprK gerBl ltW//= lerB//.
     by rewrite /dboth !ge_min lexx !orbT.
  rewrite r42 => c1.
  case : ifP => ht.
  - have : fminus t \in closed_ball u0 r4%:num.
      apply/mem_set/cminus.
      move: ht.
      rewrite inE/=!in_itv/= lerNr lerNl opprD !opprK => /andP[h1 ->//=].
      by rewrite (le_trans _ h1)// lerD2l lerN2 /safe_dist_sym !ge_min lexx !orbT.
    by rewrite inE !r42 => /closed_ball_split; exact.
  - have : fplus t \in closed_ball u0 (r2%:num / 2).
      rewrite -r42.
      have ht' : t \in `[t0, t0 + dboth t0].
        have := tad.
        rewrite 2!inE /=!in_itv/= => /andP[h1 ->]; apply /andP; split => //.
        have [hat//| hat] := lerP t0 t.
        rewrite -ht.
        by rewrite inE/=in_itv/= h1//= ltW.
     apply/mem_set/cplus.
     move : ht'; rewrite inE/= !in_itv/= => /andP[-> h1//=].
     apply: (le_trans h1).
     by rewrite lerD// /dboth /dplus 2!ge_min lexx !orbT.
   rewrite inE => c2.
   exact: (closed_ball_split _ c2).
split; first by [].
split; last by rewrite closure_itvoo // /safe_dist_sym // ler_ltD // gtrN.
suff h : is_sol_cauchy_oo phi (t0 - dboth t0) (t0 + dboth t0)
    (cauchy_lipschitz_f_sym (t0 - dboth t0)) cauchy_lipschitz_f_sym.
  by apply h.2.1.
have kn0 : k != 0 by apply lt0r_neq0.
have at0t0 : a <= t0 - dboth t0.
  rewrite lerBrDl -lerBrDr.
  by rewrite /dboth /dminus /dplus !unlock/= !ge_min opprK (addrC t0) lexx /= !orbT.
have t0t0b : t0 + dboth t0 <= b.
  by rewrite -lerBrDl !ge_min lexx.
apply/(@is_sol_integral_cauchy _ _ _ _ _ _ r2) => /=.
- by rewrite lerD// gerN// ltW.
- move=> t tab; apply/continuous_subspaceW/cont1.
    by apply: subset_itv; rewrite bnd_simp.
  exact/mem_set/Buneg/set_mem.
- move=> t tab /= x Bx; apply: lip2.
    by apply: subset_itv tab; rewrite bnd_simp.
  by split; [exact/Buneg/Bx.1|exact/Buneg/Bx.2].
- exact: contf.
- move => _ [t tp] <-.
  rewrite {1}/cauchy_lipschitz_f_sym patch_in.
    by rewrite inE/=in_itv/= lexx //= gerBl ltW.
  by apply fc; rewrite inE.
apply: is_sol_integral_patch.
- by rewrite gtrBl.
- apply: (@within_continuous_lipschitz _ _ _ _ _ u0 r k) => /=; rewrite -/B.
  + move => t tB; apply/continuous_subspaceW/cont1 => //.
    by apply: subset_itv; rewrite bnd_simp// (itvP t0ab).
  + move=> x xt0; apply: lip2.
    by apply: subset_itv xt0; rewrite bnd_simp// (le_trans _ t0t0b)// lerDl ltW.
  + exact: contf_minus.
  + move => _ [/= t' tp] <-.
    apply: (@le_closed_ball _ _ _ r4%:num) => //.
    suff : fminus t' \in closed_ball u0 r4%:num by rewrite inE.
    apply/mem_set/cminus.
    move: tp.
    rewrite !in_itv/=lerNl opprK => /andP[h0 ->//=].
    rewrite lerNl opprD opprK //= (le_trans _ h0)//.
    rewrite lerD2l lerN2 /dboth /dplus /dminus.
    by rewrite !ge_min lexx !orbT.
- apply: (@within_continuous_lipschitz _ _ _ _ _ u0 r k) => /=; rewrite -/B.
  + move=> t tB; apply/continuous_subspaceW/cont1 => //.
    by apply: subset_itv; rewrite bnd_simp// (itvP t0ab).
  + move=> x xt0; apply: lip2.
    by apply: subset_itv xt0; rewrite bnd_simp// (itvP t0ab).
  + exact: contf_plus.
  + move => _ [/= t' tp] <-.
    apply: (@le_closed_ball _ _ _ r4%:num) => //.
    suff : fplus t' \in closed_ball u0 r4%:num by rewrite inE.
    apply/mem_set/cplus.
    apply: subset_itvl tp; rewrite bnd_simp lerD2l.
    by rewrite /dboth /dplus 2!ge_min lexx !orbT.
- by [].
- apply/(@is_sol_cauchy_integral _ _ _ _ _ _ uneg r2).
  + move=> t tab; apply/continuous_subspaceW/cont1.
      by apply: subset_itv; rewrite bnd_simp// (itvP t0ab).
    exact/mem_set/Buneg/set_mem.
  + move => x bx; apply: lip2'.
    by apply: subset_itvl bx; rewrite bnd_simp lerDl ltW.
  + exact: contf_minus.
  + move => _ [t tp] <-.
    rewrite /uneg.
    rewrite {1}/cauchy_lipschitz_f_sym patch_in.
      by rewrite inE/= in_itv/= lexx //= gerBl ltW.
    have /fc : t \in `[t0 - dboth t0, t0 + dboth t0].
      by rewrite inE; apply: subset_itv tp; rewrite bnd_simp// lerDl// ltW.
    rewrite {1}/cauchy_lipschitz_f_sym patch_in; first by rewrite inE.
    exact.
  + split.
    + rewrite /cauchy_lipschitz_f_sym patch_in.
        by rewrite inE/=in_itv/= lexx //= gerBl ltW.
      reflexivity.
    + split; last by rewrite closure_itvoo; first rewrite gtrBl.
      move => t tad.
      case : (solminus.2.1 (- t)).
        move : tad.
        rewrite -/dminus /=!in_itv/= ltrNr ltrNl opprD !opprK => /andP[h1 ->//=].
        by rewrite (le_lt_trans _ h1)// lerD2l lerN2 !ge_min lexx !orbT.
      move=> h1 h2.
      have hd : derivable fminus t 1.
        rewrite /fminus/=.
        apply/derivable1_diffP.
        apply/differentiable_comp => //.
        exact/derivable1_diffP/h1.
      split =>//.
      rewrite /fminus/=.
      apply/rowP => i /=.
      rewrite derive1E/= !derive_mx //= !mxE -derive1E/=.
      have -> : (fun t0 => fminus0 (- t0) 0 i) = ((fun t => fminus0 t 0 i) \o -%R).
        by apply funext.
      rewrite derive1_comp/=.
      - by [].
      - by move /derivable_mxP: h1.
      - rewrite !derive1N//=derive1_id/=.
        move/rowP : h2 => /(_ i).
        rewrite !derive1E /=!derive_mx.
          by apply: h1.
        rewrite /=!mxE => ->.
        by rewrite mulrN1 !opprK.
- apply/(@is_sol_cauchy_integral _ _ _ _ _ _ (fminus t0) r2 k).
  + move=> t tab; apply/continuous_subspaceW/cont1.
    by apply: subset_itv; rewrite bnd_simp//= (itvP t0ab).
  + rewrite /B.
    suff -> : u0 = fminus t0.
      apply mem_set.
      move/set_mem : tab.
      apply: le_closed_ball.
      by rewrite /r2/= ler_piMr// invf_le1 // ler1n.
    rewrite -fa.
    rewrite /cauchy_lipschitz_f_sym.
    rewrite patch_in//.
    rewrite inE/= bound_itvE.
    by rewrite lerBlDl lerDr ltW.
  + move=> x bx.
    rewrite /fminus/=.
    rewrite solminus.1.
    move => [x1 x2] [ Bx1 Bx2].
    apply: lip2.
    * move: bx.
      apply: subset_itv; rewrite bnd_simp.
        by rewrite (itvP t0ab).
      by rewrite -lerBrDl ge_min lexx.
    * split => /=.
        rewrite /B.
        apply: (le_closed_ball _ Bx1).
        by rewrite ler_piMr// invf_le1// ler1n.
      apply: (le_closed_ball _ Bx2).
      by rewrite ler_piMr// invf_le1// ler1n.
  + exact: contf_plus.
  + move=> _ [t tp] <-.
    rewrite /fminus /= solminus.1.
    apply: (le_closed_ball ler42).
    suff : fplus t \in closed_ball u0 r4%:num by rewrite inE.
    apply/mem_set; apply cplus.
    move/mem_set : tp.
    rewrite inE; apply: subset_itvl; rewrite bnd_simp// lerD2l.
    by rewrite /dboth /dplus 2!ge_min lexx !orbT.
  + rewrite /fminus /= solminus.1.
    split; first by apply solplus.
    split.
      move=> t tad; apply solplus.
      apply: subset_itvl tad; rewrite bnd_simp lerD2l.
      by rewrite /dboth /dplus 2!ge_min lexx !orbT.
    apply/continuous_subspaceW/cfplus.
    rewrite closure_itvoo; first by rewrite ltrDl.
    apply: subset_itvl; rewrite bnd_simp lerD2l.
    by rewrite /dboth /dplus 2!ge_min lexx !orbT.
Qed.

Lemma is_sol_cauchy_ooN :
  is_sol_cauchy_oo phi_sym (- t0) (- t0 + dminus t0) u0 fminus0.
Proof. exact: cauchy_lipschitz_ex. Qed.

Lemma cauchy_lipschitz_sym_left t : t \in `[t0 - safe_dist_sym, t0]%R ->
  cauchy_lipschitz_f_sym t = fminus0 (- t).
Proof.
move=> ht.
by rewrite cauchy_lipschitz_f_sym_left.
Qed.

Lemma cauchy_lipschitz_sym :
  is_sol_cauchy_sym phi t0 safe_dist_sym u0 cauchy_lipschitz_f_sym.
Proof.
split; last by apply cauchy_lipschitz_sym_oo.
have solminus := cauchy_lipschitz_ex (ltW amin1) (ltW k0) (phi_sym_lip2 t0ab')
  (phi_sym_cont1 t0ab') rho1.
rewrite /cauchy_lipschitz_f_sym patch_in /fminus /=; last by apply solminus.
by rewrite inE/= in_itv/= lexx gerBl ltW.
Qed.

End cauchy_lipschitz_sym.

End cauchy_lipschitz_symmetric.

Section safe_dist_sym_gt0.
Context {R : realType} {n} (U := 'rV[R]_n) (phi : R -> U -> U) (a b c : R)
  (u0 : U) (r : {posnum R}) (k : R) (sol : R -> U).

Local Notation safe_dist := (@safe_dist_sym R n phi a c u0 r k b).

Hypothesis ab : a < b.
Hypothesis bc : b < c.
Hypothesis k0 : 0 < k.

Lemma safe_dist_sym_gt0 : 0 < safe_dist.
Proof.
by rewrite lt_min subr_gt0 bc /= lt_min !safe_dist_gt0 // ltrNl opprK.
Qed.

End safe_dist_sym_gt0.
