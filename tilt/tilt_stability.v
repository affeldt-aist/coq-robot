From HB Require Import structures.
From mathcomp Require Import boot order algebra ring_tactic.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions filter reals.
From mathcomp Require Import topology prodnormedzmodule normedtype landau.
From mathcomp Require Import sequences derive realfun.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot ode.

(**md**************************************************************************)
(* # Elements of stability theory                                             *)
(*                                                                            *)
(* This file provides elements of stability theory including a proof of       *)
(* Lyapunov's stability theorem.                                              *)
(*                                                                            *)
(* ```                                                                        *)
(*                      posdefmx M == M is definite positive                  *)
(*     is_Lyapunov_candidate V D x := x is in D, V x = 0, and V is positive   *)
(*                                    everywhere in D except at x             *)
(*                        'D~(f) V == derivative of V along the solution f    *)
(* is_equilibrium_point phi Init x := x is in Init and cst x satisfies        *)
(*                                    sol_is_deriv_co phi                     *)
(*            state_space phi Init == the set points attainable by a solution *)
(*                                    of the autonomous ODE phi starting from *)
(*                                    Init                                    *)
(*              is_stable_at f V x == Lyapunov stability                      *)
(*  is_global_time_stable_at f V x == TODO                                    *)
(* ```                                                                        *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - Hassan K. Khalil, Nonlinear systems, 2002                                *)
(******************************************************************************)

Reserved Notation "''D~(' f ) V" (at level 10, f, V at next level,
  format "''D~(' f )  V").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Definition posdefmx {R : realType} m (M : 'M[R]_m) : Prop :=
  M \is sym m R /\ forall a, eigenvalue M a -> a > 0.

Local Open Scope classical_set_scope.

Section locdef.
Context {R : realType} {U : normedModType R}.
Implicit Types V : U -> R.

Definition is_Lyapunov_candidate V (A : set U) (x : U) :=
  [/\ x \in A, V x = 0 & forall z, z \in A -> z != x -> V z > 0].

Definition locnegdef V (x : U) := V x = 0 /\ \forall z \near x^', V z < 0.

(* locally negative semidefinite *)
Definition locnegsemidef V (x : U) := V x = 0 /\ \forall z \near x^', V z <= 0.

End locdef.

(* derivation along the solution f, see Khalil p.114 *)
(* NB: we are not representing the initial state at t = 0 of the solution f *)
Definition derive_along {R : numFieldType} {n} (U := 'rV[R]_n) (V : U -> R)
    (f : R -> U) t :=
  (jacobian1 V (f t))^T *d 'D_1 f t.

Notation "''D~(' f ) V" := (derive_along V f).

Section derive_along.
Context {R : realType} {n : nat}.
Variable f : R -> 'rV[R]_n.

Lemma derive_along_derive (U := 'rV[R]_n) (V : U -> R) (t : R) :
  differentiable V (f t) -> differentiable f t ->
  'D~(f) V t = 'D_1 (V \o f) t.
Proof.
move=> difV difsol.
rewrite /derive_along/=.
rewrite /jacobian1.
rewrite /jacobian.
rewrite /dotmul.
rewrite -trmx_mul.
rewrite mul_rV_lin1.
rewrite mxE.
rewrite -deriveE=> /=.
  apply: differentiable_comp => //.
  exact/differentiable_scalar_mx.
rewrite derive_mx /=.
  apply: derivable_scalar_mx => //.
  exact: diff_derivable.
rewrite mxE.
rewrite [in RHS]deriveE/=.
  exact: differentiable_comp.
rewrite [in RHS]diff_comp//=.
do 2 (rewrite -[in RHS]deriveE; first by []).
by under eq_fun do rewrite mxE /= mulr1n /=.
Qed.

Lemma derive_alongMl (V : 'rV_n -> R) (k : R) t :
  differentiable V (f t) -> differentiable f t ->
  'D~(f) (k *: V) t = k *: 'D~(f) V t.
Proof.
move=> dfx dpx.
rewrite derive_along_derive.
  exact: differentiable_comp.
  by [].
rewrite deriveZ/=.
  apply: diff_derivable => /=.
  rewrite -fctE.
  exact: differentiable_comp.
congr (_ *: _).
by rewrite derive_along_derive.
Qed.

Lemma derive_alongD (V1 V2 : 'rV_n -> R) t :
  differentiable V1 (f t) -> differentiable V2 (f t) ->
  differentiable f t ->
  'D~(f) (V1 + V2) t  = 'D~(f) V1 t + 'D~(f) V2 t.
Proof.
move=> dfV1 dfV2 dfsol.
rewrite derive_along_derive.
  exact: differentiableD.
  by [].
rewrite deriveD/=.
  apply: diff_derivable => //.
  rewrite -fctE.
  exact: differentiable_comp.
  apply: diff_derivable => //.
  rewrite -fctE.
  exact: differentiable_comp.
rewrite derive_along_derive; [by []..|].
by rewrite derive_along_derive.
Qed.

Lemma derivative_derive_along_eq0 (V : 'rV_n -> R) (t : R) :
  differentiable V (f t) ->
  'D_1 f t = 0 -> 'D~(f) V t = 0.
Proof.
move=> df dsol0.
rewrite /derive_along /jacobian1 /dotmul dotmulP /dotmul -trmx_mul.
by rewrite dsol0 mul0mx !mxE.
Qed.

Lemma derive_along_enorm_squared m (V : 'rV[R]_n -> 'rV[R]_m) (t : R) :
  differentiable V (f t) ->
  differentiable f t ->
  'D~(f) (fun y => `|V y|_e ^+ 2) t =
  (2 *: 'D_1 (V \o f) t *m (V (f t))^T) 0 0.
Proof.
move=> difff diffphi.
rewrite derive_along_derive//; first exact: differentiable_enorm_squared.
rewrite fctE derive_enorm_squared /=.
  by apply: diff_derivable=> //=; exact: differentiable_comp.
by rewrite mulrDl mul1r scalerDl scale1r mulmxDl [in RHS]mxE.
Qed.

End derive_along.

(* NB: not used, can be shown to be equivalent to derive_along *)
Definition derive_along_partial {R : realType} n (V : 'rV[R]_n -> R)
    (a : R -> 'rV[R]_n) (t : R) : R :=
  \sum_(i < n) (partial V (a t) i * ('D_1 a t) ``_ i).

Section ode.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variable phi : U -> U.

Lemma sol_is_deriv_c0oP (D : R) (f : R -> U) (e : {posnum R}) :
  is_sol_cauchy_oo (fun=> phi) (f (- e%:num)) (- e%:num) D f ->
  sol_is_deriv_co (fun=> phi) 0 D f.
Proof.
move=> [_ [H cf]] t t0D; apply H; rewrite inE/=; apply: subset_itv t0D => //.
by rewrite bnd_simp.
Qed.

(* "global" solution *)
Definition sol_is_deriv_c0y (f : R -> U) :=
  sol_is_deriv_cbnd (fun=> phi) 0 (BInfty R false) f.

(* TODO: generalize this lemma *)
Lemma sol_is_deriv_c0yP (f : R -> U) : sol_is_deriv_c0y f <->
  forall t, t >= 0 -> derivable f t 1 /\ f^`() t = phi (f t).
Proof.
split=> H t t0oo; apply: H.
  by rewrite in_itv/= andbT.
by move: t0oo; rewrite in_itv/= andbT.
Qed.

Lemma sol_is_deriv_c0yco f : sol_is_deriv_c0y f ->
  forall D, sol_is_deriv_co (fun=> phi) 0 D f.
Proof.
move=> + D t t0D.
apply.
by move: t0D; rewrite !in_itv/= => /andP[->].
Qed.

End ode.

Section state_space.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variable phi : U -> U.

Definition state_space (Init : set U) : set U :=
  [set x | exists f D, [/\ f 0 \in Init, is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f &
    exists2 t, t \in `[0, D[%R & x = f t]].

End state_space.

Section equilibrium_point.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variable phi : U -> U.

Definition is_equilibrium_point (x : U) :=
   sol_is_deriv (fun=> phi) `[0, +oo[%R (cst x).

(* Lemma equilibrium_point_in_state_space (Init : set U) : *)
(*   is_equilibrium_point Init `<=` state_space phi Init. *)
(* Proof. *)
(* move=> x solf; exists (cst x), 1; split => //=. *)
(*   apply: sol_is_deriv_cy_co. *)
(* by exists 0 => //; rewrite bound_itvE. *)
(* Qed. *)

Definition equilibrium_points Init := [set p | Init p /\ is_equilibrium_point p].

Lemma equilibrium_points_subset (A B : set U) : A `<=` B ->
  equilibrium_points A `<=` equilibrium_points B.
Proof.
move=> AB x.
rewrite /equilibrium_points/= /is_equilibrium_point.
move => [Ax H].
split => //.
by apply AB.
Qed.

End equilibrium_point.

Section stability.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.
Variable phi : U -> U.
Variable Init : set U.

Definition is_stable_at (x : U) :=
  forall eps, eps > 0 -> exists2 d, d > 0 &
  forall f D, f 0 \in Init -> is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
    `| f 0 - x | < d -> forall t, t \in `[0, D[%R -> `| f t - x | < eps.

(* assuming solution exists for all time *)
(* Definition is_global_time_stable_at (x : U) := *)
(*   forall eps, eps > 0 -> exists2 d, d > 0 & *)
(*   forall f, f 0 \in Init -> sol_is_deriv_c0y phi f -> *)
(*     `| f 0 - x | < d -> forall t, 0 <= t -> `| f t - x | < eps. *)

(* Lemma stable_global_time : is_stable_at `<=` is_global_time_stable_at. *)
(* Proof. *)
(* move=> x H e /H [d d0 stable]. *)
(* exists d => // z0 z0Init zglob zd /= t t0. *)
(* apply: (stable _ (t + 1)) => //. *)
(*   exact: sol_is_deriv_c0yco. *)
(* by rewrite in_itv/= t0/= ltrDl. *)
(* Qed. *)

Definition is_asymptotically_stable_at (x : U) (f : R -> U) : Prop :=
  exists2 d, d > 0 & `| f 0 - x | < d -> f t @[t --> +oo] --> x.

End stability.

Section about_Lyapunov_function.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.+1.
Variable phi : U -> U.
Variable D : R.
Variable f : R -> U.
Hypothesis derivable_f : {in `]0, D[%R, forall t, derivable f t 1}.
Hypothesis within_cont_f : {within `[0, D[, continuous f}.

Variable V : U -> R.
Hypothesis Vdiff : forall t : U, differentiable V t.
Hypothesis DV_le0 : forall t, t \in `]0, D[%R -> 'D~(f) V t <= 0.

Lemma V_nincr a b : b < D -> 0 <= a <= b -> V (f b) <= V (f a).
Proof.
move=> bD /andP[a_ge0 ab].
apply: (@ler0_derive1_le_cc _ (V \o f) 0 b) => //=.
- move=> y yb.
  apply/diff_derivable/differentiable_comp; last exact: differentiable_comp.
  rewrite -derivable1_diffP; apply: derivable_f.
  by apply: subset_itv yb; rewrite bnd_simp// ltW.
- move=> y yb.
  rewrite derive1E -derive_along_derive//.
  + rewrite -derivable1_diffP; apply: derivable_f.
    by apply: subset_itv yb; rewrite bnd_simp// ltW.
  + apply: DV_le0.
    by apply: subset_itvl yb; rewrite bnd_simp ltW.
- (* `[0, b] *)
  have [b0|] := ltP 0 b; last first.
    move=> b0.
    have -> : b = 0 by apply/eqP; rewrite eq_le b0 (le_trans a_ge0).
    rewrite set_itv1.
    exact: continuous_subspace1.
  apply: within_continuous_comp => //.
  (* apply/continuous_within_itvP => //; split. *)
  + move=> z z0b.
    apply: continuous_comp; last exact: differentiable_continuous.
    apply: differentiable_continuous => //.
  + apply/continuous_subspaceW/within_cont_f.
    apply: subset_itvl.
    by rewrite bnd_simp.
- by rewrite bound_itvE (le_trans a_ge0).
- by rewrite in_itv/= ab andbT.
Qed.

End about_Lyapunov_function.

(* TODO: move *)
Section sphere.
Context {R : realType} {n : nat}.
Local Open Scope classical_set_scope.

Definition sphere r := [set x : 'rV[R]_n | `|x| = r].

Lemma sphere_nonempty r : n != 0 -> 0 < r -> sphere r !=set0.
Proof.
move=> n0 r_gt0.
rewrite /sphere.
exists (const_mx r).
rewrite /sphere /= /normr/=.
(* TODO: need lemma? *)
rewrite mx_normrE/=.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: bigmax_le.
    exact: ltW.
  by move=> i _; rewrite mxE gtr0_norm.
under eq_bigr do rewrite mxE gtr0_norm//.
apply/le_bigmax => /=.
destruct n as [|n'] => //.
exact: (ord0, ord0).
Qed.

Lemma compact_sphere r : compact (sphere r).
Proof.
apply: bounded_closed_compact.
  suff : \forall M \near +oo, forall p, sphere r p ->
      forall i, `|p ord0 i| < M.
    rewrite /bounded_set.
    apply: filter_app; near=> M0.
    move=> Kbnd /= p /Kbnd ltpM0.
    rewrite /normr/= mx_normrE.
    apply/bigmax_leP; split => //= i _.
    by rewrite ord1; exact/ltW/ltpM0.
  near=> M => v.
  rewrite /sphere /= => vr i.
  rewrite (@le_lt_trans _ _ r)//.
    rewrite -vr [leRHS]/normr/= mx_normE.
    under eq_bigr do rewrite ord1.
    rewrite -(pair_big xpredT xpredT (fun _ j => `|v ord0 j|%:nng))//=.
    rewrite big_ord_recr/= big_ord0.
    rewrite max_r; first exact/bigmax_ge_id.
    rewrite (bigD1 i)//= -maxE le_max.
    by apply/orP; left.
  clear v vr i.
  by near: M; apply: nbhs_pinfty_gt; rewrite num_real.
pose d := fun x : 'rV[R]_n  => `|x| : R.
have contd : continuous d by move=> /= z; exact: norm_continuous.
rewrite [X in closed X](_ : _ = d @^-1` [set r]).
  by apply/seteqP; split.
by apply continuous_closedP.
Unshelve. all: by end_near. Qed.

End sphere.

Section Lyapunov_stability.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.+1.
Variable phi : U -> U.
Variable A : set U.
Hypothesis openA : open A.
Variable Init : set U.

Let B r := closed_ball_ (fun x => `|x|) (0 : 'rV[R]_n.+1) r.

Let BE s : 0 < s -> B s = closed_ball 0 s.
Proof. by move=> r0; rewrite /B -closed_ballE. Qed.

Variable V : U -> R.
Hypothesis Vdiff : forall t : U, differentiable V t.
Hypothesis DV_le0 : forall D f, f 0 \in Init ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  forall t, t \in `]0, D[%R -> 'D~(f) V t <= 0.

(* khalil theorem 4.1 *)
Theorem Lyapunov_stability0 :
  is_Lyapunov_candidate V A 0 -> is_stable_at phi Init 0.
Proof.
move=> VInitx /= eps eps0/=.
move: VInitx => [/= xInit Vx0 InitxV].
have [r [r_gt0 r_eps BrD]] : exists r : R, [/\ 0 < r, r <= eps & B r `<=` A].
  move: xInit; rewrite inE => /(open_subball openA)[r0/= r0_gt0] q.
  pose r := Num.min (r0 / 2) eps.
  have r_gt0 : 0 < r by rewrite /r lt_min eps0 divr_gt0.
  exists (r / 2); split.
  - by rewrite divr_gt0.
  - by rewrite /r ler_pdivrMr// ge_min ler_pMr// ler1n orbT.
  - move=> v Brv; apply: (q r) => //.
    rewrite /ball/= sub0r normrN gtr0_norm// gt_min.
    by rewrite gtr_pMr ?invf_lt1 ?ltr1n.
  move: Brv; rewrite BE ?divr_gt0//.
  exact: subset_closure_half(*TODO: naming seems off, report*).
rewrite {xInit}.
have alpha_min : {x : 'rV[R]_n.+1 | x \in sphere r /\
    forall y, y \in sphere r -> V x <= V y}.
  have : {within sphere r, continuous V}.
    apply: continuous_subspaceT => /= v.
    by apply/differentiable_continuous; exact/Vdiff.
  move/(EVT_min_rV (sphere_nonempty _ r_gt0) (@compact_sphere _ _ r)).
  by move=> /(_ isT)/cid2[c sphere_r_c sphere_r_V]; exists c.
pose alpha := V (sval alpha_min).
have alpha_gt0 : 0 < alpha.
  have sphere_pos y : y \in sphere r -> 0 < V y.
    move=> yr; apply: InitxV; last first.
       rewrite gtr0_norm_neq0//.
       by move: yr; rewrite inE /sphere/= => ->.
    apply/mem_set/BrD.
    move: yr; rewrite inE /sphere/= => <-.
    by rewrite /B /closed_ball_/= sub0r normrN.
  rewrite /alpha sphere_pos// /sphere inE/=.
  by have [+ _] := svalP alpha_min; rewrite inE.
rewrite {InitxV}.
have [beta /andP[beta_gt0 beta_alpha]] : exists beta, 0 < beta < alpha.
  by exists (alpha / 2); rewrite divr_gt0//= ltr_pdivrMr//= ltr_pMr// ltr1n.
set Omega_beta := [set x : 'rV[R]_n.+1 | B r x /\ V x <= beta].
have Omega_beta_Br : Omega_beta `<=` (B r)°.
  move=> y [Bry Vybeta].
  rewrite BE// interior_closed_ballE => //=.
  have yr : `|y| <= r by move: Bry; rewrite /B /closed_ball_/= sub0r normrN.
  have [{}yr|ry|{}yr] := ltgtP `|y| r.
  - by rewrite mx_norm_ball /ball_/= sub0r normrN.
  - by have := le_lt_trans yr ry; rewrite ltxx.
  - have alphaVy : alpha <= V y.
      by rewrite /alpha; case: (svalP alpha_min) => [_]; apply; rewrite inE.
    by have := lt_le_trans beta_alpha (le_trans alphaVy Vybeta); rewrite ltxx.
(* any trajectory starting in Omega_beta at t = 0
   stays in Omega_beta for all t >= 0 *)
have Df_Omega_beta D f : f 0 \in Init -> is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
   f 0 \in Omega_beta -> forall t, t \in `[0, D[%R -> f t \in Omega_beta.
  move=> f0 solf f0_Omega.
  have /= V_nincr_consequence t : t \in `]0, D[%R -> forall u, 0 <= u <= t ->
      'D~(f) V u <= 0 -> V (f t) <= V (f 0) <= beta.
    move=> /= t0D u ut Vle0l; apply/andP; split.
    - move: f0_Omega; rewrite inE /Omega_beta/= => -[Brphi0 Vphi0beta].
      apply: (@V_nincr _ _ D f).
      + by move=> t' t'0D; have [_ [d _]] := solf; apply d.
      + have [_ [_ solc]] := solf.
        apply /continuous_subspaceW/solc; rewrite closure_itvoo.
          by rewrite (itvP t0D).
        by apply: subset_itvl; rewrite bnd_simp.
      + by move=> t'; exact: Vdiff.
      + exact: DV_le0.
      + by rewrite (itvP t0D).
      + by rewrite lexx/= (itvP t0D).
    - by move: f0_Omega; rewrite inE => -[].
  move=> t t0D.
  have [->//|t0] := eqVneq t 0.
  have {t0}t0D : t \in `]0, D[%R.
    by rewrite in_itv/= lt_neqAle eq_sym t0/= 2!(itvP t0D).
  rewrite inE; split; last first.
    have : 'D~(f) V t <= 0 by exact: (DV_le0 _ solf).
    have := @V_nincr_consequence t t0D t.
    rewrite lexx (itvP t0D)/= => /(_ isT) => /[apply].
    by move=> /andP[/le_trans] => /[apply].
  move: f0_Omega; rewrite inE /Omega_beta/= /B /closed_ball_/=.
  rewrite !sub0r !normrN => -[f0r Vf0beta].
  rewrite leNgt; apply/negP => rft.
  have [t1 /andP[t1_ge0 t1t] phit1r] : exists2 t0, 0 <= t0 <= t & `|f t0| = r.
    have t0 : 0 <= t by rewrite (itvP t0D).
    have norm_phi_cont : {within `[0, t]%classic, continuous (normr \o f)}.
      apply/(@within_continuous_comp _ _ _ `[0, t] f (@normr _ _)) => //.
        by move=> z _; exact: norm_continuous.
      have [_ [_ cont]] := solf.
      apply/continuous_subspaceW/cont.
      rewrite closure_itvoo.
        by rewrite (itvP t0D).
      by apply: subset_itvl; rewrite bnd_simp (itvP t0D).
    have : Num.min `|f 0| `|f t| <= r <= Num.max `|f 0| `|f t|.
      by rewrite ge_min f0r/= le_max (ltW rft) orbT.
    move=> /(IVT t0 norm_phi_cont)[c cI norm_phi_c].
    by exists c => //; move/itvP: cI => ->.
  have alphaVphit1 : alpha <= V (f t1).
    rewrite {alpha_gt0 beta_alpha} /alpha; case: alpha_min => /=.
    by move=> y [_ +]; apply; rewrite inE.
  have : beta < V (f t1).
    by rewrite (lt_le_trans _ alphaVphit1)//; case/andP: beta_alpha.
  apply/negP; rewrite -leNgt.
  move: t1_ge0; rewrite le_eqVlt => /predU1P[<-//|t10].
  have := @V_nincr_consequence t1.
  have tD : t < D by rewrite (itvP t0D).
  rewrite in_itv/= t10/= (le_lt_trans t1t tD) => /(_ isT).
  move=> /(_ t1); rewrite (ltW t10) lexx => /(_ isT).
  have : 'D~(f) V t1 <= 0.
    apply: (@DV_le0 _ _ _ solf) => //.
    by rewrite in_itv/= t10/= (le_lt_trans _ tD).
  move=> /[swap] /[apply].
  by move=> /andP[/le_trans] => /[apply].
have _ : compact Omega_beta.
  apply: bounded_closed_compact; rewrite /Omega_beta.
  - rewrite /bounded_set /= /globally.
    exists r; split => //= t rt v.
    rewrite /B /closed_ball_/= sub0r normrN.
    by move=> [/le_trans vr _]; rewrite vr// ltW.
  - apply: closedI => /=.
      by rewrite BE//; exact: closed_ball_closed.
    rewrite [X in closed X](_ : _ = V @^-1` [set x | x <= beta]).
      by apply/seteqP; split.
    apply: preimage_closed => //= v _.
    apply: continuous_comp; first by [].
    exact: differentiable_continuous.
have [d0 d0_gt0 Vbeta] : exists2 d, d > 0 & forall x, `|x| <= d -> V x < beta.
  have [d d_gt0 xdV] : exists2 d, 0 < d &
      forall y, `|y - 0| < d -> `|V y - V 0| < beta.
    have /cvgrPdist_lt /(_ _ beta_gt0) :
        V x @[x --> nbhs (0 : 'rV_n.+1) ] --> V 0.
      exact/differentiable_continuous/Vdiff.
    rewrite nearE /= => /nbhs_ballP[d /= d_pos xdV].
    exists d => // y.
    move: xdV; rewrite mx_norm_ball /ball_ /= distrC => /[apply].
    by rewrite distrC.
  exists (d / 2); first exact: divr_gt0.
  move=> v vd;  have /(xdV v) : `|v - 0| < d.
    by rewrite subr0 (le_lt_trans vd)// ltr_pdivrMr // ltr_pMr // ltr1n.
  by rewrite Vx0 subr0; apply: le_lt_trans; rewrite ler_normlW.
pose delta := Num.min d0 r.
have delta_gt0 : 0 < delta by rewrite /delta lt_min d0_gt0 r_gt0.
have deltaV y : `|y| <= delta -> V y < beta.
  move=> /= ydelta.
  have : `|y| <= d0 by rewrite (le_trans ydelta)// /delta ge_min lexx.
  exact: Vbeta.
have B_delta_Omega_beta : B delta `<=` Omega_beta.
  rewrite /Omega_beta => /= v.
  rewrite /B /closed_ball_/= sub0r normrN => vdelta.
  split; last exact/ltW/deltaV.
  by rewrite (le_trans vdelta)// /delta ge_min lexx orbT.
exists delta => //.
move=> f D' f0 solf f0xD t0 t0_ge0.
rewrite subr0.
have : f 0 \in Omega_beta.
  rewrite inE; apply: B_delta_Omega_beta.
  rewrite /B /closed_ball_/= sub0r normrN; apply/ltW.
  by rewrite subr0 in f0xD.
rewrite inE => -[+ Vf0beta].
rewrite /B /closed_ball_/= sub0r normrN => f0r.
have : (B r)° (f t0).
  apply: Omega_beta_Br; apply/set_mem.
  apply: (Df_Omega_beta D') => //.
  rewrite inE; split; first by rewrite /B /closed_ball_/= sub0r normrN.
  have : B delta (f 0).
    rewrite /closed_ball_; apply: ltW; rewrite sub0r normrN.
    by rewrite subr0 in f0xD.
  by move/B_delta_Omega_beta => [].
rewrite BE//= interior_closed_ballE//=.
by rewrite mx_norm_ball /ball_/= sub0r normrN => /lt_le_trans; exact.
Unshelve. all: by end_near. Qed.

End Lyapunov_stability.

Section is_equilibrium_point_change_of_variables.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.+1.
Variable phi : U -> U.
Variable Init : set U.

Lemma sol_is_deriv_co_substitution D f x :
 sol_is_deriv_co (fun=> phi) 0 D f ->
 sol_is_deriv_co (fun _ y => phi (y + x)) 0 D (f \- cst x).
Proof.
rewrite /sol_is_deriv_co => /= H t t0D; split.
  apply: derivableB => /=.
  by apply H.
  by [].
rewrite subrK derive1E deriveB/=.
  by apply H.
  by [].
by rewrite derive_cst subr0 -derive1E; apply H.
Qed.

Lemma is_sol_cauchy_oo_substitution D f x :
 is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
 is_sol_cauchy_oo (fun _ y => phi (y + x)) (f 0 - x) 0 D (f \- cst x).
Proof.
move=> /= [init [sol cont]]; split.
- by [].
- split.
  split.
  + apply: derivableB.
      by apply sol.
    by [].
  + rewrite subrK derive1E deriveB/=; first by apply sol.
    by [].
    by rewrite derive_cst subr0 -derive1E; apply sol.
  + apply : within_continuousB => //.
    apply: continuous_subspaceT.
    exact: cst_continuous.
Qed.

Lemma is_stable_at_substitution x :
  is_stable_at (fun y => phi (y + x)) [set y - x | y in Init] 0 ->
  is_stable_at phi Init x.
Proof.
move=> H.
rewrite /is_stable_at => /= e e0.
have [/= d d0 {}H] := H _ e0.
exists d => // f D f0Init solf f0xd t t0.
rewrite -[_ - _]subr0.
rewrite -[f t - x]/((f \- cst x) t).
apply: (H _ D) => /=.
- exact/image_f.
- exact: is_sol_cauchy_oo_substitution.
- by rewrite /= subr0.
- assumption.
Qed.

Lemma is_equilibrium_point_substitutionP x :
  is_equilibrium_point (fun y => phi (y + x)) 0 <->
  is_equilibrium_point phi x.
Proof.
split.
- move=> issol t t0; split.
  exact: derivable_cst.
  have := issol 0.
  rewrite in_itv/= lexx => /(_ isT)[_].
  rewrite add0r => <-.
  by rewrite !derive1_cst.
- move=> issol t t0; split.
  exact: derivable_cst.
  have [] := issol _ t0.
  rewrite !derive1_cst //=.
  by rewrite add0r => _ ->.
Qed.

Lemma is_Lyapunov_candidate_substitution V x :
  is_Lyapunov_candidate V Init x ->
  is_Lyapunov_candidate (fun y => V (y + x)) [set y - x | y in Init] 0.
Proof.
move=> [xInit Vx0/= InitV].
split.
- rewrite inE/=.
  exists x; rewrite ?subrr//.
  by rewrite inE in xInit.
- by rewrite add0r.
- move=> /= z.
  rewrite inE/= => -[x0 x0Init <-{z}].
  rewrite subr_eq0 => x0x.
  apply: InitV => //.
    by rewrite subrK inE.
  by rewrite subrK.
Qed.

End is_equilibrium_point_change_of_variables.

Section Lyapunov_stability.
Context {R : realType} {n : nat}.
Let U := 'rV[R]_n.+1.
Variable phi : U -> U.
Variable A : set U.
Hypothesis openA : open A.
Variable Init : set U.

Variable V : U -> R.
Hypothesis Vdiff : forall t : U, differentiable V t.
Hypothesis V'_le0 : forall D (f : R -> U),
  f 0 \in Init ->
  is_sol_cauchy_oo (fun=> phi) (f 0) 0 D f ->
  forall t, t \in `]0, D[%R -> 'D~(f) V t <= 0.

Theorem Lyapunov_stability :
  is_Lyapunov_candidate V A `<=` is_stable_at phi Init.
Proof.
move=> x VInitx.
(* TODO: renaming Init <-> A*)
apply: is_stable_at_substitution.
pose A' := [set y - x | y in A].
have openA' : open A'.
  rewrite /A'.
  rewrite [X in open X](_ : _ = (fun y => y + x) @^-1` A).
    apply/seteqP; split.
      by move=> /= z [v vInit <-]; rewrite subrK.
    by move=> /= z zxInit; exists (z + x) => //; rewrite addrK.
  apply: open_comp => // z _.
  rewrite /continuous_at.
  apply: (@cvgD _ 'rV_n.+1) => //=.
    by apply: filter_filter; exact: mx_nbhs_filter. (* TODO: should be automatic! *)
  by apply: cvg_cst; apply: filter_filter; exact: mx_nbhs_filter.
apply: (@Lyapunov_stability0 _ _ _ _ openA' _ (fun y => V (y + x))) => //.
- by move=> t; exact: differentiable_comp.
- move=> /= D sol sol0Init solp /= t t0D.
  rewrite [leLHS](_ : _ =  ('D~((fun y => y + x) \o sol) V) t).
    rewrite derive_along_derive.
      exact: differentiable_comp.
      apply/derivable1_diffP.
      have [_ [d _]] := solp.
      apply d.
      by apply: subset_itvr t0D; rewrite bnd_simp.
    have -> : (fun y => V (y + x)) \o sol = V \o (+%R^~ x \o sol).
      exact/funext.
    rewrite derive_along_derive.
      exact: differentiable_comp.
      apply: differentiable_comp => //.
      apply/derivable1_diffP.
      have [_ [d _]] := solp.
      apply d.
      by apply: subset_itvr t0D; rewrite bnd_simp.
    by [].
  apply: (@V'_le0 D); last by assumption.
  - rewrite inE/=.
    move: sol0Init; rewrite inE/= => -[x0 x0Init <-].
    by rewrite subrK.
  - split => /=.
    by [].
    have [_ [d _]] := solp.
    split.
    move=> /= z z0D; split.
      apply/derivable1_diffP/differentiable_comp => //.
      apply/derivable1_diffP.
      by apply d.
    rewrite derive1E deriveD/=; first by apply d.
    by [].
    rewrite derive_cst addr0 -derive1E.
    by apply d.
    apply: within_continuous_comp.
    move => x0 x0p.
    apply: continuousD => //.
    apply: cst_continuous.
    by have [_ [_ +]] := solp.
by have /= := @is_Lyapunov_candidate_substitution R n A V _ VInitx.
Qed.

End Lyapunov_stability.
