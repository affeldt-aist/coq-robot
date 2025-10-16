From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals order.
From mathcomp Require Import topology normedtype landau derive realfun.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.
(*Require Import lasalle pendulum.*)

(**md**************************************************************************)
(* # tentative formalization of [1]                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*                posdefmx M == M is definite positive                        *)
(*             locposdef V x == V is locally positive definite at x           *)
(*   is_Lyapunov_candidate V := locposdef V                                   *)
(*         locnegsemidef V x == V is locally negative semidefinite            *)
(*         LieDerivative V x == Lie derivative                                *)
(*       solves_equation f y == the function y satisfies y' = f y             *)
(*  is_equilibrium_point f p := solves_equation f (cst p)                     *)
(*             state_space f == the set points attainable by a solution       *)
(*                              (in the sense of `solves_equation`)           *)
(*  is_Lyapunov_stable_at f V x == Lyapunov stability                         *)
(* ```                                                                        *)
(*                                                                            *)
(* References:                                                                *)
(* - [1]                                                                      *)
(* https://hal.science/hal-04271257v1/file/benallegue2019tac_October_2022.pdf *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

Local Open Scope classical_set_scope.
(* NB: we are just mimicking the proofs for the real line already available in derive.v *)
Lemma EVT_max_rV (R : realType) n (f : 'rV[R]_n.+1 -> R) (A : set 'rV[R]_n.+1) :
  A !=set0 ->
  compact A ->
  {within A, continuous f} -> exists2 c, c \in A &
  forall t, t \in A -> f t <= f c.
Proof.
move=> A0 compactA fcont; set imf := f @` A.
have imf_sup : has_sup imf.
  split.
    case: A0 => a Aa.
    by exists (f a); apply/imageP.
  have [M [Mreal imfltM]] : bounded_set (f @` A).
    exact/compact_bounded/continuous_compact.
  exists (M + 1) => y /imfltM yleM.
  by rewrite (le_trans _ (yleM _ _)) ?ler_norm ?ltrDl.
have [|imf_ltsup] := pselect (exists2 c, c \in A & f c = sup imf).
  move=> [c cab fceqsup]; exists c => // t tab; rewrite fceqsup.
  apply/sup_upper_bound => //.
  exact/imageP/set_mem.
have {}imf_ltsup t : t \in A -> f t < sup imf.
  move=> tab; case: (ltrP (f t) (sup imf)) => // supleft.
  rewrite falseE; apply: imf_ltsup; exists t => //; apply/eqP.
  rewrite eq_le supleft andbT sup_upper_bound//.
  exact/imageP/set_mem.
pose g t : R := (sup imf - f t)^-1.
have invf_continuous : {within A, continuous g}.
  rewrite continuous_subspace_in => t tab; apply: cvgV => //=.
    by rewrite subr_eq0 gt_eqF // imf_ltsup //; rewrite inE in tab.
  by apply: cvgD; [exact: cst_continuous | apply: cvgN; exact: (fcont t)].
have /ex_strict_bound_gt0 [k k_gt0 /= imVfltk] : bounded_set (g @` A).
  by apply/compact_bounded/continuous_compact.
have [_ [t tab <-]] : exists2 y, imf y & sup imf - k^-1 < y.
  by apply: sup_adherent => //; rewrite invr_gt0.
rewrite ltrBlDr -ltrBlDl.
suff : sup imf - f t > k^-1 by move=> /ltW; rewrite leNgt => /negbTE ->.
rewrite -[ltRHS]invrK ltf_pV2// ?qualifE/= ?invr_gt0 ?subr_gt0 ?imf_ltsup//; last first.
  exact/mem_set.
by rewrite (le_lt_trans (ler_norm _) _) ?imVfltk//; exact: imageP.
Qed.

Lemma EVT_min_rV (R : realType) n (f : 'rV[R]_n.+1 -> R) (A : set 'rV[R]_n.+1) :
  A !=set0 ->
  compact A ->
  {within A, continuous f} -> exists2 c, c \in A &
  forall t, t \in A -> f c <= f t.
Proof.
move=> A0 cA fcont.
have /(EVT_max_rV A0 cA) [c clr fcmax] : {within A, continuous (- f)}.
  by move=> ?; apply: continuousN => ?; exact: fcont.
by exists c => // ? /fcmax; rewrite lerN2.
Qed.
Local Close Scope classical_set_scope.

(* spin and matrix/norm properties*)

Lemma norm_spin {R : rcfType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
  (u *m \S(v - u) ^+ 2 *m (u)^T) 0 0 = - norm (u *m \S(v)) ^+ 2.
Proof.
rewrite spinD spinN -tr_spin mulmxA !mulmxDr mulmxDl !mul_tr_spin !addr0.
rewrite -dotmulvv /dotmul trmx_mul.
rewrite mxE [X in _ + X = _](_ : _ = 0) ?addr0; last first.
  by rewrite tr_spin -mulmxA mulNmx spin_mul_tr mulmxN mulmx0 oppr0 mxE.
by rewrite tr_spin mulNmx mulmxN [in RHS]mxE opprK mulmxA.
Qed.

Lemma sqr_spin {R : realType} (u : 'rV[R]_3) (norm_u1 : norm u = 1) :
  \S(u) *m \S(u) = u^T *m u - 1%:M.
Proof.
have sqrspin : \S(u) ^+ 2 = u^T *m u - (norm u ^+ 2)%:A by rewrite sqr_spin.
rewrite expr2 norm_u1 expr2 mulr1 in sqrspin.
rewrite mulmxE sqrspin.
  apply/matrixP => i j ; rewrite mxE /= [in RHS]mxE /=.
  congr (_+_); rewrite mxE mxE /= mul1r.
  by rewrite [in RHS]mxE [in RHS]mxE /= -mulNrn mxE -mulNrn.
Qed.

Definition posdefmx {R : realType} m (M : 'M[R]_m) : Prop :=
  M \is sym m R /\ forall a, eigenvalue M a -> a > 0.

From mathcomp Require Import spectral.
From mathcomp Require Import complex.

Lemma posdefmxP {R : realType} m (M : 'M[R]_m) :
  posdefmx M <-> (forall v : 'rV[R]_m, v != 0 -> (v *m M *m v^T) 0 0 > 0).
Proof.
split.
(*  rewrite /posdefmx => -[symM eigen_gt0] v v0.
Local Open Scope complex_scope.
  pose M' := map_mx (fun r => r%:C) M.
  have : M' \is normalmx.
    apply: symmetric_normalmx.*)
  move => [Msym eigenM] x x_neq0.
  apply/eigenM/eigenvalueP.
  exists x => //=.
  (* spectral theorem? *)
Admitted.

Local Open Scope classical_set_scope.

Definition locposdef {R : realType} (T : normedModType R) (V : T -> R)
    (D : set T) (x : T) : Prop :=
  x \in D /\ V x = 0 /\ forall z, z \in D -> z != x -> V z > 0.

Notation is_Lyapunov_candidate := locposdef.

(* locally positive semi definite (NB* not used yet) *)
Definition lpsd {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near x^', V z >= 0.

(* locally negative semidefinite *)
Definition locnegsemidef {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near x^', V z <= 0.

(* locally negative definite (NB: not used yet) *)
Definition lnd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near x^', V z < 0.

Section derive_help.
Local Open Scope classical_set_scope.
End derive_help.

Section gradient.

Definition jacobian1 {R : numFieldType} n (f : 'rV[R]_n.+1 -> R)
    : 'rV_n.+1 -> 'cV_n.+1 :=
  jacobian (scalar_mx \o f).
(* not used*)
Definition partial {R : realType} {n : nat} (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) i :=
  lim (h^-1 * (f (a + h *: 'e_i) - f a) @[h --> 0^'])%classic.

Lemma partial_diff {R : realType} n (f : 'rV[R]_n.+1 -> R)  (a : 'rV[R]_n.+1)
    (i : 'I_n.+1) :
  derivable f a 'e_i ->
  partial f a i = ('D_'e_i (@scalar_mx _ 1 \o f) a) 0 0.
Proof.
move=> fa1.
rewrite derive_mx ?mxE//=; last first.
  exact: derivable_scalar_mx.
rewrite /partial.
under eq_fun do rewrite (addrC a).
by under [in RHS]eq_fun do rewrite !mxE/= !mulr1n.
Qed.

(* NB: not used *)
Definition err_vec {R : ringType} n (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Lemma err_vecE {R : ringType} n (i : 'I_n.+1) :
  err_vec i = 'e_i :> 'rV[R]_n.+1.
Proof.
apply/rowP => j.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Definition gradient_partial {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :=
  \row_(i < n.+1) partial f a i.

Lemma gradient_partial_sum {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :
  gradient_partial f a = \sum_(i < n.+1) partial f a i *: 'e_i.
Proof.
rewrite /gradient_partial [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

Lemma gradient_partial_jacobian1 {R : realType} n (f : 'rV[R]_n.+1 -> R)
    (v : 'rV[R]_n.+1) : differentiable f v ->
  gradient_partial f v = (jacobian1 f v)^T.
Proof.
move=> fa; apply/rowP => i.
rewrite /gradient_partial mxE mxE /jacobian mxE -deriveE; last first.
  apply: differentiable_comp => //.
  exact: differentiable_scalar_mx.
rewrite partial_diff//.
exact/diff_derivable.
Qed.

End gradient.

Reserved Notation "''D~(' sol , x ) f" (at level 10, sol, x, f at next level,
  format "''D~(' sol ,  x )  f").

(* derivation along the trajectory h *)
Definition derive_along {R : realType} {n : nat}
    (V : 'rV[R]_n.+1 -> R) (h : R -> 'rV[R]_n.+1) (x : 'rV[R]_n.+1)
    (t : R) : R :=
  (jacobian1 V (h t))^T *d 'D_1 h t.

Notation "''D~(' sol , x ) f" := (derive_along f (sol x) x).

Section derive_along.
Context {R : realType} {n : nat}.
Variable sol : 'rV[R]_n.+1 -> R -> 'rV[R]_n.+1.
(* sol represents the solutions of a differential equation *)

Lemma derive_along_derive (V : 'rV[R]_n.+1 -> R) (x : 'rV[R]_n.+1) (t : R) :
  differentiable V (sol x t) -> differentiable (sol x) t ->
  'D~(sol, x) V t = 'D_1 (V \o sol x) t.
(* Warning: we are not representing the initial state at t = 0 of the trajectory x
   see Khalil p.114 *)
Proof.
move => dif1 dif2.
rewrite /derive_along /=.
rewrite /jacobian1.
rewrite /jacobian.
rewrite /dotmul.
rewrite -trmx_mul.
rewrite mul_rV_lin1.
rewrite mxE.
rewrite -deriveE => //=; last first.
  apply: differentiable_comp => //=.
  exact/differentiable_scalar_mx.
rewrite derive_mx /=; last first.
  apply: derivable_scalar_mx => //=.
  exact: diff_derivable.
rewrite mxE.
rewrite [in RHS]deriveE => //=.
rewrite [in RHS]diff_comp => //=.
rewrite -![in RHS]deriveE => //=.
under eq_fun do rewrite mxE /= mulr1n /=.
  by [].
exact: differentiable_comp.
Qed.

Lemma derive_alongMl (f : 'rV_n.+1 -> R) (k : R) (x : 'rV[R]_n.+1) t :
  differentiable f (sol x t) -> differentiable (sol x) t ->
  'D~(sol, x) (k *: f) t = k *: 'D~(sol, x) f t.
Proof.
move=> dfx dpx.
rewrite derive_along_derive; last 2 first.
  exact: differentiable_comp.
  by [].
rewrite deriveZ/=; last first => //=.
  apply: diff_derivable => //=.
  rewrite -fctE.
  exact: differentiable_comp.
congr (_ *: _).
by rewrite derive_along_derive.
Qed.

Lemma derive_alongD (f g : 'rV_n.+1 -> R) (x : 'rV_n.+1) t :
  differentiable f (sol x t) -> differentiable g (sol x t) ->
  differentiable (sol x) t ->
  'D~(sol, x) (f + g) t  = 'D~(sol, x) f t + 'D~(sol, x) g t.
Proof.
move=> dfx dgx difp.
rewrite derive_along_derive; last 2 first.
  exact: differentiableD.
  by [].
rewrite deriveD/=; last 2 first.
  apply: diff_derivable => //.
  rewrite -fctE .
  exact: differentiable_comp.
  apply: diff_derivable => //.
  rewrite -fctE .
  exact: differentiable_comp.
rewrite derive_along_derive; [|by []..].
by rewrite derive_along_derive.
Qed.

Lemma derivative_derive_along_eq0
  (f : 'rV_n.+1 -> R) (x : 'rV[R]_n.+1) (t : R) :
  differentiable f (sol x t) ->
  'D_1 (sol x) t = 0 -> 'D~(sol, x) f t = 0.
Proof.
move=> xt1 dtraj.
rewrite /derive_along /jacobian1 /dotmul dotmulP /dotmul -trmx_mul.
by rewrite dtraj mul0mx !mxE.
Qed.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

Lemma derive_along_norm_squared m (f : 'rV[R]_n.+1 -> 'rV_m.+1)
  (x : 'rV[R]_n.+1) (t : R) :
  differentiable f (sol x t) ->
  differentiable (sol x) t ->
  'D~(sol, x) (fun y => norm (f y) ^+ 2) t =
  (2 *: 'D_1 (f \o sol x) t *m (f (sol x t))^T) 0 0.
Proof.
move=> difff diffphi.
rewrite derive_along_derive => //=; last exact: differentiable_norm_squared.
rewrite -derive1E /= fctE derive_norm_squared //=; last first.
  by apply: diff_derivable=> //=; exact: differentiable_comp.
by rewrite mulrDl mul1r scalerDl scale1r mulmxDl [in RHS]mxE.
Qed.

End derive_along.

(* not used, can be shown to be equivalent to derive_along *)
Definition derive_along_partial {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (a : R -> 'rV[R]_n.+1) (t : R) : R :=
  \sum_(i < n.+1) (partial V (a t) i * ('D_1 a t) ``_ i).

Section ode_equation.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.+1.

Variable phi : (K -> T) -> K -> T.

Definition is_sol (x : K -> T) (A : set T) :=
   [/\ x 0 \in A, (forall t, derivable x t 1)
                  & forall t, 'D_1 x t = phi x t].

Lemma is_sol_subset y0 (A B : set T) (AB : A `<=` B) :
  is_sol y0 A -> is_sol y0 B.
Proof.
rewrite /is_sol inE => -[inD0 deriv tilt].
rewrite inE.
split.
- exact: AB.
- exact: deriv.
- exact: tilt.
Qed.

Definition is_equilibrium_point x := is_sol (cst x).

Lemma is_equilibrium_point_subset x (A B : set T) (AB : A `<=` B) :
  is_equilibrium_point x A -> is_equilibrium_point x B.
Proof.
rewrite /is_equilibrium_point /is_sol inE => -[inD0 deriv tilt].
rewrite inE.
split.
- exact: AB.
- exact: deriv.
- exact: tilt.
Qed.

Definition equilibrium_points A := [set p : T | is_equilibrium_point p A ].

Definition state_space A :=
  [set p : T | exists y, is_sol y A /\ exists t, p = y t ].

Definition equilibrium_is_stable_at
  (A : set T) (x : T) (z : K -> 'rV[K]_n.+1) :=
  forall eps, eps > 0 ->
  exists2 d, d > 0 &
  (`| z 0 - x | < d -> forall t, t >= 0 -> `| z t - x | < eps).

Definition equilibrium_is_asymptotically_stable_at
  (A : set T) (x : T) (z : K -> 'rV[K]_n.+1) : Prop :=
    exists2 d, d > 0 &
      (`| z 0 - x | < d -> z t @[t --> +oo] --> x).

End ode_equation.
 (* axiom cauchy thm 3.3 *)

(* we introduce a definition of uniqueness of solutions of a
differential equation that we will assume when necessary for
lack of a formalization of Cauchy-Lipschitz/Picard-Lindelof theorem. *)
Section solutions_unique.
Context {K : realType} {n : nat}.
Variable D : set 'rV[K]_n.+1.
Variable f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1.

Definition solutions_unique := forall (a b : K -> 'rV_n.+1) (x0 : 'rV_n.+1),
  is_sol f a D ->
  is_sol f b D ->
  a 0 = x0 -> b 0 = x0 ->
  a = b.

End solutions_unique.

Definition existence_uniqueness {K : realType} {n} (D : set 'rV[K]_n.+1)
    (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
    (sol : 'rV[K]_n.+1 -> K -> 'rV[K]_n.+1) :=
  forall y, y 0 \in D -> is_sol f y D <-> sol (y 0) = y.

Definition initial_condition {K : realType} {n}
    (sol : 'rV[K]_n.+1 -> K -> 'rV[K]_n.+1) :=
  forall p, sol p 0 = p.

Lemma existence_uniqueness_unique {K : realType} {n} (D : set 'rV[K]_n.+1)
    (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
    (sol : 'rV[K]_n.+1 -> K -> 'rV[K]_n.+1) :
  existence_uniqueness D f sol -> solutions_unique D f.
Proof.
move=> solP.
move => a b x0.
move => fad fbd a0 b0.
apply/funext => x.
case : (fad) => //=.
move => a0D Da fa.
have := solP _ a0D.
case.
move => /(_ fad).
move => a0a _.
case : (fbd) => //=.
move => b0D Db fb.
have := solP _ b0D.
case.
move => /(_ fbd).
move => b0b _.
rewrite -b0b -a0a.
by rewrite a0 b0.
Qed.

Lemma existence_uniqueness_exists {K : realType} {n} (D : set 'rV[K]_n.+1)
    (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
    (sol : 'rV[K]_n.+1 -> K -> 'rV[K]_n.+1) :
  existence_uniqueness D f sol -> initial_condition sol ->
  forall p, p \in D -> is_sol f (sol p) D.
Proof.
move=> solP sol0 p pD.
have H := solP (sol p).
apply H.
  by rewrite sol0.
by rewrite sol0.
Qed.

(* preuve qui repose sur la continuite et la monotonie via locpos
 continument differentiable V*)

From mathcomp Require Import normedtype.
From mathcomp Require Import matrix_normedtype.

Lemma ball0_le0 (R : realDomainType) (V : pseudoMetricNormedZmodType R) (a : V) (r : R) :
  ball a r = set0 -> r <= 0.
Proof.
rewrite -subset0 => ar0; rewrite leNgt; apply/negP => r0.
by have /(_ (ballxx _ r0)) := ar0 a.
Qed.

Lemma le0_ball0 (R : realDomainType) (V : pseudoMetricNormedZmodType R) (a : V) (r : R) :
  r <= 0 -> ball a r = set0.
Proof.
move=> r0; rewrite -subset0 => y.
rewrite -ball_normE /ball_/= ltNge => /negP; apply.
by rewrite (le_trans r0).
Qed.

Lemma closed_ball0 (R : realDomainType) (V : pseudoMetricNormedZmodType R) (a : V) (r : R) :
  r <= 0 -> closed_ball a r = set0.
Proof.
move=> r0; rewrite -subset0 => v.
by rewrite /closed_ball le0_ball0// closure0.
Qed.

Lemma closed_ballAE {K : realType} n (e : K) (x : 'rV[K]_n.+1) :
  0 < e -> closed_ball x e = closed_ball_ (@mx_norm _ _ _) x e.
Proof.
by move=> e0; rewrite closed_ballE.
Qed.

Import Order.Def.

(* NB: added to be able to produce the following instance to be able to use bigop lemmas *)
Lemma nng_max0r {K : realType} : left_id ((0:K)%:nng) (@maxr {nonneg K}).
Proof.
move=> x.
rewrite /max; case: ifPn => //.
rewrite -leNgt => x0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact: x0.
by have : 0 <= x%:nngnum by []. (* NB: this should be automatic *)
Qed.

HB.instance Definition _ {K : realType} :=
  Monoid.isComLaw.Build {nonneg K} 0%:nng max maxA maxC nng_max0r.

Lemma maxE {K : realType} (x y : {nonneg K}) :
  (max x%:num y%:num) = (max x y)%:num.
Proof.
rewrite /max; apply/esym.
case: ifPn => // xy.
  case: ifPn => //.
  rewrite -leNgt => yx.
  by apply/eqP; rewrite eq_le yx/= ltW.
case: ifPn => // yx.
apply/eqP; rewrite eq_le (ltW yx)/=.
by rewrite -leNgt in xy.
Qed.

Section sphere.
Context {K : realType} {n : nat}.

Definition sphere r := [set x : 'rV[K]_n.+1 | `|x| = r].

Lemma sphere_nonempty r : 0 < r -> sphere r !=set0.
Proof.
move=> r_gt0; exists (const_mx r).
rewrite /sphere /= /normr/=.
(* TODO: need lemma? *)
rewrite mx_normrE/=.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: bigmax_le.
    exact: ltW.
  by move=> i _; rewrite mxE gtr0_norm.
under eq_bigr do rewrite mxE gtr0_norm//.
apply/le_bigmax => /=.
exact: (ord0, ord0).
Qed.

Lemma compact_sphere r : compact (sphere r).
Proof.
apply: bounded_closed_compact.
  suff : \forall M \near +oo, forall p, sphere r p -> forall i, `|p ord0 i| < M.
    rewrite /bounded_set; apply: filter_app; near=> M0.
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
    rewrite max_r; last exact/bigmax_ge_id.
    rewrite (bigD1 i)//= -maxE le_max.
    by apply/orP; left.
  clear v vr i.
  by near: M; apply: nbhs_pinfty_gt; rewrite num_real.
pose d := fun x : 'rV[K]_n.+1  => `|x| : K.
have contd : continuous d by move=> /= z; exact: norm_continuous.
rewrite [X in closed X](_ : _ = d @^-1` [set r]); last first.
  by apply/seteqP; split.
by apply continuous_closedP.
Unshelve. all: by end_near. Qed.

End sphere.

Section Lyapunov_stability.
Context {K : realType} {n : nat}.
Variable D : set 'rV[K]_n.+1.
Variable f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1.
Variable sol : 'rV[K]_n.+1 -> K -> 'rV[K]_n.+1.
Hypothesis openD : open D. (* D est forcement un ouvert *)
(* see Cohen Rouhling ITP 2017 Sect 3.2 *)
Hypothesis solP : existence_uniqueness D f sol.
Hypothesis sol0 : initial_condition sol.

Let B r := closed_ball_ (fun x => `|x|) (0 : 'rV[K]_n.+1) r.

Let BE r : 0 < r -> B r = closed_ball 0 r.
Proof. by move=> r0; rewrite /B -closed_ballE. Qed.

Variable V : 'rV[K]_n.+1 -> K.
Hypothesis V'le_0 : forall x, x \in D ->
  forall t, t >= 0 -> 'D~(sol, x) V t <= 0.
Hypothesis Vderiv : forall t : 'rV[K]__, differentiable V t.

Let V_nincr a b : 0 <= a <= b ->
  forall x, x \in D -> V (sol x b) <= V (sol x a).
Proof.
move=> /andP[a_ge0 ab] x xD.
apply: (@ler0_derive1_le_cc _ (V \o sol x) 0 b) => //=.
- move=> y yb.
  apply/diff_derivable/differentiable_comp; last exact: differentiable_comp.
  rewrite -derivable1_diffP.
  by have [] : is_sol f (sol x) D by apply solP; rewrite sol0.
- move=> y yb.
  rewrite derive1E -derive_along_derive//.
  + apply: V'le_0 => //.
    by move : yb; rewrite in_itv/= => /andP[/ltW].
  + rewrite -derivable1_diffP.
    by have [] : is_sol f (sol x) D by apply solP; rewrite sol0.
- apply: continuous_subspaceT => z.
  apply: continuous_comp; last exact: differentiable_continuous.
  apply: differentiable_continuous => //.
  rewrite -derivable1_diffP.
  by have [] : is_sol f (sol x) D by apply solP; rewrite sol0.
- by rewrite !in_itv/= lexx (le_trans a_ge0).
- by rewrite in_itv/= ab andbT.
Qed.

(* khalil theorem 4.1 *)
Theorem Lyapunov_stability (x : 'rV[K]_n.+1 := 0)
  (VDx : is_Lyapunov_candidate V D x) :
  is_equilibrium_point f x D ->
  equilibrium_is_stable_at D x (sol x).
Proof.
move=> eq /= eps eps0.
move: VDx => [/= xD [Vx0 DxV]].
have [r [r_gt0 [r_eps BrD]]] : exists2 r : K, 0 < r & r <= eps /\ B r `<=` D.
  move: xD; rewrite inE => /(open_subball openD)[r0/= r0_gt0] q.
  pose r := Num.min (r0 / 2) eps.
  have r_gt0 : 0 < r by rewrite /r lt_min eps0 divr_gt0.
  exists (r / 2); first by rewrite divr_gt0.
  split; first by rewrite /r ler_pdivrMr// ge_min ler_pMr// ler1n orbT.
  move=> v Brv; apply (q r) => //.
    rewrite /ball/= sub0r normrN gtr0_norm//.
    by rewrite /r gt_min ltr_pdivrMr// ltr_pMr// ltr1n.
  by move: Brv; rewrite BE ?divr_gt0//; exact: subset_closure_half.
have alpha_min : {x : 'rV[K]_n.+1 | x \in sphere r /\
    forall y, y \in sphere r -> V x <= V y}.
  have : {within sphere r, continuous V}.
    apply: continuous_subspaceT => /= v.
    by apply/differentiable_continuous; exact/Vderiv.
  move/(EVT_min_rV (sphere_nonempty r_gt0) (@compact_sphere _ _ r)).
  by move=> /cid2[c sphere_r_c sphere_r_V]; exists c.
pose alpha := V (sval alpha_min).
have alpha_gt0 : 0 < alpha.
  have sphere_pos y : y \in sphere r -> 0 < V y.
    move=> yr; apply: DxV; last first.
      rewrite gtr0_norm_neq0//.
      by move: yr; rewrite inE /sphere/= => ->.
    apply/mem_set/BrD.
    move : yr; rewrite inE /sphere/= => <-.
    by rewrite /B /closed_ball_/= sub0r normrN.
  rewrite /alpha sphere_pos// /sphere inE/=.
  by have [+ _] := svalP alpha_min; rewrite inE.
have [beta /andP[beta_gt0 beta_alpha]] : exists beta, 0 < beta < alpha.
  by exists (alpha / 2); rewrite divr_gt0//= ltr_pdivrMr//= ltr_pMr// ltr1n.
set Omega_beta := [set x : 'rV[K]_n.+1 | B r x /\ V x <= beta].
have Omega_beta_Br : Omega_beta `<=` (B r)°.
  move=> y [Bry Vybeta].
  rewrite BE// interior_closed_ballE => //=.
  have yr : `|y| <= r by move: Bry; rewrite /B /closed_ball_/= sub0r normrN.
  have [{}yr | ry | {}yr] := ltgtP (`|y|) r.
  - by rewrite mx_norm_ball /ball_/= sub0r normrN.
  - by have := le_lt_trans yr ry; rewrite ltxx.
  - have alphaVy : alpha <= V y.
      by rewrite /alpha; case: (svalP alpha_min) => [_]; apply; rewrite inE.
    by have := lt_le_trans beta_alpha (le_trans alphaVy Vybeta); rewrite ltxx.
(* any trajectory starting in Omega_beta at t = 0
   stays in Omega_beta for all t >= 0 *)
have Df_Omega_beta phi : is_sol f phi D ->
    phi 0 \in Omega_beta -> forall t, 0 <= t -> phi t \in Omega_beta.
  move=> sol_phi phi_Omega.
  have /= V_nincr_consequence : forall t, 0 <= t -> forall u, 0 <= u <= t ->
      'D~(sol, phi 0) V u <= 0 ->
      V (sol (phi 0) t) <= V (sol (phi 0) 0) <= beta.
    move=> /= t1 t10 u ut1 Vle0.
    apply/andP; split.
      move : phi_Omega; rewrite inE /Omega_beta/= => -[Brphi0 Vphi0beta].
      by apply: V_nincr; [rewrite lexx t10|rewrite inE; exact: BrD].
    by rewrite sol0; move: phi_Omega; rewrite inE => -[].
  move=> t t0.
  rewrite inE; split; last first.
    have : 'D~(sol, phi 0) V t <= 0.
      by apply: V'le_0 => //; case: sol_phi.
    move/V_nincr_consequence => /(_ t).
    rewrite lexx t0/= => /(_ isT isT).
    have -> : sol (phi 0) = phi by apply solP => //; case: sol_phi.
    by case/andP; exact: le_trans.
  move: phi_Omega; rewrite inE /Omega_beta/= /B /closed_ball_/=.
  rewrite !sub0r !normrN => -[phi0r Vphi0beta].
  rewrite leNgt; apply/negP => phi_t_r.
  have [t1 [t1_ge0 phit1r]] : exists t0, t0 >= 0 /\ `|phi t0| = r.
    have norm_phi_cont : {within `[0, t]%classic, continuous (normr \o phi)}.
      apply: continuous_subspaceT => /= y.
      apply: continuous_comp; last exact: norm_continuous.
      apply: differentiable_continuous => //.
      case : (sol_phi) => _ + _ => /(_ y).
      by rewrite derivable1_diffP.
    have : min `|phi 0| `|phi t| <= r <= max `|phi 0| `|phi t|.
      by rewrite ge_min phi0r/= le_max (ltW phi_t_r) orbT.
    move=> /(IVT t0 norm_phi_cont)[c cI norm_phi_c].
    by exists c; split => //; move/itvP: cI => ->.
  have alphaVphit1 : alpha <= V (phi t1).
    rewrite {alpha_gt0 beta_alpha} /alpha; case: alpha_min => /=.
    by move=> y [_ +]; apply; rewrite inE.
  have : beta < V (phi t1).
    by rewrite (lt_le_trans _ alphaVphit1)//; case/andP : beta_alpha.
  apply/negP; rewrite -leNgt.
  have := V_nincr_consequence t1 t1_ge0 t1.
  rewrite lexx t1_ge0 => /(_ isT).
  have : 'D~(sol, phi 0) V t1 <= 0 by apply: V'le_0 => //; case: sol_phi.
  move=> /[swap] /[apply].
  have -> : sol (phi 0) = phi.
    apply solP => //;rewrite inE; apply: BrD => //.
    by rewrite /B /closed_ball_/= sub0r normrN.
  by move=> /andP[]; exact: le_trans.
have _ : compact Omega_beta.
  apply: bounded_closed_compact; rewrite /Omega_beta.
  - rewrite /bounded_set /= /globally.
    exists r; split => //= t rt v.
    rewrite /B /closed_ball_/= sub0r normrN.
    by move=> [/le_trans vr _]; rewrite vr// ltW.
  - apply: closedI => /=.
      by rewrite BE//; exact: closed_ball_closed.
    rewrite [X in closed X](_ : _ = V @^-1` [set x | x <= beta]); last first.
      by apply/seteqP; split.
    apply: closed_comp => //= v _.
    apply: continuous_comp; first by [].
    exact: differentiable_continuous.
have [d0 d0_gt0 Vbeta] : exists2 d, d > 0 & forall x, `|x| <= d -> V x < beta.
  have [d d_gt0 xdV] : exists2 d : K, 0 < d &
      forall y, `|y - x| < d -> `|V y - V x| < beta.
    have /cvgrPdist_lt /(_ _ beta_gt0) : V x @[x --> nbhs x] --> V x.
      exact/differentiable_continuous/Vderiv.
    rewrite nearE /= => /nbhs_ballP[d /= d_pos xdV].
    exists d => // y.
    move: xdV; rewrite mx_norm_ball /ball_ /= distrC => /[apply].
    by rewrite distrC.
  exists (d / 2); first exact: divr_gt0.
  move=> v vd;  have /(xdV v) : `|v - x| < d.
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
have _ : (B delta) (sol x 0) ->
    forall t, t >= 0 -> sol x t \in Omega_beta -> (B r) (sol x t).
  by move => ball0 t1 t1_ge0; rewrite /Omega_beta inE => -[].
rewrite /x !subr0.
exists delta => // sol0_delta t0 t0_ge0.
rewrite subr0.
have : sol x 0 \in Omega_beta.
  rewrite inE; apply: B_delta_Omega_beta.
  by rewrite /B /closed_ball_/= sub0r normrN; apply/ltW; exact: sol0_delta.
rewrite inE => -[+ _].
rewrite /B /closed_ball_/= sub0r normrN => solx0r.
have : (B r)° (sol x t0).
  apply: Omega_beta_Br; apply/set_mem.
  apply: Df_Omega_beta => //.
    by have [] : is_sol f (sol x) D by apply solP; rewrite sol0.
  rewrite inE; split; first by rewrite /B /closed_ball_/= sub0r normrN.
  have : B delta (sol x 0).
    by rewrite /closed_ball_; apply: ltW; rewrite sub0r normrN.
  by move/B_delta_Omega_beta => [].
rewrite BE//= interior_closed_ballE//=.
rewrite mx_norm_ball /ball_/= sub0r normrN => /lt_le_trans; exact.
Unshelve. all: by end_near. Qed.

End Lyapunov_stability.

(* see Appendix VII.A of
   https://hal.science/hal-04271257v1/file/benallegue2019tac_October_2022.pdf *)
Section basic_facts.
Variable K : realType.

Lemma fact212 (v w : 'rV[K]_3) : \S(v) * \S(w) = w^T *m v - (v *m w^T)``_0 *: 1.
Proof.
apply/matrix3P/and9P; split; apply/eqP;  rewrite !(mxE,sum3E,spinij,sum1E); Simp.r.
  ring.
by rewrite mulrC.
by rewrite mulrC.
by rewrite mulrC.
by rewrite !opprD; ring.
by rewrite mulrC.
by rewrite mulrC.
by rewrite mulrC.
by rewrite !opprD; ring.
Qed.

Lemma fact213 (v w : 'rV[K]_3) : \S(v) * \S(w) * \S(v) = - (v *m w^T) ``_0 *: \S(v).
Proof.
rewrite fact212 mulrBl -mulmxE -mulmxA; have: v *m \S(v) = 0.
  apply: trmx_inj.
  by rewrite trmx_mul tr_spin mulNmx spin_mul_tr trmx0 oppr0.
move => ->.
by rewrite mulmx0 sub0r -mul_scalar_mx -mulNmx; congr (_ *m _); rewrite scalemx1 rmorphN.
Qed.

Lemma fact215 ( v w : 'rV[K]_3) : \S(w *m \S(v)) = \S(w) * \S(v) - \S(v) * \S(w).
Proof.
by rewrite spinE spin_crossmul.
Qed.

Lemma fact216 (v w : 'rV[K]_3): \S(w *m \S(v)) = v^T *m w - w^T *m v.
Proof.
by rewrite fact215 !fact212 -!/(_ *d _) dotmulC opprB addrA subrK.
Qed.
Lemma fact217 (v : 'rV[K]_3): \S(v) ^+ 3 = - (norm v ^+2) *: \S(v).
  exact: spin3.
Qed.

Lemma fact214 (R : 'M[K]_3) (v_ : seq 'rV[K]_3) : R \is 'SO[K]_3 ->
  R^T * (\prod_(i <- v_) \S( i )) * R =  (\prod_(i <- v_) \S( i *m R)).
Proof.
move => RSO.
elim/big_ind2 : _ => //.
  by rewrite -!mulmxE mulmx1 rotation_tr_mul.
- move => a b c d H1 H2.
  rewrite -H1 // -H2 // -!mulmxE -!rotation_inv // !mulmxA -[R^-1 *m b *m R *m R^-1]mulmxA.
  rewrite mulmxV; last first.
    rewrite unitmxE.
    apply: orthogonal_unit.
    exact: rotation_sub.
  by rewrite -[R^-1 *m b *m 1%:M *m d]mulmxA mul1mx.
- move => i true.
  exact: spin_similarity.
Qed.

End basic_facts.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

(* definition du probleme *)
Record equa_diff (K : realType) := {
  equa_f : 'rV[K]_6 -> 'rV[K]_6 ; (* autonomous *)
  equa_S0 : set 'rV[K]_6 ; (* intended to be invariant *)
  equa_fk : exists k, k.-lipschitz_equa_S0 equa_f ;
    (* hypothesis for existence and uniqueness of a solution (NB: not really used yet) *)
  equa_t0 : K ; (* initial time *)
}.

Definition is_invariant_solution_equa_diff {K : realType}
    (e : equa_diff K) (y1 : K -> 'rV[K]_6) A :=
  is_sol (fun y t => equa_f e (y t)) y1 A /\
  (y1 (equa_t0 e) \in equa_S0 e ->
    (forall t, t > 0 -> y1  (equa_t0 e + t) \in equa_S0 e)). (*TODO*)

Section ya.
(* mesure de l'accelerometre *)
Variable K : realType.
Variable v : K -> 'rV[K]_3. (* local frame of the sensor *)
Variable R : K -> 'M[K]_3. (*L -> W*)
Variable g0 : K. (*standard gravity constant*)
Let w t := ang_vel R t. (* local frame of the sensor (gyroscope) *)
Let x1 t :=  v t. (* local frame *)
Definition x2 t : 'rV_3 := 'e_2 *m R t.
Definition y_a t := - x1 t *m \S( w t) + 'D_1 x1 t + g0 *: x2 t. (* world frame *)
Variable p : K -> 'rV[K]_3.
Let v1 := fun t : K => 'D_1 p t *m R t.
Definition y_a1 t := - v1 t *m \S(w t) + 'D_1 v1 t + g0 *: x2 t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.

Lemma y_aE t (derivableR : forall t, derivable R t 1)
    (derivablep : forall t, derivable p t 1)
    (derivableDp : forall t, derivable ('D_1 p) t 1) :
  ('D_1 ('D_1 p) t + g0 *: 'e_2) *m R t= y_a1 t .
Proof.
rewrite mulmxDl.
rewrite /y_a1/= /v1 /= /x2.
congr +%R; last by rewrite scalemxAl.
rewrite -ang_vel_mxE/=; last 2 first.
 move=> t0.
 by rewrite rotation_sub.
 exact : derivableR.
rewrite [in RHS]derive_mulmx => //.
rewrite derive1mx_ang_vel => //; last first.
  by move=> t0; rewrite rotation_sub.
rewrite ang_vel_mxE// => //; last first.
  by move=> t0; rewrite rotation_sub.
rewrite addrCA.
rewrite -mulmxE.
rewrite -mulNmx.
rewrite [X in _ = _ X]addrC.
rewrite !mulNmx.
by rewrite -mulmxA /= addrN addr0.
Qed.

End ya.

Definition S2 {K : realType} := [set x : 'rV[K]_3 | norm x = 1].

Section problem_statementA.
Variable K : realType.
Variable g0 : K.
Variable R : K -> 'M[K]_3.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.
Hypothesis derivableR : forall t, derivable R t 1.
Variable v : K -> 'rV[K]_3.
Let x1 t := v t.
Let x2 t : 'rV_3 := ('e_2) *m R t (* eqn (8) *). (* local frame ez ? *)
Let x1_dot t := 'D_1 x1 t.
Let x2_dot t := 'D_1 x2 t.
Let w t := ang_vel R t.

Lemma x2_S2 t : x2 t \in S2.
Proof.
by rewrite /S2 /x2 inE/= orth_preserves_norm ?normeE ?rotation_sub.
Qed.

(* not used but could be interesting *)
Lemma dRu t (u : K -> 'rV[K]_3) (T : K -> 'M[K]_3) (w' := ang_vel T)
  : 'D_1 (fun t => u t *m T t) t = u t *m T t *m \S(w' t) + 'D_1 u t *m T t.
Proof.
rewrite derive_mulmx; last 2 first.
  admit.
  admit.
rewrite addrC.
congr(_+_).
rewrite -ang_vel_mxE; last 2 first.
  admit.
  admit.
rewrite -mulmxA.
rewrite mulmxE.
rewrite -derive1mx_ang_vel; last 2 first.
  admit.
  admit.
by [].
Abort.

(* eqn 10 *)
Notation y_a := (y_a v R g0).
Lemma derive_x1 t : 'D_1 x1 t = x1 t *m \S(w t) + y_a t - g0 *: x2 t.
Proof.
rewrite /y_a/= -addrA addrK.
rewrite /x1.
rewrite addrCA addrA mulNmx /= /w.
by rewrite (addrC(-_)) subrr add0r.
Qed.

 (* eqn 11b *)
Lemma derive_x2 (t : K) : x2_dot t = x2 t *m \S( w t ).
Proof.
rewrite /w.
rewrite -ang_vel_mxE; last 2 first.
  by move=> ?; rewrite rotation_sub.
  by [].
rewrite /x2_dot.
rewrite /x2.
have ->: 'D_1 (fun t0 : K => 'e_2 *m (R t0)) t =
         'e_2 *m 'D_1 (fun t => (R t)) t.
  move => n /=.
  rewrite derive_mulmx//=.
  by rewrite derive_cst mul0mx add0r.
rewrite derive1mx_ang_vel /=; last 2 first.
  by move=> ?; rewrite rotation_sub.
  by [].
by rewrite mulmxA.
Qed.

End problem_statementA.

Section problem_statementB.
Variable K : realType.
Variable gamma : K.
Variable alpha1 : K.
Variable v : K -> 'rV[K]_3.
Variable R : K -> 'M[K]_3.
Hypothesis derivableR : forall t, derivable R t 1.
Let w t := ang_vel R t.
Variable x1_hat : K -> 'rV[K]_3.
Hypothesis derivable_x1_hat : forall t, derivable x1_hat t 1.
Variable x2_hat : K -> 'rV[K]_3.
Variable g0 : K.
Hypotheses g0_eq0 : g0 != 0.
Notation y_a := (y_a v R g0).
Let x1 t := v t .
Let x2'_hat t := -(alpha1 / g0) *: (x1 t - x1_hat t). (* 12b*)
Hypothesis eqn12a : forall t,
  'D_1 x1_hat t = x1_hat t *m \S(w t) + y_a t - g0 *: x2'_hat t.
Hypothesis eqn12c : forall t,
  'D_1 x2_hat t = x2_hat t *m \S(w t - gamma *: x2'_hat t *m \S(x2_hat t)).
Hypothesis x2_hat_S2 : x2_hat 0 \in S2.
Hypothesis x2_hat_derivable : forall t, derivable x2_hat t 1.
Hypothesis v_derivable : forall t, derivable v t 1.
Notation x2 := (x2 R).
(* estimation error *)
Let error1 t := x2 t - x2'_hat t. (* p_1 in [benallegue2023ieeetac] *)
Let error2 t := x2 t - x2_hat t. (* \tilde{x_2} in [benallegue2023ieeetac] *)
Let error1_dot t := 'D_1 error1 t.
Let error2_dot t := 'D_1 error2 t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.
(* projection from the local frame to the world frame(?) *)
Let error1_p t := error1 t *m (R t)^T (* z_p_1 in [benallegue2023ieeetac] *).
Let error2_p t := error2 t *m (R t)^T.
Hypothesis norm_x2_hat : forall t, norm (x2_hat t) = 1.

Let error1E : error1 = fun t => x2 t + (alpha1 / g0) *: (x1 t - x1_hat t).
Proof.
apply/funext => ?.
rewrite /error1 /x2; congr +%R.
by rewrite /x2'_hat scaleNr opprK.
Qed.

Let error2E t : error2 t = error2_p t *m R t.
Proof.
rewrite /error2 -mulmxA.
by rewrite orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

Let derivable_x2 t : derivable x2 t 1. Proof. exact: derivable_mulmx. Qed.

Let derivable_x2'_hat t : derivable x2'_hat t 1.
Proof. by apply: derivableZ => /=; exact: derivableB. Qed.

Let derivable_error1 t : derivable error1 t 1. Proof. exact: derivableB. Qed.

Let derivable_error2 t : derivable error2 t 1. Proof. exact: derivableB. Qed.

Lemma derive_error1 t :
  'D_1 error1 t = error1 t *m \S(w t) - alpha1 *: error1 t.
Proof.
simpl in *.
rewrite error1E.
rewrite deriveD//=; last first.
  by apply: derivableZ => /=; exact: derivableB.
rewrite deriveZ//=; last exact: derivableB.
rewrite deriveB//.
rewrite !(derive_x2) // -/(x2 t) /=.
rewrite (derive_x1  g0 R) //.
rewrite -/(x2 t) -/(v t) -/(x1 t) -/(w t).
rewrite eqn12a.
transitivity ((x2 t + (alpha1 / g0) *: (x1 t - x1_hat t)) *m \S(w t)
              - alpha1 *: error1 t).
  transitivity (x2 t *m \S(w t) + (alpha1 / g0)
                *: (x1 t *m \S(w t) - g0 *: x2 t - (x1_hat t *m \S(w t) - g0 *: x2'_hat t))).
    do 2 f_equal.
    rewrite -3![in LHS]addrA -[in RHS]addrA.
    congr +%R.
    rewrite opprD addrCA.
    rewrite [in RHS]opprB [in RHS]addrA [in RHS]addrC.
    congr +%R.
    by rewrite opprD addrACA subrr add0r opprK.
  rewrite (_ : x1 t *m \S(w t) - g0 *: x2 t - (x1_hat t *m \S(w t) - g0 *: x2'_hat t) =
               (x1 t - x1_hat t) *m \S(w t) - g0 *: (x2 t - x2'_hat t)); last first.
    rewrite mulmxBl scalerDr scalerN opprB addrA [LHS]addrC 2!addrA.
    rewrite -addrA; congr +%R.
      by rewrite addrC.
    by rewrite opprB addrC.
  rewrite -/(error1 t).
  rewrite scalerDr addrA scalemxAl -mulmxDl scalerN scalerA.
  by rewrite divfK.
by rewrite error1E.
Qed.

Lemma derive_error2 t :
  'D_1 error2 t = error2 t *m \S(w t) -
                  gamma *: (error2 t - error1 t) *m \S(x2_hat t) ^+ 2.
Proof.
rewrite /error2.
rewrite [in LHS]deriveB//.
rewrite derive_x2//.
rewrite -/(x2 t) -/(w t) -/(error2 t).
rewrite eqn12c.
rewrite spinD spinN -scalemxAl (spinZ gamma).
rewrite mulmxBr opprB [LHS]addrA.
rewrite [in LHS]addrC addrA (addrC _ (x2 t *m \S(w t))).
rewrite -mulmxBl -/(error2 t).
congr +%R.
rewrite -scalemxAr -mulNmx -scalerN -[RHS]scalemxAl.
congr (_ *: _).
rewrite /error2 /error1.
rewrite (opprB _ (x2'_hat t)) -addrA (addrC (x2 t)) addrA.
rewrite subrK opprD opprK mulmxBl.
rewrite [X in _ = X + _](_ : _ = 0) ?add0r; last first.
  rewrite mulmxA.
  rewrite -(mulmxA(x2_hat t)) sqr_spin //.
  rewrite mulmxDr !mulmxA.
  rewrite dotmul1 // mul1mx.
  by rewrite mulmxN mulmx1 subrr.
rewrite expr2 -mulmxE fact215 -mulmxE -spin_crossmul.
rewrite [in RHS]mulmxA [in RHS]spinE spinE spinE.
by rewrite [LHS](@lieC _ (vec3 K)).
Qed.

Lemma Rx2 t : x2_hat t *m (R t)^T = 'e_2 - error2_p t.
Proof.
rewrite /error2_p /error2 mulmxBl opprB addrCA.
rewrite [X in _ + X](_ : _ = 0) ?addr0//.
rewrite /x2 -mulmxA.
by rewrite orthogonal_mul_tr ?rotation_sub// mulmx1 subrr.
Qed.

Lemma derive_error1_p t : 'D_1 error1_p t = -alpha1 *: error1_p t.
Proof.
rewrite /error1.
rewrite derive_mulmx//=; last by rewrite derivable_trmx.
rewrite derive_error1.
rewrite mulmxBl addrAC.
apply/eqP.
rewrite subr_eq.
rewrite [in eqbRHS]addrC scaleNr scalemxAl subrr /=.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel //; last by move => t0; rewrite rotation_sub.
rewrite ang_vel_mxE //; last by move => t1 ; rewrite rotation_sub.
rewrite -/(w t) -mulmxA -mulmxDr trmx_mul tr_spin.
by rewrite mulNmx subrr mulmx0.
Qed.

Lemma derive_error2_p t : 'D_1 error2_p t = gamma *: (error2_p t - error1_p t) *m - \S('e_2 - error2_p t)^+2.
Proof.
rewrite [LHS]derive_mulmx//=; last first.
  by rewrite derivable_trmx.
simpl in *.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel//=; last first.
  by move => t0; rewrite rotation_sub.
rewrite !ang_vel_mxE//; last first.
  by move => t0; rewrite rotation_sub.
rewrite trmx_mul mulmxA -mulmxDl.
rewrite derive_error2 /=.
rewrite addrAC -/(w t) tr_spin mulmxN subrr sub0r.
rewrite -scalemxAl -scaleNr -scalemxAl.
rewrite mulmxN -scalemxAl -[in RHS]scaleNr.
congr (- _ *: _).
rewrite -Rx2.
rewrite -spin_similarity ?rotationV//.
rewrite trmxK.
rewrite [in RHS]expr2 -mulmxE !mulmxA.
congr (_ *m _ *m _).
rewrite -[in RHS]mulmxA.
rewrite orthogonal_tr_mul ?rotation_sub// mulmx1.
congr (_ *m _).
rewrite error2E.
rewrite mulmxBl; congr (_ - _)%R.
by rewrite /error1 -mulmxA orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

End problem_statementB.

Definition state_space_tilt {K : realType} :=
  [set x : 'rV[K]_6 | norm ('e_2 - Right x) = 1].

Section tilt_eqn.
Variable K : realType.
Variable alpha1 : K.
Variable gamma : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.

Definition tilt_eqn (f : K -> 'rV[K]_6) : K ->'rV[K]_6 :=
  let error1_p_dot := Left \o f in
  let error2_dot := Right \o f in
  fun t => row_mx
    (- alpha1 *: error1_p_dot t)
    (gamma *: (error2_dot t - error1_p_dot t) *m \S('e_2 - error2_dot t) ^+ 2).

Definition tilt_eqn_no_time (zp1_z2_point : 'rV[K]_6) : 'rV[K]_6 :=
  let zp1_point := Left zp1_z2_point in
  let z2_point := Right zp1_z2_point in
  row_mx (- alpha1 *: zp1_point)
         (gamma *: (z2_point - zp1_point) *m \S('e_2%:R - z2_point) ^+ 2).

Lemma tilt_eqnE f t : tilt_eqn f t = tilt_eqn_no_time (f t).
Proof. by []. Qed.

Lemma tilt_eqn_no_time_lipschitz : exists k, k.-lipschitz_setT tilt_eqn_no_time.
Proof.
near (pinfty_nbhs K) => k.
exists k => -[/= x x0] _.
rewrite /tilt_eqn_no_time.
set fx := row_mx (- alpha1 *: Left x)
                 (gamma *: (Right x - Left x) *m \S('e_2 - Right x) ^+ 2).
set fy := row_mx (- alpha1 *: Left x0)
                 (gamma *: (Right x0 - Left x0) *m \S('e_2 - Right x0) ^+ 2).
rewrite /Num.norm/=.
rewrite !mx_normrE.
apply: bigmax_le => /=.
  rewrite mulr_ge0//.
  apply: le_trans; last first.
    exact: (le_bigmax _ _ (ord0, ord0)).
  by [].
move=> -[a b] _.
rewrite /=.
rewrite [leRHS](_ : _ =
    \big[maxr/0]_ij (maxr alpha1 gamma * `|(x - x0) ij.1 ij.2|)); last first.
  admit.
rewrite (le_trans (@ler_peMl _ (maxr alpha1 gamma) _ _ _))//.
  admit.
apply: le_trans; last first.
  exact: (@le_bigmax _ _ _ 0
    (fun ij => maxr alpha1 gamma * `|(x - x0) ij.1 ij.2|) (a, b)).
rewrite /=.
apply: (@le_trans _ _
    (`|(maxr alpha1 gamma *: fx - maxr alpha1 gamma *: fy) a b|)).
  admit.
apply: (@le_trans _ _
    (`|maxr alpha1 gamma *: x a b - maxr alpha1 gamma *: x0 a b|)); last first.
Abort.

(* cauchy lipschitz par F1 qui definit un champ de vecteur lisse :
il existe une solution depuis tout point:
gamma1 ⊆ state_space*)
(* prouver invariance geometrique, tangence donc les trajectoires restent dans gamma1:
 state_space ⊆ gamma1
*)

Lemma invariant_state_space_tilt p
  (p33 : state_space tilt_eqn state_space_tilt p) :
  let y := sval (cid p33) in
  let t := sval (cid (svalP (cid p33)).2) in
  forall Delta, Delta >= 0 -> state_space tilt_eqn state_space_tilt (y (t + Delta)).
Proof.
case: p33 => /= x0 sol_y Delta Delta_ge0.
rewrite /state_space/=.
exists x0; split.
  by case: sol_y.
case: cid => //= y' y'sol.
case: cid => t'/= pt'.
Abort.

Lemma state_space_tiltS :
  state_space tilt_eqn state_space_tilt `<=` state_space_tilt.
Proof.
- move=> p [y [[y0_init1]] deri y33 ] [t ->].
  rewrite /state_space_tilt.
  have : derive1 (fun t=> ('e_2 - Right (y t)) *d (('e_2 - Right (y t)))) = 0.
    transitivity (fun t => -2 * (Right(y^`()%classic t) *d ('e_2 - Right (y t)))).
      apply/funext => x.
      rewrite !derive1E.
      rewrite derive_mx; last first.
        by auto.
      rewrite /dotmul.
      under eq_fun do rewrite dotmulP /=.
      rewrite dotmulP.
      rewrite !mxE /= mulr1n.
      under eq_fun do rewrite !mxE /= mulr1n.
      rewrite !derive_dotmul/=; last 2 first.
        by apply: derivableB => //=; exact : derivable_rsubmx => //=.
        by apply: derivableB => //=; exact: derivable_rsubmx => //=.
      rewrite /dotmul /=.
      rewrite [in RHS]mulr2n [RHS]mulNr [in RHS]mulrDl.
      rewrite !mul1r !dotmulP /= dotmulC [in RHS]dotmulC !linearD /=.
      rewrite !mxE /= !mulr1n.
      have -> : 'D_1 (fun x2 : K => 'e_2 - Right (y x2)) x = - Right ('D_1 y x).
        rewrite deriveB /= ; last 2 first.
          exact: derivable_cst.
          exact: derivable_rsubmx.
        rewrite derive_cst /= sub0r; congr (- _).
        exact: derive_rsubmx.
      rewrite -(_ : 'D_1 y x = (\matrix_(i, j) 'D_1 (fun t0 : K => y t0 i j) x)); last first.
        apply/matrixP => a b; rewrite !mxE.
        rewrite derive_mx//= ?mxE//.
      ring.
  have Rsu t0 : (Right (y^`()%classic t0) =
                  (gamma *: (Right (y t0) - Left (y t0)) *m \S('e_2 - Right (y t0)) ^+ 2)).
      rewrite derive1E.
      rewrite y33.
      by rewrite row_mxKr.
    apply/funext => t0.
    rewrite /dotmul.
    transitivity (-2 * (gamma *: (Right (y t0) - Left (y t0)) *m \S('e_2 - Right (y t0)) ^+ 2
             *m ('e_2 - Right (y t0))^T) 0 0).
      by rewrite Rsu /=.
    rewrite !mulmxA.
    apply/eqP.
    rewrite mulf_eq0 /= oppr_eq0 ?pnatr_eq0 /= -!mulmxA spin_mul_tr.
    by rewrite !mulmx0 mxE.
  under eq_fun do rewrite dotmulvv /=. (* derivee de la norme est egale a 0 *)
  move => h.
  have norm_constant : forall t, norm ('e_2 - Right (y t))^+2 = norm ('e_2 - Right (y 0))^+2.
    move => t0.
    have : forall x0, is_derive x0 (1:K) (fun x : K => norm ('e_2 - Right (y x)) ^+ 2) 0.
      move => x0.
      apply: DeriveDef.
      apply/derivable_norm_squared => //=.
          apply/derivableB => //=.
          apply/derivable_rsubmx => //.
      by rewrite -derive1E h.
    rewrite /=.
    move/is_derive_0_is_cst.
    move/ (_ _ 0).
    move => s0.
    by apply: s0.
  suff: norm ('e_2 - Right (y t)) ^+ 2 = 1.
    move => /(congr1 Num.sqrt).
    rewrite sqrtr1 sqr_sqrtr //.
    by rewrite dotmulvv sqr_ge0.
  rewrite norm_constant.
  move: y0_init1.
  rewrite inE /state_space_tilt /= => ->.
  by rewrite expr2 mulr1.
Qed.

Definition point1 : 'rV[K]_6 := 0.
Definition point2 : 'rV[K]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2).

Lemma equilibrium_point1 : is_equilibrium_point tilt_eqn point1 state_space_tilt.
Proof.
split => //=.
- rewrite inE /state_space_tilt /point1.
  rewrite /=.
  by rewrite rsubmx_const /= subr0 normeE.
- move=> t ; rewrite derive_cst /tilt_eqn /point1; apply/eqP.
  rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP. split.
    rewrite scaler_eq0; apply/orP; right; apply/eqP/rowP; move => i.
    rewrite /=.
    by rewrite lsubmx_const.
  apply/eqP/rowP; move => i; apply/eqP; set N := (X in _ *: X *m _); have : N = 0.
    rewrite /N /=; apply /rowP; move => a.
    rewrite !mxE.
    by rewrite subrr.
  by move => n; rewrite n scaler0 mul0mx.
Qed.

Lemma equilibrium_point2 : is_equilibrium_point tilt_eqn point2 state_space_tilt.
Proof.
split => //.
- rewrite inE /state_space_tilt /point2 /=.
  rewrite row_mxKr.
  rewrite -[X in X - _ ]scale1r.
  rewrite -scalerBl normZ normeE mulr1 distrC.
  rewrite [X in _ - X](_:1 = 1%:R) //.
  by rewrite -natrB //= normr1.
- move => t. rewrite derive_cst; apply /eqP; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
  set N := (X in _ *: X == 0 /\ _).
  have N0 : N = 0.
    apply/rowP; move => i; rewrite !mxE; case: splitP.
      move => j _; by rewrite mxE.
    move => k /= i3k.
    have := ltn_ord i.
    by rewrite i3k -ltn_subRL subnn.
  split.
    by rewrite scaler_eq0 N0 eqxx orbT.
  rewrite -scalemxAl scalemx_eq0 gt_eqF//=.
  rewrite -[Left point2]/N N0 subr0.
  set M := (X in X *m _); rewrite -/M.
  have ME : M = 2 *: 'e_2.
    apply/rowP => i; rewrite !mxE eqxx/=.
    case: splitP => [j ij|j]/=.
      have := ltn_ord j.
      by rewrite -ij.
    move/eqP.
    rewrite eqn_add2l => /eqP /ord_inj ->.
    by rewrite !mxE eqxx/=.
  rewrite ME -scalemxAl scalemx_eq0 pnatr_eq0/= [X in X *: _](_ : _ = 1 + 1)// scalerDl scale1r opprD addrA subrr sub0r spinN sqrrN expr2 -mulmxE mulmxA.
  by rewrite (_ : 'e_2 *m _ = 0) ?mul0mx// ; apply: trmx_inj; rewrite trmx_mul trmx0 tr_spin mulNmx spin_mul_tr oppr0.
Qed.

Variable F1 : 'rV[K]_6 -> 'rV[K]_6.
Variable sol : 'rV[K]_6 -> K -> 'rV[K]_6.
Hypothesis sol_correct : forall x0, ('D_1 fun t=> (sol x0 t)) = fun t => F1 (sol x0 t).
Definition tilt_eqn_interface (x : 'rV_6) (t : K) : 'rV_6 :=
  tilt_eqn (fun _ => x) t.

(*Hypothesis invariant_gamma : is_invariant tilt_eqn_interface (state_space_tilt). a transformer en lemme*)

(* this lemma asks for Lyapunov + lasalle *)
Lemma tractories_converge (y : K -> 'rV[K]_6) : is_sol tilt_eqn y state_space_tilt ->
  y t @[t --> +oo] --> point1 \/ y t @[t --> +oo] --> point2.
Proof.
move=> is_sol_y.
Abort.

End tilt_eqn.
Arguments point1 {K}.

Open Scope classical_set_scope.

(* technical section, skip on a first reading *)
Section u2.
Context {K : realType}.

Definition u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2) [eta (fun=> 0) with
  (0,0) |-> 1,
  (0,1) |-> -2^-1,
  (1,0) |-> -2^-1,
  (1,1) |-> 1] (i, j).

Lemma u2neq0 : u2 != 0.
Proof. by apply/matrix0Pn; exists 1, 1; rewrite mxE /= oner_neq0. Qed.

Lemma u2_sym : u2 \is sym 2 K.
Proof.
rewrite /= symE.
apply/eqP/matrixP.
move => i j.
rewrite !mxE/=.
case: ifPn => [/eqP[->{i} ->{j}//]|].
case: ifPn => [/eqP[->{i} ->{j}//]|].
case: ifPn => [/eqP[->{i} ->{j}//]|].
case: ifPn => [/eqP[->{i} ->{j}//]|].
by move: i j => [[|[|//]]] /= ? [[|[|]]].
Qed.

Lemma tr_u2 : \tr u2 = 2.
Proof. by rewrite /u2/= /mxtrace /= sum2E/= !mxE/=. Qed.

Lemma det_u2 : \det u2 = 3/4.
Proof. by rewrite /u2 det_mx22 /= !mxE /=; field. Qed.

Lemma posdefmxu2 : posdefmx u2.
Proof.
split; first exact: u2_sym.
move=> a.
move/eigenvalueP => [u] /[swap] u0 H.
have a_eigen : eigenvalue u2 a.
  apply/eigenvalueP.
  exists u. rewrite /u2.
    exact: H.
  exact: u0.
have : root (char_poly u2) a.
  rewrite -eigenvalue_root_char.
  exact : a_eigen.
rewrite char_poly2 tr_u2 det_u2 rootE => a_root .
have char_poly_fact : 'X^2 - 2%:P * 'X + (3/4)%:P =
    ('X - (1%:R / 2)%:P) * ('X - (3%:R / 2)%:P) :> {poly K}.
  rewrite mulrBr mulrBl -expr2 -!addrA; congr +%R.
  rewrite mulrBl opprB addrCA addrC; congr +%R.
    by rewrite -[RHS]polyCM; congr (_%:P); field.
  rewrite [in RHS]mulrC -opprD -mulrDr mulrC; congr (- (_ * _)).
  by rewrite -polyCD; congr (_%:P); by field.
move: a_root.
rewrite char_poly_fact hornerM !hornerXsubC.
by rewrite mulf_eq0 => /orP[|]; rewrite subr_eq0 => /eqP ->; rewrite divr_gt0.
Qed.

End u2.

Section V1.
Local Open Scope classical_set_scope.
Context {K : realType}.
Variables alpha1 gamma : K.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.

Definition V1 (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  (norm zp1)^+2 / (2 * alpha1) + (norm z2)^+2 / (2 * gamma).

Lemma V1_is_Lyapunov_candidate : is_Lyapunov_candidate V1 [set: 'rV_6] point1.
Proof.
rewrite /locposdef. (*; split; last first.
  rewrite /V1.
  apply/differentiableD => //; last first.
    apply/differentiableM => //; apply/differentiable_norm_squared => //=.
    exact/differentiable_rsubmx.
  apply/differentiableM => //; apply/differentiable_norm_squared => //=.
  exact/differentiable_lsubmx.*)
rewrite /V1 /point1 /locposdef; split; first by rewrite inE.
split.
  by rewrite lsubmx_const rsubmx_const norm0 expr0n/= !mul0r add0r.
move=> /= z_near _ z0.
have /orP[lz0|rz0] : (Left z_near != 0) || (Right z_near != 0).
  rewrite -negb_and.
  apply: contra z0 => /andP[/eqP l0 /eqP r0].
  rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
  apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?;
  by rewrite mxE.
- set rsub := Right z_near.
  have : norm rsub >= 0 by rewrite norm_ge0.
  set lsub := Left z_near.
  move=> nor.
  have normlsub : norm lsub > 0 by rewrite norm_gt0.
  rewrite ltr_pwDl//.
    by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
  by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
- rewrite ltr_pwDr//.
    by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0// norm_gt0.
  by rewrite divr_ge0 ?exprn_ge0 ?norm_ge0// mulr_ge0// ltW.
Unshelve. all: by end_near. Qed.

Definition V1dot (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  - (norm zp1)^+2 + (z2 *m (\S('e_2 - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2 - z2))^+2 *m zp1^T)``_0.

End V1.

Section hurwitz.
Context {K : realType}.

(* thm 4.6 p136*)
Definition hurwitz n (A : 'M[K]_n.+1) : Prop :=
  (forall a, eigenvalue A a -> a < 0).

(* thm 4.7 p139 + fact: it is exponentially stable*)
Definition locally_exponentially_stable_at n (eqn : 'rV[K]_n.+1 -> 'rV[K]_n.+1)
    (point : 'rV[K]_n.+1) : Prop :=
  hurwitz (jacobian eqn point).

Lemma tilt_eqn_is_locally_exponentially_stable_at_0 alpha1 gamma :
  locally_exponentially_stable_at (tilt_eqn_no_time alpha1 gamma) point1.
Proof.
rewrite /locally_exponentially_stable_at /jacobian /hurwitz.
move => a.
move/eigenvalueP => [u] /[swap] u0 H.
have a_eigen : eigenvalue (jacobian (tilt_eqn_no_time alpha1 gamma) point1) a.
  apply/eigenvalueP.
  exists u.
    exact: H.
  exact: u0.
have : root (char_poly (jacobian (tilt_eqn_no_time alpha1 gamma) point1)) a.
  rewrite -eigenvalue_root_char.
  exact : a_eigen.
rewrite /tilt_eqn_no_time /jacobian.
Abort.

End hurwitz.

Section tilt_eqn_Lyapunov.
Local Open Scope classical_set_scope.
Context {K : realType}.
Variable alpha1 : K.
Variable gamma : K.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.
Variable R : K -> 'M[K]_3.

Lemma derive_zp1 (z : K) (traj : K -> 'rV_6) :
  is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  'D_1 (Left \o traj) z = - alpha1 *: Left (traj z).
Proof.
move=> [/= traj0 dtraj].
move=> /(_ z)/(congr1 Left).
by rewrite row_mxKl => ?; rewrite derive_lsubmx//=.
Qed.

Lemma derive_z2  (z : K) (traj : K -> 'rV_6) : is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt ->
   'D_1 (Right \o traj) z =
   gamma *: (Right (traj z) - Left (traj z)) *m \S('e_2 - Right (traj z)) ^+ 2.
Proof.
move=> [/= traj0 dtraj].
by move => /(_ z)/(congr1 Right); rewrite row_mxKr => ?; rewrite derive_rsubmx//=.
Qed.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

Lemma derive_V1dot (z : K) (traj : K -> 'rV_6)
  (zp1 := Left \o traj) (z2 := Right \o traj) :
  is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  c1 *: (2 *: 'D_1 zp1 z *m (Left (traj z))^T) 0 0 +
  c2 *: (2 *: 'D_1 z2 z *m (Right (traj z))^T) 0 0
  = V1dot (traj z).
Proof.
move=> ?.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite derive_zp1 // -scalemxAl mxE [X in X + _](mulrA (alpha1^-1) (- alpha1)) mulrN mulVf ?gt_eqF// mulN1r.
rewrite derive_z2 // -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE scalerA mulVf ?gt_eqF// scale1r.
rewrite norm_squared /V1dot.
congr +%R.
rewrite -2![in RHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
rewrite -[X in _ = (X *m (_ *m _)) 0 0]trmxK -[X in _ = (_ *m (X *m _)) 0 0]trmxK.
rewrite mulmxA -trmx_mul -trmx_mul [RHS]mxE.
rewrite -(mulmxA (Right (traj z) - (Left (traj z)))) mulmxE -expr2.
rewrite tr_sqr_spin.
by rewrite mulmxA.
Qed.

Lemma is_sol_state_space_tilt (sol : K -> 'rV_6) t :
  is_sol (tilt_eqn alpha1 gamma) sol state_space_tilt ->
  state_space_tilt (sol t).
Proof.
case => sol0 dsol deriv_sol.
apply: (@state_space_tiltS _ alpha1 gamma) => //=.
exists sol; split => //.
by exists t.
Qed.

Lemma norm_u1 (traj : K -> 'rV_6) (z : K) (z2 := Right \o traj)
    (zp1 := Left \o traj) (u := 'e_2 - z2 z) :
  is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt -> norm u = 1.
Proof.
move=> dtraj.
suff: state_space_tilt (row_mx (zp1 z) (z2 z)).
  by rewrite /state_space_tilt/= row_mxKr.
rewrite /zp1 /z2 hsubmxK /=.
exact: is_sol_state_space_tilt.
Qed.

Lemma deriveV1 (x : 'rV[K]_6) t sol :
  is_sol (tilt_eqn alpha1 gamma) (sol x) state_space_tilt ->
  (forall t, differentiable (sol x) t) ->
  'D~(sol, x) (V1 alpha1 gamma) t = V1dot (sol x t).
Proof.
rewrite /tilt_eqn => tilt_eqnx dif1.
rewrite /V1 derive_alongD; last 3 first.
  apply/differentiableM => //=.
  exact/differentiable_norm_squared/differentiable_lsubmx.
  apply/differentiableM => //=.
  exact/differentiable_norm_squared/differentiable_rsubmx.
  exact: dif1.
under [X in derive_along X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl => //; last first.
  exact/differentiable_norm_squared/differentiable_lsubmx.
rewrite derive_alongMl => //; last first.
  exact/differentiable_norm_squared/differentiable_rsubmx.
rewrite -fctE /= !derive_along_norm_squared//=.
- rewrite -derive_V1dot.
    by rewrite /c1 /c2 !invfM.
  rewrite /= in tilt_eqnx.
  exact: tilt_eqnx.
- exact/differentiable_lsubmx.
- exact/differentiable_rsubmx.
Qed.

(* TODO: Section general properties of our system *)

Lemma angvel_sqr (traj : K -> 'rV_6) (z : K)  (z2 := fun r : K => Right (traj r) : 'rV_3)
  (w := (z2 z) *m \S('e_2)) (u := 'e_2 - z2 z) :
  is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  (w *m \S(u)) *d (w *m \S(u)) = (w *d w) * (u *d u) - (w *d u) ^+ 2.
Proof.
move=> dtraj.
rewrite /dotmul !trmx_mul !tr_spin !mulNmx mulmxN opprK mulmxN !dotmulP.
have key_ortho : (z2 z *m \S('e_2)) *d u = 0.
 by rewrite dotmulC; exact/ortho_spin.
rewrite key_ortho expr2.
rewrite [in RHS]mxE.
rewrite [X in _ =  - (w *m (\S('e_2) *m (z2 z)^T)) 0 0 * (u *d u)%:M 0 0 - 0%:M 0 0 * X]mxE mulr1n mulr0 subr0/=.
rewrite /u -/w /dotmul.
have Hw_ortho : (w *d u) = 0 by rewrite /u dotmulC ortho_spin.
rewrite !mulmxA dotmulP dotmulvv norm_u1 // expr2 mulr1.
rewrite [X in _ =  - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1n /=.
rewrite [X in _ =   - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1.
have wu0 : w *m u^T *m u = 0 by rewrite dotmulP Hw_ortho mul_scalar_mx scale0r.
rewrite -[in LHS](mulmxA w) sqr_spin; last first.
  by rewrite -/u norm_u1.
rewrite [in LHS]mulmxBr mulmxA wu0 sub0r.
by rewrite 2!mulNmx mulmx1 mxE.
Qed.

Lemma neg_spin (traj : K -> 'rV_6) (z : K) :
  is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  norm (Right (traj z) *m \S('e_2) *m - \S('e_2 - Right (traj z))) =
  norm (Right (traj z) *m \S('e_2)).
Proof.
move=> dtraj.
rewrite mulmxN normN.
pose zp1 := fun r => Left (traj r).
pose z2 := fun r => Right (traj r).
set w := (z2 z) *m \S('e_2).
have Gamma1_traj t : state_space_tilt (traj t) by apply/is_sol_state_space_tilt.
rewrite /norm.
rewrite !dotmulvv [RHS]sqrtr_sqr sqrtr_sqr.
have Hnorm_sq : norm (w *m \S('e_2 - Right (traj z))) ^+ 2 = norm w ^+ 2.
  rewrite -!dotmulvv angvel_sqr // !dotmulvv norm_u1 /= //.
  rewrite -!dotmulvv expr2 !mul1r mulr1.
  have -> : w *d ('e_2 - Right (traj z)) = 0.
    by rewrite dotmulC ortho_spin.
  by rewrite expr2 mul0r subr0.
 rewrite !normr_norm.
  by move/sqr_inj : Hnorm_sq => ->//; rewrite ?nnegrE ?norm_ge0.
Qed.

Lemma V1dot_ub (traj : K -> 'rV_6) (zp1 := Left \o traj) (z2 := Right \o traj) :
  is_sol (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  forall z,
  let w := z2 z *m \S('e_2) in
  let u1 : 'rV[K]_2 :=
    \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i in
  V1dot (traj z) <= (- u1 *m u2 *m u1^T) 0 0.
Proof.
move=> dtraj z.
set w := z2 z *m \S('e_2).
pose u1 := \row_i [eta fun=> 0 with 0 |-> norm (zp1 z), 1 |-> norm w] i.
rewrite /V1dot.
rewrite mxE norm_spin mxE addrA expr2 mulmxA.
have -> : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2).
  by rewrite spinD spinN -tr_spin !mulmxDr !mul_tr_spin !addr0.
rewrite -dotmulNv addrC -mulmxN -expr2.
have cauchy : ((w *m - \S('e_2 - z2 z) *d (zp1 z))%:M : 'rV_1) 0 0 <=
              norm(w *m - (\S('e_2 - z2 z))) * norm(zp1 z).
  rewrite mxE /= mulr1n (le_trans (ler_norm _)) //.
  rewrite -ler_sqr // ; last first.
    by rewrite nnegrE //  mulr_ge0 ?norm_ge0.
  by rewrite exprMn sqr_normr (le_trans (CauchySchwarz_vec _ _)) // !dotmulvv.
apply: (@le_trans _ _ (norm (w *m - \S('e_2 - z2 z)) * norm (zp1 z) + (- norm (zp1 z) ^+ 2 - norm w ^+ 2))).
  rewrite lerD2r.
  rewrite (le_trans _ (cauchy)) //.
  by rewrite mxE eqxx mulr1n.
rewrite neg_spin /u1 /u2 //.
rewrite mxE.
rewrite !sum2E/= ![in leRHS]mxE !sum2E/= ![in leRHS]mxE /=.
rewrite !mulr1 mulrN mulNr opprK mulrDl mulNr -expr2.
rewrite [in leLHS] addrCA -!addrA lerD2l mulrDl (mulNr (norm w)).
rewrite -expr2 !addrA lerD2r !(mulrN , mulNr) opprK -mulrA.
rewrite [in leRHS](mulrC (_ / 2)) (mulrC 2^-1) -mulrDr -splitr.
by rewrite [leRHS]mulrC.
Qed.

(* TODO: rework of this proof is needed *)
Lemma near0_le0 sol x :
  is_sol (tilt_eqn alpha1 gamma) (sol x) state_space_tilt ->
  sol x 0 = point1 ->
  \forall z \near 0^',
    ('D~(sol, x) (fun x => norm (Left x) ^+ 2 / (2 * alpha1)) +
     'D~(sol, x) (fun x => norm (Right x) ^+ 2 / (2 * gamma))) z <= 0.
Proof.
move=> dtraj traj0.
rewrite fctE !invfM /=.
near=> z.
under [X in derive_along X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _ _]eq_fun do rewrite mulrC.
move: dtraj => [H0 Hderiv Htilt].
have Hz_derivable : derivable (sol x) z 1.
  by apply: Hderiv.
rewrite derive_alongMl; last 2 first.
  exact/differentiable_norm_squared/differentiable_lsubmx.
  apply derivable1_diffP.
  exact: Hderiv.
rewrite derive_alongMl; last 2 first.
  exact/differentiable_norm_squared/differentiable_rsubmx.
  exact/derivable1_diffP.
rewrite /= !derive_along_norm_squared; last 4 first.
  exact/differentiable_rsubmx.
  exact/derivable1_diffP.
  exact/differentiable_lsubmx.
  exact/derivable1_diffP.
rewrite derive_V1dot //.
pose zp1 := Left \o sol x.
pose z2 := Right \o sol x.
set w := (z2 z) *m \S('e_2).
pose u1 : 'rV[K]_2 :=
  \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i.
apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
  exact: V1dot_ub.
have := @posdefmxu2 K.
rewrite posdefmxP => def.
have [->|H] := eqVneq u1 0.
  by rewrite mulNmx mul0mx mulNmx mul0mx mxE mxE oppr0.
have Hpos := def u1 H.
rewrite -oppr_ge0 -oppr_le0 opprK ltW//.
by rewrite -oppr_gt0 mulNmx !mulNmx mxE opprK Hpos.
Unshelve. all: try by end_near. Qed.

(* NB: should be completed to prove asymptotic stability *)
Lemma V1_dot_is_lnsd sol x :
  is_sol (tilt_eqn alpha1 gamma) (sol x) state_space_tilt ->
  sol x 0 = point1 ->
  locnegsemidef ('D~(sol, x) (V1 alpha1 gamma)) 0.
Proof.
move=> [y033] dy dtraj traj0.
rewrite /locnegsemidef /V1.
rewrite derive_alongD /=; last 3 first.
  apply: differentiableM => /=; last exact: differentiable_cst.
  exact/differentiable_norm_squared/differentiable_lsubmx.
  apply: differentiableM; last exact: differentiable_cst.
  exact/differentiable_norm_squared/differentiable_rsubmx.
  exact/derivable1_diffP.
split; last first.
  near=> z.
  rewrite derive_along_derive //; last exact/derivable1_diffP.
  admit. (* TODO: lynda *)
  admit. (* TODO: lynda *)
under [X in derive_along X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl; last 2 first.
  exact/differentiable_norm_squared/differentiable_lsubmx.
  exact/derivable1_diffP.
rewrite derive_alongMl; last 2 first.
 exact/differentiable_norm_squared/differentiable_rsubmx.
 exact/derivable1_diffP.
rewrite /= !derivative_derive_along_eq0; last 4 first.
  exact/differentiable_norm_squared/differentiable_rsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
    exact/differentiable_norm_squared/differentiable_lsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
by rewrite scaler0 scaler0 add0r.
Abort.

(* forall z? *)
Lemma V1_dot_is_lnd sol x
   (zp1 := Left \o sol x) (z2 := Right \o sol x) :
  is_sol (tilt_eqn alpha1 gamma) (sol x) state_space_tilt ->
  (forall t : K, state_space_tilt (sol x t)) ->
  sol x 0 = point1 ->
  lnd ('D~(sol, x) (V1 alpha1 gamma)) 0.
Proof.
move=> solves state y0.
split.
  rewrite /is_sol in solves.
  rewrite /= derivative_derive_along_eq0 => //; last first.
    admit.
  rewrite /V1.
  apply: differentiableD => //; last first.
    apply: differentiableM; last exact: differentiable_cst.
    exact/differentiable_norm_squared/differentiable_rsubmx.
  apply: differentiableM => //.
  exact/differentiable_norm_squared/differentiable_lsubmx.
near=> z0.
rewrite deriveV1.
- have V1dot_le := V1dot_ub solves z0 => //.
  have := @posdefmxu2 K.
  rewrite posdefmxP => def.
  set w := z2 z0 *m \S('e_2).
  set u1 : 'rV[K]_2 := \row_(i < 2)
    [eta (fun=> 0) with 0 |-> norm (zp1 z0), 1 |-> norm w] i.
  have Hpos : 0 <  (u1 *m u2 *m u1^T) 0 0.
    apply: def.
    rewrite /u1.
    admit.
  have Hneg : -  (u1 *m u2 *m u1^T) 0 0 < 0 by rewrite oppr_lt0.
  rewrite lt_neqAle.
  apply/andP; split; last first.
    apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
      by [].
    have -> : (- u1 *m u2 *m u1^T) 0 0 = - (u1 *m u2 *m u1^T) 0 0.
      rewrite !mxE -sumrN.
      under [in RHS]eq_bigr do rewrite -mulNr.
      by under eq_bigr do rewrite mulNmx mxE.
    exact/ltW.
  rewrite /V1dot.
  rewrite mxE/=.
  apply/eqP => Habs.
  admit.
- by [].
- move => t.
  apply/derivable1_diffP => //.
  move : solves; rewrite /is_sol.
  by case.
Unshelve. all: by end_near.
Abort.

(*Definition is_Lyapunov_stable_at {K : realType} {n}
  (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
  (A : set 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> K)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0 A,
      is_Lyapunov_candidate V setT x0 &
      forall traj1 traj2 : (K -> 'rV[K]_n.+1),
        is_sol f traj1 A ->
        traj1 0 = x0 ->
        locnegsemidef (derive_along V (fun a => traj1) 0 ) 0].*)

(*Lemma V1_is_Lyapunov_stable :
  is_Lyapunov_stable_at (tilt_eqn alpha1 gamma) state_space_tilt (V1 alpha1 gamma) point1.
Proof.
split.
- exact: equilibrium_point1.
- exact: V1_is_Lyapunov_candidate.
(*- by move=> traj1 ? ?; exact: V1_point_is_lnsd.
Qed.*) Abort.*)

Lemma V1_dot_le0 sol x :
  is_sol (tilt_eqn alpha1 gamma) (sol x) state_space_tilt ->
  (forall t, differentiable (sol x) t) ->
  forall t : K, 0 <= t ->
  'D~(sol, x) (V1 alpha1 gamma) t <= 0.
Proof.
move=> solves diff t t0.
rewrite deriveV1//.
have Hub := V1dot_ub solves t.
have := @posdefmxu2 K.
rewrite posdefmxP => def.
apply: (le_trans Hub).
have Hquad : let u1 := \row_i [eta fun=> 0
                   with 0 |-> norm ((Left \o sol x) t),
                        1 |-> norm ((Right \o sol x) t *m \S('e_2))]
                         i in 0 <= (u1 *m u2 *m u1^T) 0 0.
set u1 := \row_i [eta fun=> 0
                   with 0 |-> norm ((Left \o sol x) t),
                        1 |-> norm ((Right \o sol x) t *m \S('e_2))]
            i.
rewrite /=.
case: (u1 =P 0) => [->|/eqP u1_neq0].
  by rewrite !mul0mx mxE.
  apply: ltW.
  exact: (def u1 u1_neq0).
rewrite -oppr_ge0.
by rewrite !mulNmx mxE opprK Hquad.
Qed.

End tilt_eqn_Lyapunov.

Section equilibrium_zero_stable.
Context {K : realType}.
Variables gamma alpha1 : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Variable D : set 'rV[K]_6.
Variable sol : 'rV[K]_6 -> K -> 'rV[K]_6.
Hypothesis solP : existence_uniqueness D (tilt_eqn alpha1 gamma) sol.
Hypothesis sol0 : initial_condition sol.

Hypothesis y0 : 0 \in D.
Hypothesis y_sol : is_sol (tilt_eqn alpha1 gamma) (sol 0) D.
Hypothesis y00 : sol 0 0 = 0.

Lemma is_equilibrium_subset :
  (is_equilibrium_point (tilt_eqn alpha1 gamma)) 0 state_space_tilt ->
  (is_equilibrium_point (tilt_eqn alpha1 gamma)) 0 D.
Proof.
rewrite /is_equilibrium_point /is_sol inE => -[inD0 deriv tilt].
rewrite inE; split.
exact/set_mem.
by [].
by [].
Qed.

Lemma equilibrium_zero_stable (openD : open D) (D0 : 0 \in D)
    (D_in_state : D `<=` state_space_tilt) :
  equilibrium_is_stable_at D point1 (sol 0).
Proof.
apply: (@Lyapunov_stability K 5 D (tilt_eqn alpha1 gamma)
  sol openD solP _ (V1 alpha1 gamma)).
- assumption.
- move => z zD t t0.
  apply: V1_dot_le0.
  + by [].
  + by [].
  + apply: (is_sol_subset D_in_state).
    by apply solP; rewrite sol0.
  + move => t1.
    rewrite -derivable1_diffP.
    have : is_sol (tilt_eqn alpha1 gamma) (sol z) D.
      by apply solP; rewrite sol0.
    by case.
  + by [].
- move=> t.
  rewrite /V1.
  apply/differentiableD => //.
    apply/differentiableM => //.
    exact/differentiable_norm_squared/differentiable_lsubmx.
  apply/differentiableM => //.
  exact/differentiable_norm_squared/differentiable_rsubmx.
- have := V1_is_Lyapunov_candidate alpha1_gt0 gamma_gt0.
  move => Hpos.
  rewrite /is_Lyapunov_candidate in Hpos *.
  rewrite /point1 in Hpos.
  rewrite /locposdef.
  rewrite -y00 => //.
  rewrite /V1 y00.
  rewrite lsubmx_const rsubmx_const //=.
  split => //.
  split.
    by rewrite !expr2 !norm0 !mulr0 !mul0r add0r.
  move => z zin z_neq0.
  rewrite /locposdef in Hpos.
  case : Hpos => //.
  move => _.
  move => [_ Hpos].
  apply: Hpos => //.
  by rewrite inE.
- apply: is_equilibrium_subset.
  exact: equilibrium_point1.
Qed.

End equilibrium_zero_stable.
