From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals order.
From mathcomp Require Import topology normedtype landau derive realfun.
From mathcomp Require Import matrix_normedtype.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.

(**md**************************************************************************)
(* # Tentative formalization of [1]                                           *)
(*                                                                            *)
(* ```                                                                        *)
(*                  posdefmx M == M is definite positive                      *)
(*               locposdef V x == V is locally positive definite at x         *)
(*     is_Lyapunov_candidate V := locposdef V                                 *)
(*           locnegsemidef V x == V is locally negative semidefinite          *)
(*              'D~(sol, x0) V == derivative of V along the solution sol      *)
(*                                starting at x0                              *)
(*                  is_sol f y == the function y satisfies y' = phi y         *)
(*    is_equilibrium_point f p := solves_equation f (cst p)                   *)
(*               state_space f == the set points attainable by a solution     *)
(*                                (in the sense of `is_sol`)                  *)
(*  is_Lyapunov_stable_at f V x == Lyapunov stability                         *)
(* ```                                                                        *)
(*                                                                            *)
(* Reference:                                                                 *)
(* - [benallegue2023itac]                                                     *)
(* https://hal.science/hal-04271257v1/file/benallegue2019tac_October_2022.pdf *)
(* - [2]: Hassan K. Khalil, Nonlinear systems, 2002*)
(******************************************************************************)

Reserved Notation "''D~(' sol , x ) f" (at level 10, sol, x, f at next level,
  format "''D~(' sol ,  x )  f").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

(* additions to MathComp-Analysis *)


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

Lemma closed_ballAE {K : realType} n (e : K) (x : 'rV[K]_n) :
  0 < e -> closed_ball x e = closed_ball_ (@mx_norm _ _ _) x e.
Proof.
by move=> e0; rewrite closed_ballE.
Qed.

Import Order.Def.

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

Local Open Scope classical_set_scope.
(* NB: we are just mimicking the proofs for the real line already available in derive.v *)
Lemma EVT_max_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
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

Lemma EVT_min_rV (R : realType) n (f : 'rV[R]_n -> R) (A : set 'rV[R]_n) :
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

(* TODO: rm with MCA 1.15.0 *)
Definition Jacobian n m (R : numFieldType) (f : 'rV[R]_n -> 'rV[R]_m) p :=
  lin1_mx ('d f p).

Section gradient.

Definition jacobian1 {R : numFieldType} n (f : 'rV[R]_n -> R)
    : 'rV_n -> 'cV_n :=
  Jacobian (scalar_mx \o f).

(* NB: not used*)
Definition partial {R : realType} {n : nat} (f : 'rV[R]_n -> R) (a : 'rV[R]_n) i :=
  lim (h^-1 * (f (a + h *: 'e_i) - f a) @[h --> 0^'])%classic.

Lemma partial_diff {R : realType} n (f : 'rV[R]_n -> R)  (a : 'rV[R]_n)
    (i : 'I_n) :
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
Definition err_vec {R : pzRingType} n (i : 'I_n) : 'rV[R]_n :=
  \row_(j < n) (i == j)%:R.

Lemma err_vecE {R : pzRingType} n (i : 'I_n) :
  err_vec i = 'e_i :> 'rV[R]_n.
Proof.
apply/rowP => j.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Definition gradient_partial {R : realType} n (f : 'rV[R]_n -> R) (a : 'rV[R]_n) :=
  \row_(i < n) partial f a i.

Lemma gradient_partial_sum {R : realType} n (f : 'rV[R]_n -> R) (a : 'rV[R]_n) :
  gradient_partial f a = \sum_(i < n) partial f a i *: 'e_i.
Proof.
rewrite /gradient_partial [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

(* TODO: generalize with MCA 1.15.0 *)
Lemma gradient_partial_jacobian1 {R : realType} n (f : 'rV[R]_n -> R)
    (v : 'rV[R]_n) : differentiable f v ->
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

(* spin and matrix/norm properties*)

Lemma norm_spin {R : rcfType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
  (u *m \S(v - u) ^+ 2 *m (u)^T) 0 0 = - `|u *m \S(v)|_e ^+ 2.
Proof.
rewrite spinD spinN -tr_spin mulmxA !mulmxDr mulmxDl !mul_tr_spin !addr0.
rewrite -dotmulvv /dotmul trmx_mul.
rewrite mxE [X in _ + X = _](_ : _ = 0) ?addr0; last first.
  by rewrite tr_spin -mulmxA mulNmx spin_mul_tr mulmxN mulmx0 oppr0 mxE.
by rewrite tr_spin mulNmx mulmxN [in RHS]mxE opprK mulmxA.
Qed.

Lemma sqr_spin {R : realType} (u : 'rV[R]_3) (norm_u1 : `|u|_e = 1) :
  \S(u) *m \S(u) = u^T *m u - 1%:M.
Proof.
have sqrspin : \S(u) ^+ 2 = u^T *m u - (`|u|_e ^+ 2)%:A by rewrite sqr_spin.
rewrite expr2 norm_u1 expr2 mulr1 in sqrspin.
rewrite mulmxE sqrspin.
  apply/matrixP => i j ; rewrite mxE /= [in RHS]mxE /=.
  congr (_+_); rewrite mxE mxE /= mul1r.
  by rewrite [in RHS]mxE [in RHS]mxE /= -mulNrn mxE -mulNrn.
Qed.

Section posdefmx.

Definition posdefmx {K : realType} m (M : 'M[K]_m) : Prop :=
  M \is sym m K /\ forall a, eigenvalue M a -> a > 0.

Lemma posdefmxP_direct {R : realType} m (M : 'M[R]_m) :
  posdefmx M -> (forall v : 'rV[R]_m, v != 0 -> (v *m M *m v^T) 0 0 > 0).
Proof.
Abort.

Lemma posdefmxP_converse {R : realType} m (M : 'M[R]_m) :
  (forall v : 'rV[R]_m, v != 0 -> (v *m M *m v^T) 0 0 > 0) -> posdefmx M.
Proof.
Abort.

End posdefmx.

Local Open Scope classical_set_scope.

Section locdef.
Context {R : realType} {T : normedModType R}.
Implicit Types V : T -> R.

Definition is_Lyapunov_candidate V (D : set T) (x : T) :=
  x \in D /\ V x = 0 /\ forall z, z \in D -> z != x -> V z > 0.

(* TODO: useful? mettre dans un fichier wip.v? *)
Definition locnegdef V (x : T) := V x = 0 /\ \forall z \near x^', V z < 0.

(* TODO: useful? mettre dans un fichier wip.v? *)
(* locally negative semidefinite *)
Definition locnegsemidef V (x : T) := V x = 0 /\ \forall z \near x^', V z <= 0.

End locdef.

(* derivation along the trajectory h *)
Definition derive_along {R : realType} {n : nat}
    (V : 'rV[R]_n -> R) (f : R -> 'rV[R]_n)
    (t : R) : R :=
  (jacobian1 V (f t))^T *d 'D_1 f t.

Notation "''D~(' sol ) f" := (derive_along f (sol)).

Section derive_along.
Context {R : realType} {n : nat}.
Variable sol : R -> 'rV[R]_n.
(* sol represents the solutions of a differential equation *)

Lemma derive_along_derive (V : 'rV[R]_n -> R) (t : R) :
  differentiable V (sol t) -> differentiable (sol) t ->
  'D~(sol) V t = 'D_1 (V \o sol) t.
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

Lemma derive_alongMl (f : 'rV_n -> R) (k : R) t :
  differentiable f (sol t) -> differentiable (sol) t ->
  'D~(sol) (k *: f) t = k *: 'D~(sol) f t.
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

Lemma derive_alongD (f g : 'rV_n -> R) t :
  differentiable f (sol t) -> differentiable g (sol t) ->
  differentiable (sol) t ->
  'D~(sol) (f + g) t  = 'D~(sol) f t + 'D~(sol) g t.
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

Lemma derivative_derive_along_eq0 (f : 'rV_n -> R) (t : R) :
  differentiable f (sol t) ->
  'D_1 (sol) t = 0 -> 'D~(sol) f t = 0.
Proof.
move=> xt1 dtraj.
rewrite /derive_along /jacobian1 /dotmul dotmulP /dotmul -trmx_mul.
by rewrite dtraj mul0mx !mxE.
Qed.

Lemma derive_along_enorm_squared m (f : 'rV[R]_n -> 'rV_m)
  (t : R) :
  differentiable f (sol t) ->
  differentiable (sol) t ->
  'D~(sol) (fun y => `|f y|_e ^+ 2) t =
  (2 *: 'D_1 (f \o sol) t *m (f (sol t))^T) 0 0.
Proof.
move=> difff diffphi.
rewrite derive_along_derive => //=; last exact: differentiable_enorm_squared.
rewrite fctE derive_enorm_squared //=; last first.
  by apply: diff_derivable=> //=; exact: differentiable_comp.
by rewrite mulrDl mul1r scalerDl scale1r mulmxDl [in RHS]mxE.
Qed.

End derive_along.

(* NB: not used, can be shown to be equivalent to derive_along *)
Definition derive_along_partial {R : realType} n (V : 'rV[R]_n -> R)
    (a : R -> 'rV[R]_n) (t : R) : R :=
  \sum_(i < n) (partial V (a t) i * ('D_1 a t) ``_ i).

From mathcomp Require Import sequences.

Section picard.
Context {R : realType} {n : nat}.
Notation U := ('rV[R]_n).
Variable u0 : U.
Variable phi : U -> U.

Variable (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Definition is_sol_autonomous (t0 t1 : R) (f : R -> U) :=
  f t0 = u0 /\
  {in `]t0, t1[, forall x, derivable f x 1 /\ f^`() x = phi (f x)} /\
  {within `[t0, t1], continuous f} /\
  {in `[t0, t1], forall t, closed_ball u0 r%:num (f t)}.

Variables (k : R) .
Hypothesis k0 : 0 < k.
Hypothesis lip2 : k.-lipschitz_B phi.

Theorem picard_lindeloeff_autonomous t0 :
  exists sol delta,
  delta > 0 /\ is_sol_autonomous t0 (t0 + delta) sol.
Admitted.

End picard.

Section ode.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.

Variable phi : T -> T.

Definition is_sol (Init : set T) (Delta : K) (r : {posnum K}) (f : K -> T) :=
   f 0 \in Init /\ is_sol_autonomous (f 0) phi r 0 Delta f.

End ode.

Section is_sol.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.
Variable phi : T -> T.
Variable r : {posnum K}.
Variable Delta : K.

Lemma is_sol_subset y0 (A B : set T) (AB : A `<=` B) :
  is_sol phi A Delta r y0 -> is_sol phi B Delta r y0.
Proof.
rewrite /is_sol inE => -[inD0 [_ [deri [cont cball]]]]; rewrite inE.
split => //.
by apply: AB.
Qed.

End is_sol.

Section state_space.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.
Variable phi : T -> T.
Variable r : {posnum K}.

Definition state_space (Init : set T) (Delta : K) : set T:=
  [set x | exists f, (is_sol phi Init Delta r f /\ (exists t, t \in `]0, Delta[%R /\ x = f t))].

End state_space.

Section equilibrium_point.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.
Variable phi : T -> T.  (* was (K -> T) -> K -> T *)
Variable r : {posnum K}.
Variable Init : set T.
Variable Delta : K.

Definition is_equilibrium_point (x : T) := is_sol phi Init Delta r (cst x).

End equilibrium_point.

Section equilibrium_point.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.
Variable phi : T -> T.
Variable r : {posnum K}.
Variable Delta : K.

Lemma is_equilibrium_point_subset x (A B : set T) (AB : A `<=` B) :
  is_equilibrium_point phi r A Delta x -> is_equilibrium_point phi r B Delta x.
Proof.
rewrite /is_equilibrium_point /is_sol inE => -[inD0 [deriv [cont tilt]]].
rewrite inE; split => //.
exact: AB.
Qed.

Definition equilibrium_points Init :=
  [set p : T | is_equilibrium_point phi r Init Delta p ].

End equilibrium_point.

Section stability.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.

Definition is_stable_at (x : T) (z : K -> 'rV[K]_n) :=
  forall eps, eps > 0 -> exists2 d, d > 0 &
    `| z 0 - x | < d -> forall t, t >= 0 -> `| z t - x | < eps.

Definition is_locally_stable_at (x : T) (Delta : K) (z : K -> 'rV[K]_n) :=
  forall eps, eps > 0 -> exists2 d, d > 0 &
    `| z 0 - x | < d -> forall t, 0 <= t < Delta -> `| z t - x | < eps.

Definition is_asymptotically_stable_at (x : T) (z : K -> 'rV[K]_n) : Prop :=
  exists2 d, d > 0 & `| z 0 - x | < d -> z t @[t --> +oo] --> x.

End stability.

(* f' = phi f *)
(* phi_robot f =def= fun f t => phi t (f t) *)
(*Definition existence_uniqueness {K : realType} {n}
  (phi : K -> 'rV[K]_n -> 'rV[K]_n) (Init : set 'rV[K]_n) Delta
  (sol : K -> 'rV[K]_n) :=
  forall y, y 0 \in Init -> is_sol phi Init Delta y <-> sol (y 0) = y.
*)

Definition initial_condition {K : realType} {n} (sol : K -> 'rV[K]_n) x0 :=
  sol 0 = x0.

(*Section solutions_unique.
Context {K : realType} {n : nat}.
Variable phi : K -> 'rV[K]_n -> 'rV[K]_n.
Variable Init : set 'rV[K]_n.
Variable Delta : K.

Definition solutions_unique := forall (f g : K -> 'rV_n) (x0 : 'rV_n),
  is_sol phi Init Delta f ->
  is_sol phi Init Delta g ->
  f 0 = x0 -> g 0 = x0 ->
  f = g.

End solutions_unique.

Section solutions_unique_lemmas.
Context {K : realType} {n : nat}.
Variables (phi : K -> 'rV[K]_n -> 'rV[K]_n) (Init : set 'rV[K]_n).
Variable Delta : K.

Lemma existence_uniqueness_unique (sol : 'rV[K]_n -> K -> 'rV[K]_n) :
  existence_uniqueness phi Init Delta sol ->
  solutions_unique phi Init Delta.
Proof.
move=> solP f g x0 solf solg f0 g0.
apply/funext => x.
case : (solf) => //=.
move => a0D Da fa.
have := solP _ a0D.
case.
move => /(_ solf).
move => a0a _.
case : (solg) => //=.
move => b0D Db fb.
have := solP _ b0D.
case.
move => /(_ solg).
move => b0b _.
by rewrite -b0b -a0a f0 g0.
Qed.

Lemma existence_uniqueness_exists (sol : K -> 'rV[K]_n) :
  existence_uniqueness phi Init Delta sol -> forall p, p \in Init ->
  initial_condition sol p -> is_sol phi Init Delta (sol p).
Proof.
move=> solP sol0 p pD.
have H := solP (sol p).
apply H.
  by rewrite sol0.
by rewrite sol0.
Qed.

End solutions_unique_lemmas.*)

Section sphere.
Context {K : realType} {n : nat}.

Definition sphere r := [set x : 'rV[K]_n | `|x| = r].

Lemma sphere_nonempty r : n != 0 -> 0 < r -> sphere r !=set0.
Proof.
move=> n0.
move=> r_gt0.
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
pose d := fun x : 'rV[K]_n  => `|x| : K.
have contd : continuous d by move=> /= z; exact: norm_continuous.
rewrite [X in closed X](_ : _ = d @^-1` [set r]); last first.
  by apply/seteqP; split.
by apply continuous_closedP.
Unshelve. all: by end_near. Qed.

End sphere.

(* TODO: generalize  within_continuous_comp_norm *)
Lemma within_continuous_comp {R : realType} {K : numDomainType}
  {U : pseudoMetricNormedZmodType K} a y (g : U -> R) (f : R -> U) :
  a <= y ->
  {in f @` `[a, y], continuous g} ->
  {within `[a, y], continuous (fun x => f x)} ->
  {within `[a, y], continuous fun x => (g \o f) x}.
Proof.
rewrite le_eqVlt => /predU1P[<-|ay].
  rewrite set_itv1 => _ _.
  exact: continuous_subspace1.
move=> cg.
move/(continuous_within_itvP f ay) => -[H1 H2 H3].
apply/continuous_within_itvP => //; split => //.
- move=> z zay.
  apply: continuous_comp => //.
    by apply: H1.
  apply: cg.
  rewrite inE/=.
  exists z => //.
  by apply: subset_itv_oo_cc zay.
- apply: (cvg_comp f g).
    by apply: H2.
  apply: cg.
  rewrite inE/=.
  exists a => //.
  by rewrite in_itv/= lexx/= ltW.
- apply: (cvg_comp f g).
    by apply: H3.
  apply: cg.
  rewrite inE/=.
  exists y => //.
  by rewrite in_itv/= lexx/= ltW.
Qed.

Section Lyapunov_stability.
Context {K : realType} {n : nat}.
Let U := 'rV[K]_n.+1.
Variable phi : U -> U.
Variable Init : set U.
Variable Delta : K.
Variable sol : U -> K -> U.
Let u0 : U := 0.
Hypothesis Initu0 : u0 \in Init.
Variable r' : {posnum K}.
Hypothesis solP : is_sol_autonomous u0 phi r' 0 Delta (sol u0).

Hypothesis openD : open Init. (* D est forcement un ouvert *)
(* see Cohen Rouhling ITP 2017 Sect 3.2 *)

Let B r := closed_ball_ (fun x => `|x|) (0 : 'rV[K]_n.+1) r.

Let BE s : 0 < s -> B s = closed_ball 0 s.
Proof. by move=> r0; rewrite /B -closed_ballE. Qed.

Variable V : U -> K.
Hypothesis Vdiff : forall t : U, differentiable V t.
Hypothesis V'_le0 : forall x, x \in Init ->
  forall t, t >= 0 -> 'D~(sol x) V t <= 0.

Let V_nincr a b : b < Delta -> 0 <= a <= b ->
  forall x, x \in Init -> is_sol phi Init Delta r' (sol x) ->
  V (sol x b) <= V (sol x a).
Proof.
move=> bDelta /andP[a_ge0 ab] x /set_mem xD solP'.
apply: (@ler0_derive1_le_cc _ (V \o sol x) 0 b) => //=.
- move=> y yb.
  apply/diff_derivable/differentiable_comp; last exact: differentiable_comp.
  rewrite -derivable1_diffP.
  case: solP' => /= h0Init [_ [+ _]].
  move/(_ y) /(_ _) => [].
    move: yb.
    rewrite inE/=.
    apply: subset_itvl.
    by rewrite bnd_simp ltW.
  by [].
- move=> y yb.
  rewrite derive1E -derive_along_derive//.
  + apply: (V'_le0 (x := x)).
      exact/mem_set.
    by move : yb; rewrite in_itv/= => /andP[/ltW].
  + rewrite -derivable1_diffP.
    case: solP' => /= h0Init [_ [+ _]].
    move/(_ y) /(_ _) => [].
      move: yb.
      rewrite inE/=.
      apply: subset_itvl.
      by rewrite bnd_simp ltW.
    by [].
- (* `[0, b] *)
  have [b0|] := ltP 0 b; last first.
    move=> b0.
    have ? : b = 0.
      by apply/eqP; rewrite eq_le b0 (le_trans a_ge0)//.
    subst b.
    rewrite set_itv1.
    exact: continuous_subspace1.
  apply/continuous_within_itvP => //; split.
  + move=> z z0b.
    apply: continuous_comp; last exact: differentiable_continuous.
    apply: differentiable_continuous => //.
    rewrite -derivable1_diffP.
    case: solP' => /= h0Init [_ [+ _]].
    move/(_ z) /(_ _) => [].
      move: z0b.
      rewrite inE/=.
      apply: subset_itvl.
      by rewrite bnd_simp ltW.
    by [].
  + case: solP' => solu0u0 [_ [deri [cont _]]].
    (* filled this *)
    apply: cvg_comp.
    have d0 : 0 < Delta.
      by apply /lt_trans/bDelta.
    have /continuous_within_itvP := cont.
    move/(_ d0) => [_ + _].
    apply.
    apply (differentiable_continuous (Vdiff (sol x 0))).
  + apply: cvg_at_left_filter.
    apply: differentiable_continuous => //.
    apply: differentiable_comp.
      rewrite -derivable1_diffP.
      case: solP' => /= h0Init [_ [+ _]].
      move/(_ b) /(_ _) => [].
        by rewrite inE/= in_itv/= b0 bDelta.
      by [].
    by apply: Vdiff.
- by rewrite !in_itv/= lexx (le_trans a_ge0).
- by rewrite in_itv/= ab andbT.
Qed.

(* khalil theorem 4.1 *)
Theorem Lyapunov_stability (x : 'rV[K]_n.+1 := 0) :
  is_Lyapunov_candidate V Init x ->
  is_equilibrium_point phi r' Init Delta x ->
  is_locally_stable_at x Delta (sol x).
Proof.
move=> VDx eq /= eps eps0/=.
move: VDx => [/= xD [Vx0 DxV]].
have [r [r_gt0 [r_eps BrD]]] : exists2 r : K, 0 < r & r <= eps /\ B r `<=` Init.
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
    by apply/differentiable_continuous; exact/Vdiff.
  move/(EVT_min_rV (sphere_nonempty _ r_gt0) (@compact_sphere _ _ r)).
  have m0 : n.+1 != 0 by [].
  move=> /(_ m0).
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
have Df_Omega_beta :
    sol x 0 \in Omega_beta -> forall t, 0 <= t < Delta -> sol x t \in Omega_beta.
  move=> phi_Omega.
  have /= V_nincr_consequence : forall t, 0 <= t < Delta -> forall u, 0 <= u <= t ->
      'D~(sol x) V u <= 0 ->
      V (sol x t) <= V (sol x 0) <= beta.
    move=> /= t1 /andP[t10 t1Delta] u ut1 Vle0.
    apply/andP; split.
      move : phi_Omega; rewrite inE /Omega_beta/= => -[Brphi0 Vphi0beta].
      apply: V_nincr.
        assumption.
      by rewrite lexx t10.
      assumption.
    split.
      apply/mem_set.
      by apply: BrD.
    move: solP.
    by case: solP => ->.
    by move: phi_Omega; rewrite inE => -[Brh0 Vh0beta].
  move=> t /andP[t0 tDelta].
  rewrite inE; split; last first.
    have : 'D~(sol x) V t <= 0.
      by apply: V'_le0 => //; case: sol_phi.
    have := @V_nincr_consequence t.
    rewrite t0 /= tDelta => /(_ isT t).
    rewrite lexx t0/= => /(_ isT).
    move=> /[apply].
    by move=> /andP[/le_trans] => /[apply].
  move: phi_Omega; rewrite inE /Omega_beta/= /B /closed_ball_/=.
  rewrite !sub0r !normrN => -[phi0r Vphi0beta].
  rewrite leNgt; apply/negP => phi_t_r.
  have [t1 [/andP[t1_ge0 t1t] phit1r]] : exists t0, 0 <= t0 <= t/\ `|sol x t0| = r.
    have norm_phi_cont : {within `[0, t]%classic, continuous (normr \o sol x)}.
      (* `[0, t] *)
      apply/(@within_continuous_comp _ _ _ _ _ (@normr _ _) (sol x)) => //.
        move=> z _.
        by apply: norm_continuous.
      case: solP => _ [_ [+ _]].
      apply: continuous_subspaceW.
      apply: subset_itvl.
      by rewrite bnd_simp ltW.
    have : min `|sol x 0| `|sol x t| <= r <= max `|sol x 0| `|sol x t|.
      by rewrite ge_min phi0r/= le_max (ltW phi_t_r) orbT.
    move=> /(IVT t0 norm_phi_cont)[c cI norm_phi_c].
    by exists c; split => //; move/itvP: cI => ->.
  have alphaVphit1 : alpha <= V (sol x t1).
    rewrite {alpha_gt0 beta_alpha} /alpha; case: alpha_min => /=.
    by move=> y [_ +]; apply; rewrite inE.
  have : beta < V (sol x t1).
    by rewrite (lt_le_trans _ alphaVphit1)//; case/andP : beta_alpha.
  apply/negP; rewrite -leNgt.
  have := @V_nincr_consequence t1.
  rewrite t1_ge0 (le_lt_trans t1t tDelta) => /(_ isT).
  move=> /(_ t1).
  rewrite t1_ge0 lexx => /(_ isT).
  have : 'D~(sol x) V t1 <= 0 by apply: V'_le0 => //; case: sol_phi.
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
    rewrite [X in closed X](_ : _ = V @^-1` [set x | x <= beta]); last first.
      by apply/seteqP; split.
    apply: closed_comp => //= v _.
    apply: continuous_comp; first by [].
    exact: differentiable_continuous.
have [d0 d0_gt0 Vbeta] : exists2 d, d > 0 & forall x, `|x| <= d -> V x < beta.
  have [d d_gt0 xdV] : exists2 d : K, 0 < d &
      forall y, `|y - x| < d -> `|V y - V x| < beta.
    have /cvgrPdist_lt /(_ _ beta_gt0) : V x @[x --> nbhs x] --> V x.
      exact/differentiable_continuous/Vdiff.
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
Lemma fact217 (v : 'rV[K]_3): \S(v) ^+ 3 = - (`|v|_e ^+2) *: \S(v).
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

(* Modelization of the physical problem *)
Section ya.
(* mesure de l'accelerometre *)
Variable K : realType.
Variable R : K -> 'M[K]_3. (* L/W *)
Variable g0 : K. (*standard gravity constant*)
Let w t := ang_vel R t. (* local frame of the sensor (gyroscope) *)
Definition x2 t : 'rV_3 := 'e_2 *m R t.
Definition y_a x t := - x t *m \S(w t) + 'D_1 x t + g0 *: x2 t. (* world frame *)
Variable p : K -> 'rV[K]_3.
Let v := fun t : K => 'D_1 p t *m R t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.

Lemma y_aE t (derivableR : forall t, derivable R t 1)
    (derivablep : forall t, derivable p t 1)
    (derivableDp : forall t, derivable ('D_1 p) t 1) :
  ('D_1 ('D_1 p) t + g0 *: 'e_2) *m R t = y_a v t.
Proof.
rewrite mulmxDl.
rewrite /y_a/= /= /x2.
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

Definition S2 {K : realType} := [set x : 'rV[K]_3 | `|x|_e = 1].

(* section III.A of [benallegue2023itac] *)
Section state_dynamics.
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
by rewrite /S2 /x2 inE/= orth_preserves_norm ?enormeE ?rotation_sub.
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
rewrite -derive1mx_ang_vel; last first.
  admit.
by [].
Abort.

(* eqn (10/11): we write x_1 * S(w) whereas it is - S(w) * x_1 in [benallegue2023itac] *)
Notation y_a := (y_a R g0).
Lemma derive_x1 t : 'D_1 x1 t = x1 t *m \S(w t) + y_a x1 t - g0 *: x2 t.
Proof.
rewrite /y_a/= -addrA addrK.
rewrite /x1.
rewrite addrCA addrA mulNmx /= /w.
by rewrite (addrC(-_)) subrr add0r.
Qed.

 (* eqn (11b): x_2 * S(w) instead of - S(w) * x_2 in [benallegue2023itac] *)
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
rewrite derive1mx_ang_vel /=; last first.
  by move=> ?; rewrite rotation_sub.
by rewrite mulmxA.
Qed.

End state_dynamics.

(* section III.A in [benallegue2023itac] *)
Section two_steps_first_order_estimator.
Context {K : realType}.
Variables gamma alpha1 : K.
Variable v : K -> 'rV[K]_3.
Variable R : K -> 'M[K]_3.
Hypothesis derivableR : forall t, derivable R t 1.
Let w t := ang_vel R t.
Variable x1_hat : K -> 'rV[K]_3.
Hypothesis derivable_x1_hat : forall t, derivable x1_hat t 1.
Variable x2_hat : K -> 'rV[K]_3.
Variable g0 : K.
Hypotheses g0_eq0 : g0 != 0.
Notation y_a := (y_a R g0 v).
Let x1 t := v t.
Let x2'_hat t := - (alpha1 / g0) *: (x1 t - x1_hat t). (* eqn (12b) *)
(* we write x^_1 * S(w) instead - S(w) * x^_1 in [benallegue2023itac] *)
Hypothesis eqn12a : forall t,
  'D_1 x1_hat t = x1_hat t *m \S(w t) + y_a t - g0 *: x2'_hat t. (* eqn (12a) *)
(* we write x^_2 * S(...) instead of - S(...) * x^_2
   and + gamma instead of - gamma in [benallegue2023itac] *)
Hypothesis eqn12c : forall t,
  'D_1 x2_hat t = x2_hat t *m \S(w t + gamma *: x2'_hat t *m \S(x2_hat t)). (* eqn (12c) *)
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
Hypothesis norm_x2_hat : forall t, `|x2_hat t|_e = 1.

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

(* eqn (13a) *)
(* we write p_1 * S(w) instead of - S(w) * p1 in [benallegue2023itac] *)
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
    congr (_ + _ *: _).
    rewrite -2![in LHS]addrA -[in RHS]addrA.
    congr +%R.
    rewrite opprD [in LHS]addrCA.
    rewrite opprK.
    rewrite [in RHS]opprB.
    rewrite [in RHS]addrCA [in RHS]addrC.
    rewrite -[in RHS]addrA.
    congr +%R.
    rewrite opprD.
    rewrite [LHS]addrA.
    rewrite (addrC (y_a t)).
    by rewrite subrK.
  rewrite (_ : x1 t *m \S(w t) - g0 *: x2 t -
                 (x1_hat t *m \S(w t) - g0 *: x2'_hat t) =
               (x1 t - x1_hat t) *m \S(w t) -
                 g0 *: (x2 t - x2'_hat t)); last first.
    rewrite mulmxBl scalerDr scalerN opprB addrA [LHS]addrC 2!addrA.
    rewrite -addrA; congr +%R.
      by rewrite addrC.
    by rewrite opprB addrC.
  rewrite -/(error1 t).
  rewrite scalerDr addrA scalemxAl -mulmxDl scalerN scalerA.
  by rewrite divfK.
by rewrite error1E.
Qed.

(* eqn (13b) *)
(* we write x~_2 * S(w) instead of - S(w) * x~_2 in [benallegue2023itac] *)
Lemma derive_error2 t :
  'D_1 error2 t = error2 t *m \S(w t) +
                  gamma *: (error2 t - error1 t) *m \S(x2_hat t) ^+ 2.
Proof.
rewrite /error2.
rewrite [in LHS]deriveB//.
rewrite derive_x2//.
rewrite -/(x2 t) -/(w t) -/(error2 t).
rewrite eqn12c.
rewrite spinD.
rewrite -[in LHS]scalemxAl.
rewrite (spinZ gamma).
rewrite mulmxDr opprD [LHS]addrA.
rewrite [in LHS]addrC addrA (addrC _ (x2 t *m \S(w t))).
rewrite addrAC.
rewrite -mulmxBl -/(error2 t).
simpl in *.
rewrite -[in RHS]opprB.
rewrite scalerN mulNmx.
congr (_ - _).
rewrite -scalemxAr -[RHS]scalemxAl.
congr (_ *: _).
rewrite /error2 /error1.
rewrite opprB addrCA.
rewrite (addrC (x2 t)) addrK.
rewrite mulmxBl.
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

Lemma x2_hatR t : x2_hat t *m (R t)^T = 'e_2 - error2_p t.
Proof.
rewrite /error2_p /error2 mulmxBl opprB addrCA.
rewrite [X in _ + X](_ : _ = 0) ?addr0//.
rewrite /x2 -mulmxA.
by rewrite orthogonal_mul_tr ?rotation_sub// mulmx1 subrr.
Qed.

(* eqn (14a) *)
Lemma derive_error1_p t : 'D_1 error1_p t = - alpha1 *: error1_p t.
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

Definition eqn14b_rhs x1 x2 := gamma *: (x2 - x1) *m \S('e_2 - x2) ^+ 2.

(* eqn (14b) *)
Lemma derive_error2_p t : 'D_1 error2_p t = eqn14b_rhs (error1_p t) (error2_p t).
Proof.
rewrite /eqn14b_rhs.
rewrite [LHS]derive_mulmx//=; last by rewrite derivable_trmx.
simpl in *.
rewrite derive_trmx//.
rewrite derive1mx_ang_vel//=; last by move=> ?; rewrite rotation_sub.
rewrite !ang_vel_mxE//; last by move=> ?; rewrite rotation_sub.
rewrite trmx_mul mulmxA -mulmxDl.
rewrite derive_error2 /=.
rewrite -/(w t) tr_spin mulmxN.
rewrite -!addrA addrC addrA subrK.
rewrite -scalemxAl.
rewrite -!scalemxAl.
congr (_ *: _).
rewrite -x2_hatR.
rewrite -spin_similarity ?rotationV//.
rewrite trmxK.
rewrite [in RHS]expr2 -mulmxE !mulmxA.
rewrite -!mulNmx opprB.
congr (_ *m _ *m _).
rewrite -[in RHS]mulmxA.
rewrite orthogonal_tr_mul ?rotation_sub// mulmx1.
congr (_ *m _).
rewrite -/(error2 _).
rewrite error2E.
rewrite mulmxDl.
congr (_ + _)%R.
by rewrite /error1 -mulmxA orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

End two_steps_first_order_estimator.

Definition state_space_tilt {K : realType} :=
  [set x : 'rV[K]_6 | `|'e_2 - Right x|_e = 1].

Lemma cst_oo_cc {R : realType} (f : R -> R) y (a b : R) :
  y \in `[a, b] ->
  {within `[a, b], continuous f} ->
  {in `]a, b[, f =1 cst (f y)} ->
  {in `[a, b], f =1 cst (f y)}.
Proof.
have [ab|ba] := ltP a b; last first.
  move=> yab _ H x.
  rewrite inE/= in_itv/= => /andP[ax xb].
  have /eqP ? : a == x by rewrite eq_le ax (le_trans xb _).
  subst x.
  move: yab; rewrite inE/= in_itv/= => /andP[ay yb].
  have /eqP ? : a == y by rewrite eq_le ay (le_trans yb _).
  by subst.
move=> yab cf H x.
rewrite inE/= in_itv/= => /andP[].
rewrite le_eqVlt => /predU1P[<-{x} _|].
  move: yab; rewrite inE/= in_itv/= => /andP[].
  rewrite le_eqVlt => /predU1P[->//|ay yb].
  move/continuous_within_itvP : cf => /(_ ab)[_ fafa _].
  move/cvgrPdist_le in fafa.
  rewrite /= in fafa.
  apply/eqP.
  rewrite -subr_eq0.
  rewrite -normr_le0.
  apply/ler_addgt0Pr => /= e e0.
  rewrite add0r.
  have := fafa _ e0 => -[d /= d0] H'.
  near a^'+ => a0.
  rewrite (_ : f y = f a0)//; last first.
    apply/esym/H.
    rewrite inE/= in_itv/=.
    by apply/andP; split => //.
  apply: H' => //=.
  rewrite ltr0_norm ?subr_lt0// opprB.
  rewrite ltrBlDl.
  near: a0.
  apply: nbhs_right_lt.
  by rewrite ltrDl.
move=> ax.
rewrite le_eqVlt => /predU1P[->|]; last first.
  move=> xb.
  apply: H => //.
  by rewrite inE/= in_itv/= ax.
clear x ax.
move: yab.
rewrite inE/= in_itv/= => /andP[ay].
rewrite le_eqVlt => /predU1P[<-//|yb].
move/continuous_within_itvP : cf => /(_ ab)[_ _ fbfb].
move/cvgrPdist_le in fbfb.
rewrite /= in fbfb.
apply/eqP.
rewrite -subr_eq0.
rewrite -normr_le0.
apply/ler_addgt0Pr => /= e e0.
rewrite add0r.
have := fbfb _ e0 => -[d /= d0] H'.
near b^'- => b0.
rewrite (_ : f y = f b0)//; last first.
  apply/esym/H.
  rewrite inE/= in_itv/=.
  by apply/andP; split => //.
apply: H' => //=.
rewrite distrC.
rewrite ltr0_norm ?subr_lt0// opprB.
rewrite ltrBlDr.
rewrite -ltrBlDl.
near: b0.
apply: nbhs_left_gt.
by rewrite ltrBlDl ltrDr.
Unshelve. all: by end_near. Qed.

Lemma is_derive_0_is_cst_new {R : realType} (f : R -> R) y (a b : R) :
  y \in `]a, b[ ->
  {within `[a, b], continuous f} ->
  (forall x, x \in `]a, b[ -> is_derive x (1 : R) f 0) -> {in `[a, b], f =1 cst (f y)}.
Proof.
move=> yab cf Hd.
apply: cst_oo_cc => //.
  move: yab.
  rewrite !inE/=.
  by apply: subset_itv_oo_cc.
move=> x xab.
wlog xLy : x y xab yab/ x <= y.
  move=> H; case: (leP x y) => [/H |/ltW xy].
  exact.
  by apply/esym/H => //.
rewrite -(subKr (f y) (f x)).
have [| |] := @MVT_segment R f 0 _ _ xLy.
- move=> z zxy.
  apply: Hd.
  move: zxy.
  rewrite inE/=.
  apply: subset_itvSoo; rewrite bnd_simp.
  by move: xab; rewrite inE/= in_itv/= => /andP[/ltW].
  by move: yab; rewrite inE/= in_itv/= => /andP[_ /ltW].
- apply: continuous_subspaceW(* NB: should be , do a PRS*) cf.
  apply: subset_itvScc; rewrite bnd_simp.
  by move: xab; rewrite inE/= in_itv/= => /andP[/ltW].
  by move: yab; rewrite inE/= in_itv/= => /andP[_ /ltW].
move=> r rxy.
rewrite mul0r => ->.
by rewrite subr0.
Qed.

Section tilt_eqn.
Context {K : realType}.
Variables alpha1 gamma : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.

Definition tilt_eqn (f : K -> 'rV[K]_6) : K -> 'rV[K]_6 :=
  let error1_p_dot := Left \o f in
  let error2_p_dot := Right \o f in
  fun t => row_mx
    (- alpha1 *: error1_p_dot t)
    (eqn14b_rhs gamma (error1_p_dot t) (error2_p_dot t)).

Definition tilt_eqn_no_time (zp1_z2_point : 'rV[K]_6) : 'rV[K]_6 :=
  let zp1_point := Left zp1_z2_point in
  let z2_point := Right zp1_z2_point in
  row_mx (- alpha1 *: zp1_point)
         (eqn14b_rhs gamma zp1_point z2_point).

Definition tilt_eqn' (x : 'rV[K]_6) : 'rV[K]_6 :=
  let zp1_point := Left x in
  let z2_point := Right x in
  row_mx (- alpha1 *: zp1_point)
         (eqn14b_rhs gamma zp1_point z2_point).

Lemma tilt_eqn'E (f : K -> 'rV[K]_6) t :
  tilt_eqn' (f t) = tilt_eqn f t.
Proof. by []. Qed.

Lemma tilt_eqnE f t : tilt_eqn f t = tilt_eqn_no_time (f t).
Proof. by []. Qed.

(* TODO: this does not hold, we need locally lipschitz *)
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

(*Lemma invariant_state_space_tilt p
  (p33 : state_space tilt_eqn' state_space_tilt p) :
  let y := sval (cid p33) in
  let t := sval (cid (svalP (cid p33)).2) in
  forall Delta, Delta >= 0 ->
  state_space tilt_eqn state_space_tilt (y (t + Delta)).
Proof.
case: p33 => /= x0 sol_y Delta Delta_ge0.
rewrite /state_space/=.
exists x0; split.
  by case: sol_y.
case: cid => //= y' y'sol.
case: cid => t'/= pt'.
Abort.*)

Variable (r : {posnum K}).

Lemma derivable_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
   derivable f t v -> derivable (fun x => rsubmx (f x)) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= r' Hr]:= df1.
apply/cvg_ex => /=; exists (r'``_(rshift n1 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hr => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, rshift n1 j)).
by rewrite !mxE.
Qed.

Lemma derive_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v ->
  'D_v (fun x => rsubmx (f x)) t = @rsubmx _ _ n1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE//=; last exact: derivable_rsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.

Lemma state_space_tiltS Delta :
  state_space (tilt_eqn') r state_space_tilt Delta `<=` state_space_tilt.
Proof.
have [Delta0|Delta0] := leP 0 Delta; last first.
  move=> t.
  rewrite /state_space/= => -[f [rf [x]]].
  rewrite in_itv/= => -[/andP[x0 xDelta]].
  have := lt_trans xDelta Delta0.
  by rewrite ltNge (ltW x0).
move=> p [y [[y0_init1]] [_ [/= deri [conti ball]]]].
rewrite /state_space_tilt.
have : {in `]0, Delta[, derive1 (fun t => ('e_2 - Right (y t)) *d (('e_2 - Right (y t)))) =1 0}.
  move => x xd /=.
  transitivity ((fun t => -2 * (Right(y^`()%classic t) *d ('e_2 - Right (y t)))) x).
    rewrite !derive1E.
    rewrite derive_mx; last first.
      by apply deri.
    rewrite /dotmul.
    under eq_fun do rewrite dotmulP /=.
    rewrite dotmulP.
    rewrite !mxE /= mulr1n.
    under eq_fun do rewrite !mxE /= mulr1n.
    rewrite !derive_dotmul/=; last 2 first.
      apply: derivableB => //=;  apply : derivable_rsubmx => //=.
      by apply deri.
      apply: derivableB => //=; apply: derivable_rsubmx => //=.
      by apply deri.
    rewrite /dotmul /=.
    rewrite [in RHS]mulr2n [RHS]mulNr [in RHS]mulrDl.
    rewrite !mul1r !dotmulP /= dotmulC [in RHS]dotmulC !linearD /=.
    rewrite !mxE /= !mulr1n.
    have -> : 'D_1 (fun x2 : K => 'e_2 - Right (y x2)) x = - Right ('D_1 y x).
      rewrite deriveB /= ; last 2 first.
        exact: derivable_cst.
        apply: derivable_rsubmx.
        by apply deri.
      rewrite derive_cst /= sub0r; congr (- _).
      apply: derive_rsubmx.
      by apply deri.
    rewrite -(_ : 'D_1 y x =
        (\matrix_(i, j) 'D_1 (fun t0 : K => y t0 i j) x)); last first.
      apply/matrixP => a b; rewrite !mxE.
      rewrite derive_mx//= ?mxE//.
      by apply deri.
    ring.
  have Rsu t0 : t0 \in `]0, Delta[ ->  Right (y^`()%classic t0) =
               (gamma *: (Right (y t0) - Left (y t0)) *m \S('e_2 - Right (y t0)) ^+ 2).
    move => t0d.
    have [_ ->] := deri t0 t0d.
    by rewrite row_mxKr.
  rewrite /dotmul.
  transitivity (-2 * (gamma *: (Right (y x) -
                          Left (y x)) *m \S('e_2 - Right (y x)) ^+ 2 *m
                                          ('e_2 - Right (y x))^T) 0 0).
    by rewrite Rsu.
  rewrite !mulmxA.
  apply/eqP.
  rewrite mulf_eq0 /= oppr_eq0 ?pnatr_eq0 /= -!mulmxA spin_mul_tr.
  by rewrite !mulmx0 mxE.
move => h [t [t0d ->]].
   (* under eq_fun do rewrite dotmulvv /=. (* derivee de la norme est egale a 0 *)  *)
    (* move => h. *)
have norm_constant : forall t, t \in `]0,Delta[ -> `|'e_2 - Right (y t)|_e ^+ 2 = `|'e_2 - Right (y 0)|_e ^+ 2.
  move => t0.
  have : forall x0, x0 \in `]0,Delta[ -> is_derive x0 (1:K) (fun x : K => `|'e_2 - Right (y x)|_e ^+ 2) 0.
    move => x0 x0d.
    apply: DeriveDef.
      apply/derivable_enorm_squared => //=.
      apply/derivableB => //=.
      apply/derivable_rsubmx => //.
      by apply deri.
    rewrite -derive1E.
    have := h _ x0d.
    under eq_fun do rewrite dotmulvv /=.
                    by apply.
  rewrite /=.
  move => hd0 t0d'.
  apply/esym.
  have := is_derive_0_is_cst_new t0d' _ hd0.
  apply => //; last first.
    by rewrite inE/= in_itv/= lexx/=.
  apply: (@within_continuous_comp _ _ _ _ _ (fun x => `|'e_2 - Right x|_e ^+ 2) y) => //=.
  move=> z _.
  apply: differentiable_continuous => //.
  apply: differentiable_enorm_squared => /=.
  apply: differentiableB => //.
  by apply: differentiable_rsubmx.
suff: `|'e_2 - Right (y t)|_e ^+ 2 = 1.
  move => /(congr1 Num.sqrt).
  rewrite sqrtr1 sqr_sqrtr //.
  by rewrite dotmulvv sqr_ge0.
rewrite norm_constant //; last first.
  by rewrite inE.
move: y0_init1.
rewrite inE /state_space_tilt /= => ->.
by rewrite expr2 mulr1.
Qed.

Definition point1 : 'rV[K]_6 := 0.
Definition point2 : 'rV[K]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2).

Lemma equilibrium_point1 Delta :
  is_equilibrium_point (tilt_eqn') r state_space_tilt Delta point1.
Proof.
split => //=.
- rewrite inE /state_space_tilt /point1.
  rewrite /=.
  by rewrite rsubmx_const /= subr0 enormeE.
- split => //.
  split.
  + move=> t tDelta.
    split; first exact: derivable_cst.
    rewrite derive1E derive_cst /tilt_eqn /point1; apply/eqP.

    rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP. split.
      rewrite scaler_eq0; apply/orP; right; apply/eqP/rowP; move => i.
      rewrite /=.
      by rewrite lsubmx_const.
    apply/eqP/rowP; move => i; apply/eqP.
    rewrite /eqn14b_rhs.
    set N := (X in _ *: X *m _); have : N = 0.
      rewrite /N /=; apply /rowP; move => a.
      rewrite !mxE.
      by rewrite subrr.
  by move => n; rewrite n scaler0 mul0mx.
 + split.
     apply: continuous_subspaceT =>x.
     exact: cvg_cst.
   move => t td /=.
   by apply closed_ballxx.
Qed.

Lemma equilibrium_point2 Delta :
  is_equilibrium_point (tilt_eqn') r state_space_tilt Delta point2.
Proof.
split => //.
- rewrite inE /state_space_tilt /point2 /=.
  rewrite row_mxKr.
  rewrite -[X in X - _ ]scale1r.
  rewrite -scalerBl enormZ enormeE mulr1 distrC.
  rewrite [X in _ - X](_:1 = 1%:R) //.
  by rewrite -natrB //= normr1.
- split => //.
  split.
  + move=> t tDelta.
    split; first exact: derivable_cst.
    rewrite derive1E derive_cst; apply/eqP.
    rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
    set N := (X in _ *: X == 0 /\ _).
    have N0 : N = 0.
      apply/rowP; move => i; rewrite !mxE; case: splitP.
        move => j _; by rewrite mxE.
      move => k /= i3k.
      have := ltn_ord i.
       by rewrite i3k -ltn_subRL subnn.
    split.
      by rewrite scaler_eq0 N0 eqxx orbT.
    rewrite /eqn14b_rhs.
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
    rewrite ME -scalemxAl scalemx_eq0 pnatr_eq0/=.
    rewrite [X in X *: _](_ : _ = 1 + 1)// scalerDl scale1r opprD addrA.
    rewrite subrr sub0r spinN sqrrN expr2 -mulmxE mulmxA.
    rewrite (_ : 'e_2 *m _ = 0) ?mul0mx//; apply: trmx_inj.
    by rewrite trmx_mul trmx0 tr_spin mulNmx spin_mul_tr oppr0.
 + split.
     apply: continuous_subspaceT =>x.
     exact: cvg_cst.
   move => t td /=.
   by apply closed_ballxx.
Qed.

End tilt_eqn.
Arguments point1 {K}.

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

Lemma u2_quadratic_form_gt0 (v : 'rV_2) :
  v != 0 -> 0 < (v *m u2 *m v^T) 0 0.
Proof.
move=> v0.
rewrite !(mxE,sum2E,mulr1)/= !mulrDl -!expr2.
rewrite [ltRHS](_ : _ = v``_0 ^+ 2 - v``_1 * v``_0 + v``_1 ^+ 2); last first.
  rewrite -!addrA; congr +%R.
  rewrite !addrA; congr +%R.
  rewrite (mulrC _ v``_0) -mulrA -mulrDr.
  rewrite mulrC -mulNr; congr *%R.
  rewrite mulrC -mulrDr -mulr2n.
  rewrite mulNr; congr (- _).
  rewrite -(mulr_natl v``_1).
  by rewrite mulrA mulVf// ?mul1r.
rewrite [ltRHS](_ : _ = (v``_0 - 2^-1 * v``_1) ^+ 2 + 3 / 4 * v``_1 ^+ 2); last first.
  rewrite sqrrB -!addrA; congr +%R.
  rewrite -mulNrn mulrCA -(mulr_natl (- _) 2) mulrN !mulrA divff ?mul1r//.
  rewrite mulrC; congr +%R.
  rewrite -mulrA -expr2 exprMn -mulrDl.
  rewrite (expr2 2^-1).
  rewrite -invfM -div1r -natrM -mulrDl.
  by rewrite nat1r divff// mul1r.
rewrite ltNge le_eqVlt negb_or -leNgt addr_ge0 ?(sqr_ge0,mulr_ge0)// andbT.
rewrite paddr_eq0 ?(sqr_ge0,mulr_ge0)//.
apply/negP => /andP[]; rewrite sqrf_eq0 => /[swap].
rewrite mulf_eq0/= sqrf_eq0 mulf_eq0 invr_eq0 !pnatr_eq0/= => /eqP v10.
rewrite v10 mulr0 subr0 => /eqP v00.
move/negP : v0; apply.
apply/eqP/rowP => -[[i|[j|//]]]; rewrite !mxE//.
by rewrite (_ : Ordinal _ = 0)//; exact/val_inj.
by rewrite (_ : Ordinal _ = 1)//; exact/val_inj.
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
  `|zp1|_e ^+ 2 / (2 * alpha1) + `|z2|_e ^+ 2 / (2 * gamma).

Lemma V1_is_Lyapunov_candidate : is_Lyapunov_candidate V1 [set: 'rV_6] point1.
Proof.
rewrite /V1 /point1; split; first by rewrite inE.
split.
  by rewrite lsubmx_const rsubmx_const enorm0 expr0n/= !mul0r add0r.
move=> /= z_near _ z0.
have /orP[lz0|rz0] : (Left z_near != 0) || (Right z_near != 0).
  rewrite -negb_and.
  apply: contra z0 => /andP[/eqP l0 /eqP r0].
  rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
  apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?;
  by rewrite mxE.
- set rsub := Right z_near.
  have : `|rsub|_e >= 0 by rewrite enorm_ge0.
  set lsub := Left z_near.
  move=> nor.
  have normlsub : `|lsub|_e > 0 by rewrite enorm_gt0.
  rewrite ltr_pwDl//.
    by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
  by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
- rewrite ltr_pwDr//.
    by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0// enorm_gt0.
  by rewrite divr_ge0 ?exprn_ge0 ?enorm_ge0// mulr_ge0// ltW.
Unshelve. all: by end_near. Qed.

Definition V1dot (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  - `|zp1|_e ^+ 2 + (z2 *m (\S('e_2 - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2 - z2))^+2 *m zp1^T)``_0.

End V1.

Section hurwitz.
Context {K : realType}.

(* thm 4.6 p136*)
Definition hurwitz n (A : 'M[K]_n) : Prop :=
  (forall a, eigenvalue A a -> a < 0).

(* thm 4.7 p139 + fact: it is exponentially stable*)
Definition locally_exponentially_stable_at n (eqn : 'rV[K]_n -> 'rV[K]_n)
    (point : 'rV[K]_n) : Prop :=
  hurwitz (Jacobian eqn point).

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
(*Variable R : K -> 'M[K]_3.*)
Variable Delta : K.

Variable r : {posnum K}.
(* generalization from the other file *)

Lemma derivable_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v -> derivable (fun x => lsubmx (f x)) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= l Hl]:= df1.
apply/cvg_ex => /=; exists (l``_(lshift n2 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, lshift n2 j)).
by rewrite !mxE.
Qed.

Lemma derive_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v ->
  'D_v (fun x => lsubmx (f x)) t = @lsubmx _ _ n1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE//=; last exact: derivable_lsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.

Lemma derive_zp1 (z : K) (sol : K -> 'rV_6) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r sol ->
  z \in `]0, Delta[ -> 'D_1 (Left \o sol) z = - alpha1 *: Left (sol z).
Proof.
move=> [/= traj0 [_ [dtraj btraj] ] zd].
have [_ +] := dtraj _ zd.
move=> /(congr1 Left).
rewrite derive1E.
rewrite row_mxKl => ?; rewrite derive_lsubmx//=.
by apply dtraj.
Qed. 

Lemma derive_z2 (z : K) (sol : K -> 'rV_6) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r sol ->
  z \in `]0, Delta[ -> 'D_1 (Right \o sol) z =
  gamma *: (Right (sol z) - Left (sol z)) *m \S('e_2 - Right (sol z)) ^+ 2.
Proof.
move=> [/= traj0 [_ [dtraj btraj] ] zd].
have [_ +] := dtraj _ zd.
move => /(congr1 Right).
rewrite derive1E.
rewrite row_mxKr => ?; rewrite derive_rsubmx //.
by apply dtraj.
Qed.

Lemma is_sol_state_space_tilt (sol : K -> 'rV_6) t :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r sol ->
  state_space_tilt (sol t).
Proof.
case => sol0 [_[ deriv_sol bsol]].
apply: (@state_space_tiltS _ alpha1 gamma) => //=.
exists sol; split => //.
(*by exists t.
Qed.*) Admitted.

Lemma enorm_e2z2 (sol : K -> 'rV_6) (z : K)
    (z2 := Right \o sol) (zp1 := Left \o sol) (u := 'e_2 - z2 z) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r sol -> `|u|_e = 1.
Proof.
move=> dtraj.
suff: state_space_tilt (row_mx (zp1 z) (z2 z)).
  by rewrite /state_space_tilt/= row_mxKr.
rewrite /zp1 /z2 hsubmxK /=.
exact: is_sol_state_space_tilt.
Qed.

Lemma angvel_sqr (traj : K -> 'rV_6) (z : K)  (z2 := fun r : K => Right (traj r) : 'rV_3)
  (w := (z2 z) *m \S('e_2)) (u := 'e_2 - z2 z) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r traj ->
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
rewrite !mulmxA dotmulP dotmulvv enorm_e2z2 // expr2 mulr1.
rewrite [X in _ =  - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1n /=.
rewrite [X in _ =   - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1.
have wu0 : w *m u^T *m u = 0 by rewrite dotmulP Hw_ortho mul_scalar_mx scale0r.
rewrite -[in LHS](mulmxA w) sqr_spin; last by rewrite -/u enorm_e2z2.
rewrite [in LHS]mulmxBr mulmxA wu0 sub0r.
by rewrite 2!mulNmx mulmx1 mxE.
Qed.

Lemma neg_spin (traj : K -> 'rV_6) (z : K) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r traj ->
  `|Right (traj z) *m \S('e_2) *m - \S('e_2 - Right (traj z))|_e =
  `|Right (traj z) *m \S('e_2)|_e.
Proof.
move=> dtraj.
rewrite mulmxN enormN.
pose zp1 := fun r => Left (traj r).
pose z2 := fun r => Right (traj r).
set w := (z2 z) *m \S('e_2).
have Gamma1_traj t : state_space_tilt (traj t) by apply/is_sol_state_space_tilt.
rewrite /enorm.
rewrite !dotmulvv [RHS]sqrtr_sqr sqrtr_sqr.
have Hnorm_sq : `|w *m \S('e_2 - Right (traj z))|_e ^+ 2 = `|w|_e ^+ 2.
  rewrite -!dotmulvv angvel_sqr// !dotmulvv enorm_e2z2//=.
  rewrite -!dotmulvv expr2 !mul1r mulr1.
  have -> : w *d ('e_2 - Right (traj z)) = 0 by rewrite dotmulC ortho_spin.
  by rewrite expr2 mul0r subr0.
rewrite !normr_enorm.
by move/sqr_inj : Hnorm_sq => ->//; rewrite ?nnegrE ?enorm_ge0.
Qed.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

Lemma V1dotE (z : K) (sol : K -> 'rV_6)
  (zp1 := Left \o sol) (z2 := Right \o sol) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r sol ->
  z \in `]0, Delta[ ->
  V1dot (sol z) =
    c1 *: (2 *: 'D_1 zp1 z *m (Left (sol z))^T) 0 0 +
    c2 *: (2 *: 'D_1 z2 z *m (Right (sol z))^T) 0 0.
Proof.
move=> ? zd.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC.
rewrite mulVf// div1r.
rewrite derive_zp1 // -scalemxAl mxE [X in X + _](mulrA (alpha1^-1) (- alpha1)).
rewrite mulrN mulVf ?gt_eqF// mulN1r.
rewrite derive_z2 // -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE.
rewrite scalerA mulVf ?gt_eqF// scale1r.
rewrite enorm_squared /V1dot.
congr +%R.
rewrite -2![in LHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
rewrite -[X in (X *m (_ *m _)) 0 0 = _]trmxK.
rewrite -[X in (_ *m (X *m _)) 0 0 = _]trmxK.
rewrite mulmxA -trmx_mul -trmx_mul [LHS]mxE.
rewrite -(mulmxA (Right (sol z) - (Left (sol z)))) mulmxE -expr2.
rewrite tr_sqr_spin.
by rewrite mulmxA.
Qed.

Lemma derive_along_V1 (x : 'rV[K]_6) t sol :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r (sol x) ->
  (forall t, differentiable (sol x) t) ->
  'D~(sol x(*, x*)) (V1 alpha1 gamma) t = V1dot (sol x t).
Proof.
rewrite /tilt_eqn => tilt_eqnx dif1.
rewrite /V1 derive_alongD; last 3 first.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_lsubmx.
  apply/differentiableM => //=.
  exact/differentiable_enorm_squared/differentiable_rsubmx.
  exact: dif1.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
rewrite derive_alongMl => //; last first.
  exact/differentiable_enorm_squared/differentiable_lsubmx.
rewrite derive_alongMl => //; last first.
  exact/differentiable_enorm_squared/differentiable_rsubmx.
rewrite -fctE /= !derive_along_enorm_squared//=.
- rewrite V1dotE.
    by rewrite /c1 /c2 !invfM.
  rewrite /= in tilt_eqnx.
  exact: tilt_eqnx.
- admit.
- exact/differentiable_lsubmx.
- exact/differentiable_rsubmx.
Admitted.

Definition u1 (sol : K -> 'rV[K]_6) t
  (zp1 := Left \o sol) (z2 := Right \o sol)
  (w := z2 t *m \S('e_2)) : 'rV[K]_2 :=
  \row_(i < 2) [eta (fun=> 0) with 0 |-> `|zp1 t|_e, 1 |-> `|w|_e] i.

Lemma V1dot_ub (sol : K -> 'rV[K]_6) (zp1 := Left \o sol) (z2 := Right \o sol) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r sol ->
  forall t,
    V1dot (sol t) <= (- (u1 sol t) *m u2 *m (u1 sol t)^T) 0 0.
Proof.
move=> dtraj z.
set w := z2 z *m \S('e_2).
rewrite /V1dot.
rewrite mxE norm_spin mxE addrA expr2 mulmxA.
have -> : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2).
  by rewrite spinD spinN -tr_spin !mulmxDr !mul_tr_spin !addr0.
rewrite -dotmulNv addrC -mulmxN -expr2.
have cauchy : ((w *m - \S('e_2 - z2 z) *d (zp1 z))%:M : 'rV_1) 0 0 <=
              `|w *m - (\S('e_2 - z2 z))|_e * `|zp1 z|_e.
  rewrite mxE /= mulr1n (le_trans (ler_norm _)) //.
  rewrite -ler_sqr // ; last first.
    by rewrite nnegrE //  mulr_ge0 ?enorm_ge0.
  by rewrite exprMn sqr_normr (le_trans (CauchySchwarz_vec _ _)) // !dotmulvv.
apply: (@le_trans _ _ (`|w *m - \S('e_2 - z2 z)|_e * `|zp1 z|_e + (- `|zp1 z|_e ^+ 2 - `|w|_e ^+ 2))).
  rewrite lerD2r.
  rewrite (le_trans _ (cauchy)) //.
  by rewrite mxE eqxx mulr1n.
rewrite neg_spin /u1 /u2 //.
rewrite mxE.
rewrite !sum2E/= ![in leRHS]mxE !sum2E/= ![in leRHS]mxE /=.
rewrite !mulr1 mulrN mulNr opprK mulrDl mulNr -expr2.
rewrite [in leLHS] addrCA -!addrA lerD2l mulrDl (mulNr `|w|_e).
rewrite -expr2 !addrA lerD2r !(mulrN , mulNr) opprK -mulrA.
rewrite [in leRHS](mulrC (_ / 2)) (mulrC 2^-1) -mulrDr -splitr.
by rewrite [leRHS]mulrC.
Qed.

(* TODO: rework of this proof is needed *)
(* NB: unused *)
Lemma derive_along_Left_Right_le0 sol (x : 'rV[K]_6) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r (sol x) ->
  sol x 0 = point1 ->
  \forall z \near 0^',
    ('D~(sol x) (fun x => `|Left x|_e ^+ 2 / (2 * alpha1)) +
     'D~(sol x) (fun x => `|Right x|_e ^+ 2 / (2 * gamma))) z <= 0.
Proof.
move=> [in_init [_ [dtraj btraj]]] traj0.
rewrite fctE !invfM /=.
near=> z.
under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC.
(* move: dtraj => [H0 Hderiv Htilt]. *)
(* have Hz_derivable : derivable (sol x) z 1. *)
(*   apply: Hderiv. *)
(*   admit. *)
(* rewrite derive_alongMl; last 2 first. *)
(*   exact/differentiable_norm_squared/differentiable_lsubmx. *)
(*   apply derivable1_diffP. *)
(*   apply: Hderiv. *)
(*   admit. *)
(* rewrite derive_alongMl; last 2 first. *)
(*   exact/differentiable_norm_squared/differentiable_rsubmx. *)
(*   exact/derivable1_diffP. *)
(* rewrite /= !derive_along_norm_squared; last 4 first. *)
(*   exact/differentiable_rsubmx. *)
(*   exact/derivable1_diffP. *)
(*   exact/differentiable_lsubmx. *)
(*   exact/derivable1_diffP. *)
(* rewrite -V1dotE //. *)
(* pose zp1 := Left \o sol x. *)
(* pose z2 := Right \o sol x. *)
(* set w := (z2 z) *m \S('e_2). *)
(* pose u1 : 'rV[K]_2 := *)
(*   \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i. *)
(* apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)). *)
(*   exact: V1dot_ub. *)
(* have [->|H] := eqVneq u1 0. *)
(*   by rewrite mulNmx mul0mx mulNmx mul0mx mxE mxE oppr0. *)
(* by rewrite leNgt 2!mulNmx mxE oppr_gt0 -leNgt ltW// u2_quadratic_form_gt0. *)
Unshelve. all: try by end_near. Admitted.

(* NB: should be completed to prove asymptotic stability *)
Lemma locnegsemidef_derive_alone_V1 sol (x : 'rV[K]_6) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r (sol x) ->
  sol x 0 = point1 ->
  locnegsemidef ('D~(sol x) (V1 alpha1 gamma)) 0.
Proof.
(* move=> [y033] dy dtraj traj0. *)
(* rewrite /locnegsemidef /V1. *)
(* rewrite derive_alongD /=; last 3 first. *)
(*   apply: differentiableM => /=; last exact: differentiable_cst. *)
(*   exact/differentiable_norm_squared/differentiable_lsubmx. *)
(*   apply: differentiableM; last exact: differentiable_cst. *)
(*   exact/differentiable_norm_squared/differentiable_rsubmx. *)
(*   apply/derivable1_diffP. *)
(*   admit. *)
(* split; last first. *)
(*   near=> z. *)
(*   rewrite derive_along_derive //; last first. *)
(*     apply/derivable1_diffP. *)
(*     admit. *)
(*   admit. (* TODO: lynda *) *)
(*   admit. (* TODO: lynda *) *)
(* under [X in derive_along X _ _ + _]eq_fun do rewrite mulrC. *)
(* under [X in _ + derive_along X _ _]eq_fun do rewrite mulrC. *)
(* rewrite derive_alongMl; last 2 first. *)
(*   exact/differentiable_norm_squared/differentiable_lsubmx. *)
(*   apply/derivable1_diffP. *)
(*   admit. *)
(* rewrite /= !derivative_derive_along_eq0. *)
(* - by rewrite scaler0 add0r. *)
(* TODO: urgent - apply/differentiable_norm_squared/differentiable_rsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  rewrite /eqn14b_rhs.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
    exact/differentiable_enorm_squared/differentiable_lsubmx.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  rewrite /eqn14b_rhs.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.*)
Abort.

Lemma locnegdef_derive_along_V1 sol (x : 'rV[K]_6)
   (zp1 := Left \o sol x) (z2 := Right \o sol x) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r (sol x) ->
  (forall t : K, state_space_tilt (sol x t)) ->
  sol x 0 = point1 ->
  locnegdef ('D~(sol x) (V1 alpha1 gamma)) 0.
Proof.
move=> solves state y0.
split.
  rewrite /is_sol in solves.
  rewrite /= derivative_derive_along_eq0 => //; last first.
    admit.
  rewrite /V1.
  apply: differentiableD => //; last first.
    apply: differentiableM; last exact: differentiable_cst.
    exact/differentiable_enorm_squared/differentiable_rsubmx.
  apply: differentiableM => //.
  exact/differentiable_enorm_squared/differentiable_lsubmx.
near=> z0.
rewrite derive_along_V1.
- have V1dot_le := V1dot_ub solves z0 => //.
  set w := z2 z0 *m \S('e_2).
  set u1 : 'rV[K]_2 := \row_(i < 2)
    [eta (fun=> 0) with 0 |-> `|zp1 z0|_e, 1 |-> `|w|_e] i.
  have Hpos : 0 <  (u1 *m u2 *m u1^T) 0 0.
    rewrite u2_quadratic_form_gt0//.
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
      by under [in LHS]eq_bigr do rewrite mulNmx mxE.
  by apply/ltW => //.
  rewrite /V1dot.
  rewrite mxE/=.
  apply/eqP => Habs.
  admit.
- by [].
- move => t.
  apply/derivable1_diffP => //.
  move : solves; rewrite /is_sol.
(*  by case.*) admit.
Unshelve. all: by end_near. Abort.

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

Lemma derive_along_V1_le0 sol (x : 'rV[K]_6) :
  is_sol (tilt_eqn' alpha1 gamma) state_space_tilt Delta r (sol x) ->
  (forall t, differentiable (sol x) t) ->
  forall t : K, 0 <= t ->
  'D~(sol x) (V1 alpha1 gamma) t <= 0.
Proof.
move=> solves diff t t0.
rewrite derive_along_V1//.
have Hub := V1dot_ub solves t.
apply: (le_trans Hub).
have Hquad : let u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o sol x) t|_e,
                        1 |-> `|(Right \o sol x) t *m \S('e_2)|_e]
                         i in 0 <= (u1 *m u2 *m u1^T) 0 0.
  set u1 := \row_i [eta fun=> 0
                   with 0 |-> `|(Left \o sol x) t|_e,
                        1 |-> `|(Right \o sol x) t *m \S('e_2)|_e]
            i.
  rewrite /=.
  case: (u1 =P 0) => [->|/eqP u1_neq0].
    by rewrite !mul0mx mxE.
  by rewrite ltW// u2_quadratic_form_gt0.
by rewrite -oppr_ge0 !mulNmx mxE opprK Hquad.
Qed.

End tilt_eqn_Lyapunov.

Section equilibrium_zero_stable.
Context {K : realType}.
Variables gamma alpha1 : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Let phi := tilt_eqn' alpha1 gamma.
Variable Init : set 'rV[K]_6.
Variable sol : 'rV[K]_6 -> K -> 'rV[K]_6.
Variable Delta : K.
Variable r : {posnum K}.

(*Hypothesis solP : existence_uniqueness phi Init sol.*)
(*Hypothesis sol0 : initial_condition sol.*)
Check is_sol_autonomous.

Hypothesis solP :
( is_sol_autonomous 0 phi r 0 Delta (sol 0)).


Hypothesis y0 : 0 \in Init.

Notation is_sol := (is_sol phi Init).

(* Hypothesis y_sol : is_sol Delta (sol 0). *)
(* Hypothesis y00 : sol 0 0 = 0. *)

Lemma is_equilibrium_subset :
  is_equilibrium_point phi r state_space_tilt Delta 0 ->
  is_equilibrium_point phi r Init Delta 0.
Proof.
rewrite /is_equilibrium_point.
rewrite /is_sol/= inE => -[inD0 deriv ].
by split => //; exact/set_mem.
Qed.

Lemma equilibrium_zero_stable :
  open Init -> 0 \in Init -> Init `<=` state_space_tilt ->
  is_locally_stable_at point1 Delta (sol 0).
Proof.
move=> openInit Init0 Init_in_state.
Check @Lyapunov_stability.
apply: (@Lyapunov_stability K _ phi Init Delta sol r solP openInit (V1 alpha1 gamma)).
- move=> t.
  apply/differentiableD => //.
    apply/differentiableM => //.
    exact/differentiable_enorm_squared/differentiable_lsubmx.
  apply/differentiableM => //.
  exact/differentiable_enorm_squared/differentiable_rsubmx.
- move=> z zD t t0.
  apply: (@derive_along_V1_le0 _ _ _ _ _ Delta).
  assumption.
  assumption.
  + apply: (is_sol_subset Init_in_state).
    admit. (*  pbm *)
(*    by apply solP; rewrite sol0.*)
  + move=> t1.
    rewrite -derivable1_diffP.
    (*have : is_sol (sol z) by apply solP; rewrite sol0.
    by case.*) admit.
- assumption.
- have := V1_is_Lyapunov_candidate alpha1_gt0 gamma_gt0.
  rewrite /is_Lyapunov_candidate /point1 => Hpos.
  rewrite /V1 lsubmx_const rsubmx_const; split => //.
  split.
    by rewrite !expr2 !enorm0 !mulr0 !mul0r add0r.
  move=> z zin z_neq0.
  case : Hpos => // _ [_].
  by apply => //; rewrite inE.
- exact/is_equilibrium_subset/equilibrium_point1.
Admitted.

End equilibrium_zero_stable.
