From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import boolp classical_sets functions reals order.
From mathcomp Require Import topology normedtype landau derive realfun.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.
Require Import tilt_mathcomp tilt_analysis tilt_robot.
(*Require Import lasalle pendulum.*)

(**md**************************************************************************)
(* # tentative formalization of [1]                                           *)
(*                                                                            *)
(*                defposmx M == M is definite positive                        *)
(*             locposdef V x == V is locally positive definite at x           *)
(*   is_lyapunov_candidate V := locposdef V                                   *)
(*         locnegsemidef V x == V is locally negative semidefinite            *)
(*         LieDerivative V x == Lie derivative                                *)
(*       solves_equation f y == the function y satisfies y' = f y             *)
(*  is_equilibrium_point f p := solves_equation f (cst p)                     *)
(*             state_space f == the set points attainable by a solution       *)
(*                              (in the sense of `solves_equation`)           *)
(*  is_lyapunov_stable_at f V x == Lyapunov stability                         *)
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

(* spin and matrix/norm properties*)

Lemma norm_spin {R : realType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
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

Definition defposmx {R : realType} m (M : 'M[R]_m) : Prop :=
  M \is sym m R /\ forall a, eigenvalue M a -> a > 0.

Lemma defposmxP {R : realType} m (M : 'M[R]_m) :
  defposmx M <-> (forall v : 'rV[R]_m, v != 0 -> (v *m M *m v^T) 0 0 > 0).
Proof.
split.
  move => [matsym eigen] x xneq0.
  apply/eigen/eigenvalueP; exists x => //=.
  apply/matrixP => i j.
  (* theoreme spectral? *)
Admitted.

Local Open Scope classical_set_scope.

Definition locposdef {R : realType} (T : normedModType R) (V : T -> R) (D : set T) (x : T) : Prop :=
  x \in D /\ V x = 0 /\ open D /\ forall z, z \in D -> z != x -> V z > 0.

(* add continuously diff*)
Definition is_lyapunov_candidate {K : realType} {n} (V : 'rV[K]_n.+1 -> K) (D : set  'rV[K]_n.+1)
 (x0 : 'rV[K]_n.+1) := locposdef V D x0 /\ differentiable V x0.

(* locally positive semi definite (NB* not used yet) *)
Definition lpsd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
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

Section LieDerivative.

Definition LieDerivative {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (phi : 'rV[R]_n.+1 -> R -> 'rV[R]_n.+1) (x : 'rV[R]_n.+1) (t : R) : R :=
  (jacobian1 V (phi x t))^T *d 'D_1 (phi x) t.
(* we assume that phi is the solution of a diff equa such that phi 0 x = x *) 

Lemma LieDerivative_derive {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (phi : 'rV[R]_n.+1 -> R -> 'rV[R]_n.+1) (t : R) (x : 'rV[R]_n.+1) :
   (differentiable V (phi x t)) -> (differentiable (phi x) t) ->
  LieDerivative V phi x t = 'D_1 (V \o (phi x)) t.
(* Warning: we are not representing the initial state at t = 0 of the trajectory x
   see Khalil p.114 *)
Proof.
move => dif1 dif2.
rewrite /LieDerivative /=.
rewrite /jacobian1.
rewrite /jacobian.
rewrite /dotmul.
rewrite -trmx_mul.
rewrite mul_rV_lin1.
rewrite mxE.
rewrite -deriveE => //=; last first.
  apply: differentiable_comp => //=.
  exact/differentiable_scalar_mx (* *).
rewrite derive_mx /=.
rewrite mxE.
rewrite [in RHS]deriveE => //=.
rewrite [in RHS]diff_comp => //=.
rewrite -![in RHS]deriveE => //=.
under eq_fun do rewrite mxE /= mulr1n /=.
by [].
apply: differentiable_comp => //=; last first.
apply: derivable_scalar_mx => //=.
apply: diff_derivable => //=.
Qed.

Lemma LieDerivativeMl {R : realType} n (f : 'rV_n.+1 -> R) (phi : 'rV[R]_n.+1 -> R -> 'rV_n.+1)
    (x : 'rV[R]_n.+1)
    (k : R) t :
  (differentiable f (phi x t)) -> differentiable (phi x) t ->
  LieDerivative (k *: f) phi x t = k *: LieDerivative f phi x t.
Proof.
move=> dfx dpx.
rewrite LieDerivative_derive; last 2 first.
  apply: differentiable_comp => //=.
  done.
rewrite deriveZ/=; last first => //=.
  apply: diff_derivable => //=.
  rewrite -fctE.
  apply: differentiable_comp => //=.
congr (_ *: _).
rewrite LieDerivative_derive//=.
Qed.

Lemma LieDerivativeD {R : realType} n (f g : 'rV_n.+1 -> R) (phi : 'rV[R]_n.+1 -> R -> 'rV_n.+1) (x : 'rV_n.+1) t :
  (differentiable f (phi x t)) -> differentiable g (phi x t) ->
    differentiable (phi x) t ->
  LieDerivative (f + g) phi x t  = LieDerivative f phi x t + LieDerivative g phi x t.
Proof.
move=> dfx dgx difp.
rewrite LieDerivative_derive; last 2 first.
  by apply: differentiableD => //=.
  done.
rewrite deriveD/=; last 2 first.
  apply: diff_derivable => //.
  rewrite -fctE .
  by apply: differentiable_comp => //=.
  apply: diff_derivable => //.
  rewrite -fctE .
  by apply: differentiable_comp => //=.
rewrite LieDerivative_derive; last 2 first.
  by [].
  by [].
rewrite LieDerivative_derive; last 2 first.
  by [].
  by [].
by [].
Qed.

Lemma derivative_LieDerivative_eq0 {K : realType} n
     (phi : 'rV[K]_n.+1 -> K -> 'rV_n.+1)
    (f : 'rV_n.+1 -> K) (x : 'rV[K]_n.+1) (t : K) :
  (differentiable f (phi x t)) ->
  'D_1 (phi x) t = 0 -> LieDerivative f phi x t = 0.
Proof.
move=> xt1 dtraj.
rewrite /LieDerivative /jacobian1 /dotmul dotmulP /dotmul -trmx_mul.
by rewrite dtraj mul0mx !mxE.
Qed.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

(* TODO version squared sans different de 0 *)
Lemma LieDerivative_norm {K : realType} n m (f : 'rV[K]_n.+1 -> 'rV_m.+1)
    (phi : 'rV[K]_n.+1 -> K -> 'rV_n.+1)
    (x : 'rV[K]_n.+1) (t : K) :
     differentiable f (phi x t) -> 
       differentiable (phi x) t ->
     (forall t, differentiable f t) ->
    LieDerivative (fun y => (norm (f y)) ^+ 2) phi x t =
    (2%:R *: 'D_1 (f \o phi x) t *m (f (phi x t))^T) 0 0.
Proof.
move => diffp difpx difft0 .
rewrite LieDerivative_derive => //=; last first.
  apply: differentiable_norm_squared => //=.
rewrite -derive1E /=.
rewrite fctE.
replace (fun x0 : K => norm (f (phi x x0)) ^+ 2)
  with ((1 \*o (GRing.exp (R:=K))^~ 2 \o norm) \o (f \o phi x)); last first.
  rewrite !fctE.
  rewrite -fctE.
  apply/funext => s.
  by rewrite /= /GRing.exp mul1r. 
rewrite derive_norm_squared => //=; last first.
  apply: diff_derivable=> //=.
  apply: differentiable_comp => //=.
rewrite mulrDl mul1r scalerDl scale1r mulmxDl.
by rewrite [in RHS]mxE.
Qed.

End LieDerivative.

(* not used, can be shown to be equivalent to LieDerivative *)
Definition LieDerivative_partial {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (a : R -> 'rV[R]_n.+1) (t : R) : R :=
  \sum_(i < n.+1) (partial V (a t) i * ('D_1 a t) ``_ i).

Section ode_equation.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.+1.

Variable phi : (K -> T) -> K -> T.

Definition solves_equation (x : K -> T) (A : set T) : Prop :=
   x 0 \in A  /\ (forall t, derivable x t (1:K)%R) /\ forall t, 'D_1 x t = phi x t.

Definition is_equilibrium_point x := solves_equation (cst x).

Definition equilibrium_points A := [set p : T | is_equilibrium_point p A ].

Definition state_space A :=
  [set p : T | exists y, solves_equation y A /\ exists t, p = y t ].

Definition equilibrium_is_stable_at
  (A : set T) (x : T) (z : K -> 'rV[K]_n.+1) :=
  forall eps, eps > 0 ->   
  exists2 d, d > 0 &
  (`| z 0 - x | < d -> forall t, t >= 0 -> `| z t - x | < eps).

(*Definition is_stable_equilibrium
  (A : set T) (x : T) :=
  forall z (solves_z : solves_equation z A), is_stable_equilibrium_at x solves_z.*)

(* a voir*)

Definition equilibrium_is_asymptotically_stable_at
  (A : set T) (x : T) (z : K -> 'rV[K]_n.+1) : Prop :=
    exists2 d, d > 0 &
      (`| z 0 - x | < d -> z t @[t --> +oo] --> x).
  
End ode_equation.
 (* axiom cauchy thm 3.3 *)

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
(* continuously differentiable*)
(* trajectory wise *)
Theorem Lyapunov_stability {K : realType} {n}
  (f :  (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
  (D : set 'rV[K]_n.+1)
  (sol :  'rV_n.+1 -> K -> 'rV[K]_n.+1)
  (x : 'rV[K]_n.+1 := 0)
  (fsolD : forall z, z \in D -> solves_equation f (sol z) D)
  (V : 'rV[K]_n.+1 -> K)
  (VDx : is_lyapunov_candidate V D x) (*contient l'hypothese x in D*)
  (V'le_0 : forall phi, solves_equation f phi D -> forall t, t >= 0 -> LieDerivative V sol (phi 0) t <= 0) 
  (Vderiv : forall t, differentiable V t)  :  
  is_equilibrium_point f x D ->
  equilibrium_is_stable_at D x (sol x).
Proof.
move => eq.
move => eps eps0.
rewrite /is_lyapunov_candidate in VDx.
move: VDx => [/= Vloc Vdiff].
move: Vloc => [/= inD [V0 [openD z1]]].
have init : forall x, sol x 0 = x. 
  by admit.
have : exists r : K, 0 < r /\ r <= eps /\ closed_ball_ (fun x => `|x|) (0:'rV[K]_n.+1) r `<=` D.
  rewrite inE in inD.
  have [r0 /= Hr0D] := open_subball openD inD.
  pose r := Num.min (r0 / 2) eps.
  have r_gt0 : 0 < r.
    rewrite /r /minr.
    case: ifPn => // _.
    by rewrite divr_gt0.
  move=> q.
  exists (r / 2).
  split.
    by rewrite divr_gt0.
  split.
    rewrite /r.
    rewrite /minr.
    case: ifPn.
      move/ltW; apply: le_trans.
      rewrite ler_pdivrMr//.
      by rewrite ler_peMr ?ler1n// divr_ge0// ltW.
    move=> _.
    rewrite ler_pdivrMr//.
    by rewrite ler_peMr ?ler1n// ltW.
  move=> v rv.
  apply (q r); last 2 first.
    by [].
    move: rv.
    rewrite -closed_ballE//; last first.
      by rewrite divr_gt0.
    by apply: subset_closure_half => //.
  rewrite /ball/=.
  rewrite sub0r normrN gtr0_norm// /r.
  rewrite gt_min.
  rewrite ltr_pdivrMr//.
  by rewrite ltr_pMr// ltr1n.
have Hcont := differentiable_continuous Vdiff.
move=> [r [r_pos [r_le_eps Br_sub_D]]].
pose sphere_r := [set x : 'rV[K]_n.+1 | `|x| = r].
have Halpha : {x : 'rV[K]_n.+1 | x \in sphere_r /\ forall y, y \in sphere_r -> V(x) <= V(y)}.
(* extreme value theorem?*)
(* sphere must be compact*)
  admit.    
pose alpha := V (sval Halpha).
have alpha_gt0 : 0 < alpha.
  have sphere_pos: forall y, y \in sphere_r -> 0 < V y.
    move=> y hy.
    apply: z1; last first.
      rewrite gtr0_norm_neq0 //.
      move: hy.
      by rewrite inE /sphere_r/= => ->.
    apply/mem_set.
    apply: Br_sub_D.
    rewrite /closed_ball_/= sub0r.
    move : hy.
    by rewrite inE /sphere_r/= normrN => ->.
  rewrite /alpha sphere_pos => //.
  rewrite /sphere_r inE/=.
  have Hsval := svalP Halpha.
  move: Hsval => [/= Hsphere _].
  move : Hsphere.
  rewrite inE.
  move => Hsphere.
  exact: Hsphere.
have: exists beta, 0 < beta < alpha.
  rewrite /=.
  exists (alpha / 2).
  rewrite divr_gt0 //=.
  rewrite ltr_pdivrMr => //=.
  rewrite mulr2n mulrDr mulr1.
  by rewrite ltrDl.
move=> [beta Hbeta].
set Omega_beta := [set x : 'rV[K]_n.+1 | (closed_ball_ [eta normr])``_r x /\ V x <= beta].
have HOmega_beta : Omega_beta `<=` interior (closed_ball_ [eta normr])``_r.
  rewrite /Omega_beta.
  move=> x1 [Hx mini].
  rewrite -closed_ballAE /=.
  rewrite interior_closed_ballE => //=.
  rewrite /Omega_beta /=.
  have Hnorm_le : `|x1| <= r.
    move : Hx.
    rewrite /closed_ball_ /ball. 
    under eq_fun do rewrite sub0r normrN.
    move => Hx.
    by apply: Hx.
  case: (ltgtP (`|x1|) r) => [Hlt | Heq | Hgt].
    by rewrite mx_norm_ball /ball_; under eq_fun do rewrite sub0r normrN; apply Hlt.
    exfalso.
    have Hrr : r < r by apply: (lt_le_trans Heq Hnorm_le).
      by move: Hrr; rewrite ltxx.
    have xin_sphere : x1 \in sphere_r. 
      rewrite /sphere_r inE.
      by apply: Hgt.
    have Vx_ge_alpha : alpha <= V x1.
      rewrite /alpha.
      case: (svalP Halpha) => [Hy_sphere Hy_min].
      apply: Hy_min.
      exact: xin_sphere.
    exfalso.
    move: mini Hbeta => HleVx [/andP [Hbeta_pos Hbeta_lt]].
    have : alpha <= V x1 <= beta.
      by apply/andP; split.
    have : alpha <= beta by apply: (le_trans Vx_ge_alpha HleVx).
      move=> Hle_alpha_beta alphavxbeta.
      have Hbb : beta < beta by apply: (lt_le_trans Hbeta_lt Hle_alpha_beta).
      by move : Hbb; rewrite ltxx.
    by exact: r_pos.
have uniqueness_of_solution : forall (phi1 phi2 : K -> 'rV_n.+1) (x0 : 'rV_n.+1),
    solves_equation f phi1 D ->
    solves_equation f phi2 D ->
    phi1 0 = x0 -> phi2 0 = x0 ->
    phi1 = phi2 by admit.
have H1 : forall phi , solves_equation f phi D -> phi 0 \in Omega_beta -> forall t, 0 <= t -> phi t \in Omega_beta.
  move => phi solves xOmega t t0.
have H2 : forall t, 0 <= t -> forall u, 0 <= u <= t -> LieDerivative V sol (phi 0) u <= 0 ->
  V (sol (phi 0) t) <= V (sol (phi 0) 0) <= beta.
(*  have H2 : forall t, t >= 0 -> LieDerivative V phi x t <= 0  -> V (sol x t) <= V (sol x 0) <= beta.*)
    move => t1 t10 u u10.
    have -> : phi = sol (phi 0). 
    apply: uniqueness_of_solution => //=.
    apply: fsolD => //.
    rewrite inE.
    apply: Br_sub_D => //.
    move : xOmega.
    rewrite inE /Omega_beta.
    by move => [H1 H2].
    rewrite !init /=.
    have Vneg_incr: forall s1 s2, 0 <= s1 <= s2 -> forall x, x \in D -> V (sol x s2) <= V (sol x s1).
      move=> s1 s2 Hs1_pos x2 xinD .
      apply: (@ler0_derive1_nincr _ (fun s => V (sol x2 s)) 0 s2) => //.
      - rewrite -fctE.
        move => x3 x1in.
        apply: diff_derivable.
        apply: differentiable_comp; last first.
        apply: differentiable_comp => //.
        
      (* continuity*)
          admit.
      - move=> s Hs_in.
    (* TODO *)
    (* LEMMA*)
        move :  (V'le_0 phi solves t t0).
        rewrite LieDerivative_derive => //=; last first.
           admit.
        rewrite derive1E.
        rewrite fctE.
        pose phi2 := (fun t => sol x2 t).
        have solves_phi2 : solves_equation f phi2 D by admit.
           have s_pos : 0 <= s. 
           by move: Hs_in; case/andP => /ltW.
        have deriv_le0 := V'le_0 phi2 solves_phi2 s s_pos.
        move => H.
        rewrite LieDerivative_derive /phi2 init in deriv_le0 => //.
          admit. 
          admit.
      - move: Hs1_pos => /andP [H0s1 Hs1s2].
        by apply: H0s1.
      - move: Hs1_pos => /andP [H0s1 Hs1s2].
      by apply: Hs1s2 => //=.
    have H3 : V (sol x t1) <= V (sol x 0).
      apply: Vneg_incr => //=.
      by apply/andP; split => //=.
      move => bla.
    apply/andP; split => //=.
    move : xOmega.
    rewrite inE /Omega_beta.
    move=> [clo Vxb].
    have Hdec := Vneg_incr 0 t1 _ (phi 0) _.
    rewrite init in Hdec.
    apply: Hdec => //=.
      by apply/andP; split => //.
    rewrite inE /Omega_beta.
    apply: Br_sub_D => //.
     move : xOmega.
    rewrite inE /Omega_beta.
    by move=> [clo Vxb].
  rewrite inE; split; last first.
   have t00 : 0 <= t <= t.
    apply/andP; split.
    by [].
    by [].
  have H_lie : LieDerivative V sol (phi 0) t <= 0.
    apply V'le_0.
    - exact solves.
    - exact t0.
  have V_bound := H2 t t0 t t00 H_lie.
  move : V_bound.
  rewrite !init.
  have -> : sol (phi 0) = phi.
  apply: uniqueness_of_solution => //.
  apply: fsolD => //.
 rewrite inE.
 apply: Br_sub_D => //.
 move : xOmega.
 rewrite inE /Omega_beta.
 by move => [h1 h2].
  case/andP => h1 h2.
  by apply: (le_trans h1 h2). 
  move: xOmega.
  rewrite inE /Omega_beta/=.
  rewrite /closed_ball_/=.
  rewrite !sub0r !normrN => -[] + Vxbeta.
  (* axiomatiser thm 3.3 *)
  move=> x0r.
  move : HOmega_beta.
  rewrite -closed_ballE /= => //.
  rewrite interior_closed_ballE => //.
  rewrite /Omega_beta.
  rewrite /closed_ball_.
  rewrite  mx_norm_ball /ball_.
  rewrite /= => /(_ (sol x t)).
  under eq_fun do rewrite !sub0r normrN.
  move => a.
   rewrite leNgt.
   apply/negP.
   have :  `|phi t| > r -> exists t0, t0 >=0 /\ `|phi t0 | = r.
   (* continuity, TVI *)
     by admit.
   move => cont solxr.
   have [t1 [t1_ge0 xt1r]] := cont solxr.
   have : alpha <= V (phi t1).
     rewrite {}/alpha in alpha_gt0 Hbeta *.
     move: Halpha alpha_gt0 Hbeta.
     case => alpha /= [alpha_gt0 +] Valpha_gt0 beta_alpha.
     apply.
     by rewrite inE /sphere_r/=.
   have H1 : V (phi t1) >= alpha.
     have sol_in_sphere : phi t1 \in sphere_r.
       rewrite inE.
       by rewrite /sphere_r.
     rewrite {}/alpha in alpha_gt0 Hbeta *.
     move: Halpha alpha_gt0 Hbeta.
     case => alpha /= [alpha_gt0 +] Valpha_gt0 beta_alpha.
     exact.
  have H3 : beta < V (phi t1).
    rewrite (lt_le_trans _ H1)//.
    by case/andP : Hbeta.
  have : V (phi t1) <= beta.
    have :  forall u, u >= 0 -> LieDerivative V sol (phi 0) u <= 0. 
      move => u u0.
      apply V'le_0.
    - exact solves.
    - exact u0.
    move : (H2 t1 t1_ge0).
    move=> Ht1 Hderiv.  
have Heq_sol_phi : sol (phi 0) = phi.
  apply: uniqueness_of_solution => //.
  apply : fsolD => //.
  rewrite inE.
  apply: Br_sub_D => //.
  rewrite /closed_ball_; under eq_fun do rewrite !sub0r normrN.
  by apply: x0r.
rewrite Heq_sol_phi in Ht1. 
have Vphi_le := Ht1 t1 _  _.
have t1_chain : 0 <= t1 <= t1.
 apply/andP ; split; [exact: t1_ge0 | exact: lexx].
move: (Vphi_le t1_chain (Hderiv t1 t1_ge0)) => [/andP [Vt1_le V0_le_beta]].
by apply: (le_trans Vt1_le).
  by rewrite leNgt H3.
have compact_Omega_beta : compact Omega_beta.
    rewrite /Omega_beta.
    (* use compact_closedI? *)
    apply: bounded_closed_compact.
    - rewrite /bounded_set /= /globally.
      exists r => //=.
      split => //=.
      move => x1 rx x2.
      rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
      move=> [/= x0_le_r ?].
      apply: le_trans x0_le_r _.
      exact: ltW rx.
    - apply: closedI.
        rewrite -closed_ballAE=> //=.
        by apply: closed_ball_closed => //=.
      rewrite /=.
      rewrite [X in closed X](_ : _ = V @^-1` [set x : K | x <= beta]); last first.
        by apply/seteqP; split.
      apply: closed_comp => //=.
      (* continuity*)
      admit.
have [delta0 Hdelta0] : exists d, d > 0 /\ forall x, `|x| <= d -> V x < beta. 
  rewrite /=.
  (* continuity*)
  admit.
pose delta := Num.min delta0 r.
have Hdelta : 0 < delta /\ (forall x, `|x| <= delta -> V x < beta).
  split.
    rewrite /delta /minr.
    case: (delta0 < r) => //=.
    exact: Hdelta0.1.
  rewrite /=.
  move => x1 xdel.
  move: Hdelta0 => [Hdelta0_pos Hdelta0_prop].
  have x_lt_delta0: `|x1| <= delta0.
    rewrite /delta /minr in xdel.
    apply: le_trans xdel _.  
    case: (delta0 < r) => //=.
    (* dont know, continuity?*)
    admit.
  by apply: Hdelta0_prop.
have inclusion :  (closed_ball_ [eta normr])``_delta  `<=` Omega_beta /\  Omega_beta `<=` (closed_ball_ [eta normr])``_r .
  split; last first => //=.
    apply: subset_trans HOmega_beta _.
    rewrite -closed_ballAE /=.
    rewrite interior_closed_ballE => //=.
    by apply: subset_closed_ball.
    by apply: r_pos.
  rewrite /Omega_beta.
  apply/subsetP => x1 Hx.
  rewrite inE.
  split; last first => //=.
    have [/= Hdelta_Le_Rpos Hdelta_bound] := Hdelta.
    move: Hx.
    rewrite inE.
    rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
    move => Hx.
    apply: ltW.
    by have Vx_lt_beta := Hdelta_bound _ Hx.
  rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
  have delta_le_r: delta <= r. 
    rewrite /delta.
    rewrite /minr.
    case: ifP => Hlt => //.
    by rewrite ltW.
  rewrite inE in Hx.
  move : Hx.
  rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
  move => Hball.
  move: Hball delta_le_r => /= Hx_lt_delta Hdelta_le_r.
  by apply: (le_trans (Hx_lt_delta) Hdelta_le_r).
have inclusion2 : ((closed_ball_ [eta normr])``_delta) (sol x  0) -> sol x 0 \in Omega_beta -> forall t, t >= 0 -> sol x t \in 
                   Omega_beta -> ((closed_ball_ [eta normr])``_r) (sol x t).
  move => ball0 sol0in t1 t2 soltin.
  by move: soltin; rewrite /Omega_beta inE => [] [Hball _].
rewrite /x !subr0.
have Hlast : `|sol x 0| < delta -> forall t : K , t >=0 -> `|sol x t| < r <= eps.
  move => sol0delta t1 t2.
  case: inclusion => [Hin_ball_delta _]. 
  have sol_in_Omega : sol x 0 \in Omega_beta. 
    rewrite inE.
    apply: Hin_ball_delta.
    rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN; apply/ltW; exact: sol0delta.
  rewrite /Omega_beta inE in sol_in_Omega.
  case: sol_in_Omega => [Hball_solt _].
  move : Hball_solt.
  rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
  move =>  Hball_solt.
  have : ((closed_ball_ [eta normr])``_r)° (sol x t1).
    apply: ( HOmega_beta).
    rewrite -inE.
    have xinO : sol x 0 \in Omega_beta.
      rewrite inE.
      rewrite /Omega_beta.
      split => //=.
        rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
        exact: Hball_solt. 
        have x00 : sol x 0 = x by rewrite init => //=.
        have z0_in_ball : (closed_ball_ [eta normr])``_delta (sol x 0).
          rewrite /closed_ball_; apply: ltW. 
          rewrite sub0r normrN.
          by apply: sol0delta.
        move : (Hin_ball_delta _ z0_in_ball).
        by move => [clo Vxb].
    apply: H1 => //.
    by apply: fsolD => //.
  rewrite -closed_ballAE => //=.
  rewrite interior_closed_ballE => //=.
  rewrite mx_norm_ball /ball_; under eq_fun do rewrite sub0r normrN.
  move => etc.
  by apply/andP; split => //.
exists delta.
  by case: Hdelta.
move=> x0_lt_delta t0 t0_ge0.
rewrite /x subr0.
(* sol? z ?*)
have Htraj0 : `|sol x t0| < r.
  rewrite /Omega_beta.
  have x0_in_Omega : x \in Omega_beta.
    rewrite inE.
    apply: inclusion.1.
    rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
    apply: ltW.
    rewrite /x.
    rewrite init in x0_lt_delta.
    by apply: x0_lt_delta.
  have sol_in_Omega : sol x t0 \in Omega_beta.
    apply: H1 => //=.
    by apply: fsolD => //.
    rewrite init.
    exact: x0_in_Omega; exact: t0_ge0.
  rewrite /Omega_beta inE in sol_in_Omega.
  case: sol_in_Omega => Hnorm _.
  move : Hnorm.
  rewrite /closed_ball_; under eq_fun do rewrite sub0r normrN.
  move => Hnorm.
  have traj_in_Omega : sol x t0 \in Omega_beta.
    apply: H1 => //.
    apply: fsolD => //.
    by rewrite init.
  have in_interior: ((closed_ball_ [eta normr])``_r)° (sol x t0).
    apply: HOmega_beta. 
    rewrite -inE.
    exact: traj_in_Omega.
  move: in_interior.
  rewrite -closed_ballE /=.
  rewrite interior_closed_ballE => //=.
  rewrite mx_norm_ball /ball_; under eq_fun do rewrite sub0r normrN.
  apply => //=.
  exact : r_pos.
rewrite init in x0_lt_delta.
by apply: (lt_le_trans Htraj0 r_le_eps).

Admitted.

Theorem Lyapunov_asymptotic_stability {K : realType} {n}
   (f :  (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
  (D : set 'rV[K]_n.+1)
  (sol :  'rV_n.+1 -> K -> 'rV[K]_n.+1)
  (x : 'rV[K]_n.+1 := 0)
  (fsolD : forall z, z \in D -> solves_equation f (sol z) D)
  (V : 'rV[K]_n.+1 -> K)
  (VDx : is_lyapunov_candidate V D x) (*contient l'hypothese x in D*)
  (V'le_0 : forall phi, solves_equation f phi D -> forall t, t >= 0 -> LieDerivative V sol (phi 0) t <= 0) 
  (Vderiv : forall t, differentiable V t)  :  
  is_equilibrium_point f x D ->
  equilibrium_is_asymptotically_stable_at D x (sol x).
Proof.
move => eq.

Admitted.
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
  solves_equation (fun y t => equa_f e (y t)) y1 A /\
  (y1 (equa_t0 e) \in equa_S0 e ->
    (forall t, t > 0 -> y1  (equa_t0 e + t) \in equa_S0 e)). (*TODO*)

Section ya.
(* mesure de l'accelerometre *)
Variable K : realType.
Variable v : K -> 'rV[K]_3. (* local frame of the sensor *)
Variable R : K -> 'M[K]_3. (*L -> W*)
Variable g0 : K. (*standard gravity constant*)
Let w t := ang_vel R t. (* local frame of the sensor (gyroscope) *)
Let x1 t :=  v t. (* local frame*)
Definition x2 t : 'rV_3 := 'e_2 *m R t. (* tilt in local frame, e2 is in global frame but R brings it back*)
Definition y_a t := - x1 t *m \S( w t) + 'D_1 x1 t + g0 *: x2 t. (* local frame of the sensor*)
Variable p : K -> 'rV[K]_3.
Let v1 := fun t : K => 'D_1 p t *m R t.
Definition y_a1 t := - v1 t *m \S( w t)+ 'D_1 v1 t + g0 *: x2 t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.


Lemma y_aE t : ('D_1 ('D_1 p) t + g0 *: 'e_2) *m R t= y_a1 t .
Proof.
rewrite mulmxDl.
rewrite /y_a1/= /v1 /= /x2.
congr +%R; last by rewrite scalemxAl.
rewrite -ang_vel_mxE/=; last 2 first.
   move=> t0.
   rewrite rotation_sub //.
   admit.
rewrite [in RHS]derive_mulmx; [|admit|admit].
rewrite derive1mx_ang_vel//; [|admit|admit].
rewrite ang_vel_mxE//; [|admit|admit].
rewrite addrCA.
rewrite -mulmxE.
rewrite -mulNmx.
rewrite [X in _ = _ X]addrC.
rewrite !mulNmx.
by rewrite -mulmxA /= addrN addr0.
Admitted.

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
Let x2 t : 'rV_3 := ('e_2) *m R t (* eqn (8) *).
Let x1_point t := 'D_1 x1 t.
Let x2_point t := 'D_1 x2 t.
Let w t := ang_vel R t.

Lemma x2_s2 (t0 : K) : x2 t0 \in S2.
Proof.
rewrite /S2 /x2 /=.
rewrite inE /= orth_preserves_norm.
  by rewrite normeE.
by rewrite rotation_sub // rotationV.
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
Admitted.

(* eqn 10*)
Notation y_a := (y_a v R g0).
Lemma derive_x1 t : 'D_1 x1 t = x1 t *m \S(w t) + y_a t - g0 *: x2 t.
Proof.
rewrite /y_a/= -addrA addrK.
rewrite /x1.
rewrite addrCA addrA mulNmx /= /w.
by rewrite (addrC(-_)) subrr add0r.
Qed.

 (* eqn 11b *)
Lemma derive_x2 (t : K) : x2_point t = x2 t *m \S( w t ).
Proof.
rewrite /w.
rewrite -ang_vel_mxE; last 2 first.
  by move=> ?; rewrite rotation_sub.
  by [].
rewrite /x2_point.
rewrite /x2.
have ->: 'D_1 (fun t0 : K => 'e_2 *m (R t0)) t = ('e_2 *m 'D_1 (fun t => (R t)) t).
  move => n.
  rewrite /=.
  rewrite derive_mulmx//=; last first.
  by rewrite derive_cst mul0mx add0r.
rewrite /=.
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
Let x2'hat t := -(alpha1 / g0) *: (x1 t - x1_hat t). (* 12b*)
Hypothesis eq12a : forall t, 'D_1 x1_hat t = x1_hat t *m \S(w t) + y_a t - g0 *: x2'hat t.
Hypothesis eq12c : forall t, 'D_1 x2_hat t = x2_hat t *m \S(w t - gamma *: x2'hat t *m \S(x2_hat t)). (*12c*)
Hypothesis x2_hat_S2 : x2_hat 0 \in S2.
Hypothesis x2_hat_derivable : forall t, derivable x2_hat t 1.
Hypothesis v_derivable : forall t, derivable v t 1.
Notation x2 := (x2 R).
Let p1 t := x2 t - x2'hat t. 
Let x2_tilde t :=  x2 t - x2_hat t.
Let p1_point t := 'D_1 p1 t.
Let x2_tilde_point t := 'D_1 x2_tilde t.
Hypothesis RisSO : forall t, R t \is 'SO[K]_3.
Let zp1 t := p1 t *m (R t)^T.
Let z2 t := x2_tilde t *m (R t)^T.  
Hypothesis norm_x2_hat : forall t, norm (x2_hat t) = 1.

Let p1E : p1 = fun t => x2 t + (alpha1 / g0) *: (x1 t - x1_hat t).
Proof.
apply/funext => ?.
rewrite /p1 /x2; congr +%R.
by rewrite /x2'hat scaleNr opprK.
Qed.

Let x2_tildeE t : x2_tilde t = z2 t *m R t.
Proof.
rewrite /z2 -mulmxA.
by rewrite orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

Let derivable_x2 t : derivable x2 t 1. Proof. exact: derivable_mulmx. Qed.

Let derivable_x2'hat t : derivable x2'hat t 1.
Proof. by apply: derivableZ => /=; exact: derivableB. Qed.

Let derivable_p1 t : derivable p1 t 1. Proof. exact: derivableB. Qed.

Let derivable_x2_tilde t : derivable x2_tilde t 1. Proof. exact: derivableB. Qed.

Lemma derive_p1 t : 'D_1 p1 t = p1 t *m \S(w t) - alpha1 *: p1 t.
Proof.
simpl in *.
rewrite p1E.
rewrite deriveD//=; last first.
  by apply: derivableZ => /=; exact: derivableB.
rewrite deriveZ//=; last exact: derivableB.
rewrite deriveB//.
rewrite !(derive_x2) // -/(x2 t) /=.
rewrite (derive_x1  g0 R) //.
rewrite -/(x2 t) -/(v t) -/(x1 t) -/(w t).
rewrite eq12a.
transitivity ((x2 t + (alpha1 / g0) *: (x1 t - x1_hat t)) *m \S(w t) - alpha1 *: p1 t).
  transitivity (x2 t *m \S(w t) + (alpha1 / g0) *: (x1 t *m \S(w t) - g0 *: x2 t - (x1_hat t *m \S(w t) - g0 *: x2'hat t))).
    do 2 f_equal.  
    rewrite -3![in LHS]addrA -[in RHS]addrA.
    congr +%R.
    rewrite opprD addrCA.
    rewrite [in RHS]opprB [in RHS]addrA [in RHS]addrC.
    congr +%R.
    by rewrite opprD addrACA subrr add0r opprK.
  rewrite (_ : x1 t *m \S(w t) - g0 *: x2 t - (x1_hat t *m \S(w t) - g0 *: x2'hat t) =
               (x1 t - x1_hat t) *m \S(w t) - g0 *: (x2 t - x2'hat t)); last first.
    rewrite mulmxBl scalerDr scalerN opprB addrA [LHS]addrC 2!addrA.
    rewrite -addrA; congr +%R.
      by rewrite addrC.
    by rewrite opprB addrC.
  rewrite -/(p1 t).
  rewrite scalerDr addrA scalemxAl -mulmxDl scalerN scalerA.
  by rewrite divfK.
by rewrite p1E.
Qed.

Lemma derive_x2tilde t : 'D_1 x2_tilde t = x2_tilde t *m \S( w t) - gamma *: (x2_tilde t - p1 t) *m \S( x2_hat t ) ^+ 2 .
Proof.
rewrite /x2_tilde.
rewrite [in LHS]deriveB//.
rewrite derive_x2//.
rewrite -/(x2 t) -/(w t) -/(x2_tilde t).
rewrite eq12c.
rewrite spinD spinN -scalemxAl (spinZ gamma).
rewrite mulmxBr opprB [LHS]addrA [in LHS]addrC addrA (addrC _ (x2 t *m \S(w t))).
rewrite -mulmxBl -/(x2_tilde t).
congr +%R.
rewrite -scalemxAr -mulNmx -scalerN -[RHS]scalemxAl.
congr (_ *: _).
rewrite /x2_tilde /p1.
rewrite (opprB _ (x2'hat t)) -addrA (addrC (x2 t)) addrA subrK opprD opprK mulmxBl.
rewrite [X in _ = X + _](_ : _ = 0) ?add0r; last first.
  rewrite mulmxA.
  rewrite -(mulmxA(x2_hat t)) sqr_spin //.
  rewrite mulmxDr !mulmxA.
  rewrite dotmul1 // mul1mx.
  by rewrite mulmxN mulmx1 subrr.
rewrite expr2 -mulmxE fact215 -mulmxE -spin_crossmul.
rewrite [in RHS]mulmxA [in RHS]spinE spinE spinE.
by rewrite [LHS](@lieC _ (vec3 K))/=.
Qed.

Lemma Rx2 t : x2_hat t *m (R t)^T = 'e_2 - z2 t.
Proof.
rewrite /z2 /x2_tilde mulmxBl opprB addrCA.
rewrite [X in _ + X](_ : _ = 0) ?addr0//.
rewrite /x2 -mulmxA.
by rewrite orthogonal_mul_tr ?rotation_sub// mulmx1 subrr.
Qed.

Lemma derive_zp1t t : 'D_1 zp1 t = -alpha1 *: zp1 t.
Proof.
rewrite /zp1.
rewrite derive_mulmx//=; last by rewrite derivable_trmx.
rewrite derive_p1.
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

Lemma derive_z2t t : 'D_1 z2 t = gamma *: (z2 t - zp1 t) *m - \S('e_2 -z2 t)^+2.
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
rewrite derive_x2tilde /=.
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
rewrite x2_tildeE.
rewrite mulmxBl; congr (_ - _)%R.
by rewrite /zp1 -mulmxA orthogonal_tr_mul ?rotation_sub// mulmx1.
Qed.

(* TODO relier derivezp1 et derivez2 a eqn33?*)
(* TODO see about thm11a and the rest*)

End problem_statementB.

Section eqn33.
Variable K : realType.
Variable alpha1 : K.
Variable gamma : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.
Definition state_space_tilt {K : realType} := [set x : 'rV[K]_6 | norm ('e_2 - Right x) = 1].

Definition tilt_eqn (zp1_z2_point : K -> 'rV[K]_6) : K ->'rV[K]_6 :=
  let zp1_point := Left \o zp1_z2_point in
  let z2_point := Right \o zp1_z2_point in
  fun t => row_mx (- alpha1 *: zp1_point t)
         (gamma *: (z2_point t - zp1_point t) *m \S('e_2%:R - z2_point t) ^+ 2).

(* TODO: use tilt_eqn *)
Definition eqn33' (zp1_z2_point : 'rV[K]_6) : 'rV[K]_6 :=
  let zp1_point := Left zp1_z2_point in
  let z2_point := Right zp1_z2_point in
  row_mx (- alpha1 *: zp1_point)
         (gamma *: (z2_point - zp1_point) *m \S('e_2%:R - z2_point) ^+ 2).

(*Lemma eqn33E t : eqn33 y0 t = eqn33' (y0 t). Proof. by []. Qed.*)

Lemma eqn33'_lipschitz : exists k, k.-lipschitz_setT eqn33'.
Proof.
near (pinfty_nbhs K) => k.
exists k => -[/= x x0] _.
rewrite /eqn33'.
set fx := row_mx (- alpha1 *: Left x)
                  (gamma *: (Right x - Left x) *m \S('e_2 - Right x) ^+ 2).
set fy := row_mx (- alpha1 *: Left x0)
                  (gamma *: (Right x0 - Left x0) *m \S('e_2 - Right x0) ^+ 2).
rewrite /Num.norm/=.
rewrite !mx_normrE.
apply: bigmax_le => /=.
  rewrite mulr_ge0//.
  apply: le_trans; last first.
    apply: (le_bigmax _ _ (ord0, ord0)) => //.
  by [].
move=> -[a b] _.
rewrite /=.
rewrite [leRHS](_ : _ = \big[maxr/0]_ij (maxr alpha1 gamma * `|(x - x0) ij.1 ij.2|)); last first.
  admit.
rewrite (le_trans (@ler_peMl _ (maxr alpha1 gamma) _ _ _))//.
  admit.
apply: le_trans; last first.
  exact: (@le_bigmax _ _ _ 0 (fun ij => maxr alpha1 gamma * `|(x - x0) ij.1 ij.2|) (a, b)).
rewrite /=.
apply: (@le_trans _ _ (`|(maxr alpha1 gamma *: fx - maxr alpha1 gamma *: fy) a b|)).
  admit.
apply: (@le_trans _ _ (`|maxr alpha1 gamma *: x a b - maxr alpha1 gamma *: x0 a b|)); last first.
Abort.

(* cauchy lipschitz par F1 qui definit un champ de vecteur lisse :
il existe une solution depuis tout point:
gamma1 ⊆ state_space*)
(* prouver invariance geometrique, tangence donc les trajectoires restent dans gamma1:
 state_space ⊆ gamma1
*)

Lemma invariant_state_space_tilt p (p33 : state_space tilt_eqn state_space_tilt p) :
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

Lemma thm11a : state_space tilt_eqn state_space_tilt = state_space_tilt .
Proof.
apply/seteqP; split.
- move=> p [y [[y0_init1]] [deri] y33 ] [t ->].
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
      have -> : ('D_1 (fun x2 : K => 'e_2 - Right (y x2)) x)
            = - (Right ('D_1 y x)).
        rewrite deriveB /= ; last 2 first.
          exact: derivable_cst.
          by apply: derivable_rsubmx.
        rewrite derive_cst /= sub0r; congr (-_).
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
- move=> p.
  rewrite /state_space_tilt /=.
  move=> p_statespace33.
  rewrite /state_space /=.
  rewrite /solves_equation /=.
  exists (fun _ : K => 0).
  split.
  split.
  by rewrite inE /= rsubmx_const subr0 normeE.
  split.
  apply: derivable_cst => //.
  move => t.
  rewrite /tilt_eqn /= derive_cst.
  apply /eqP; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
  split.
  apply/eqP.
  have alpha1_neq0 : alpha1 != 0 by rewrite gt_eqF.
  apply/eqP.
  rewrite scaler_eq0 //.
  rewrite eqr_oppLR oppr0.
  move/negbTE: alpha1_neq0 => alpha1_nz.
  rewrite alpha1_nz // Bool.orb_false_l.
  by rewrite lsubmx_const.
  by rewrite lsubmx_const rsubmx_const subr0 scaler0 mul0mx.
  admit. (* NG *)
Admitted.

Definition point1 : 'rV[K]_6 := 0.
Definition point2 : 'rV[K]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2).

Lemma equilibrium_point1 : is_equilibrium_point tilt_eqn point1 state_space_tilt.
Proof.
split => //=.
  rewrite inE /state_space_tilt /point1.
  rewrite /=.
  by rewrite rsubmx_const /= subr0 normeE.
split => //=.
move=> t ; rewrite derive_cst /tilt_eqn /point1; apply/eqP.
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
  rewrite inE /state_space_tilt /point2 /=.
  rewrite row_mxKr.
  rewrite -[X in X - _ ]scale1r.
  rewrite -scalerBl normZ normeE mulr1 distrC.
  rewrite [X in _ - X](_:1 = 1%:R) //.
  by rewrite -natrB //= normr1.
split => //.
move => t. rewrite derive_cst; apply /eqP; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
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

(* this lemma asks for lyapunov + lasalle *)
Lemma tractories_converge (y : K -> 'rV[K]_6) : solves_equation tilt_eqn y state_space_tilt ->
  y t @[t --> +oo] --> point1 \/ y t @[t --> +oo] --> point2.
Proof.
move=> is_sol_y.
Abort.

End eqn33.
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

Lemma defposmxu2 : defposmx u2.
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
Variable alpha1 : K.
Variable gamma : K.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.

Definition V1 (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in 
  let z2 := Right zp1_z2 in
  (norm zp1)^+2 / (2 * alpha1) + (norm z2)^+2 / (2 * gamma).

Lemma V1_is_lyapunov_candidate : is_lyapunov_candidate V1 setT point1.
Proof.
rewrite /locposdef; split.
- rewrite /V1 /point1 /locposdef; split. 
  by rewrite inE.
  rewrite lsubmx_const rsubmx_const norm0 expr0n/= !mul0r add0r.
  split.
  by [].
  split.
  exact: openT.
  move => z_near _ z0.
  have /orP[lz0|rz0] : (Left z_near != 0) || (Right z_near != 0).
  + rewrite -negb_and.
    apply: contra z0 => /andP[/eqP l0 /eqP r0].
    rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
    by apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?; rewrite mxE.
  + set rsub := Right z_near.
    have : norm rsub >= 0 by rewrite norm_ge0.
    set lsub := Left z_near.
    move => nor.
    have normlsub : norm lsub > 0 by rewrite norm_gt0.
    rewrite ltr_pwDl//.
      by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
    by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
  - rewrite ltr_pwDr//.
      by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0// norm_gt0.
    by rewrite divr_ge0 ?exprn_ge0 ?norm_ge0// mulr_ge0// ltW.
  - rewrite /V1.
    rewrite -fctE.
    apply/differentiableD => //; last first.
    apply/differentiableM => //.
    apply/differentiable_norm_squared => //=.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_rsubmx => //.
    apply/differentiableM => //.
    apply/differentiable_norm_squared => //=.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_lsubmx => //.
Unshelve. all: by end_near. Qed.

Definition V1dot (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Left zp1_z2 in
  let z2 := Right zp1_z2 in
  - (norm zp1)^+2 + (z2 *m (\S('e_2 - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2 - z2))^+2 *m zp1^T)``_0.

End V1.

Section Lyapunov.
Local Open Scope classical_set_scope.
Context {K : realType}.
Variable alpha1 : K.
Variable gamma : K.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.
Variable R : K -> 'M[K]_3.
(*Variable y0 : K -> 'rV[K]_6.
Hypothesis y0init: y0 0 \in state_space_tilt.
Hypothesis y0sol : solves_equation (tilt_eqn alpha1 gamma) y0 state_space_tilt.*)

Lemma derive_zp1 (z : K) (traj : K -> 'rV_6) : solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt -> 'D_1 (Left \o traj) z = - alpha1 *: Left (traj z).
Proof.
move=> [/= traj0].
case.
move => dtraj.
move=> /(_ z)/(congr1 Left).
by rewrite row_mxKl => ?; rewrite derive_lsubmx//=.
Qed.

Lemma derive_z2  (z : K) (traj : K -> 'rV_6) : solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
   'D_1 (Right \o traj) z =
   gamma *: (Right (traj z) - Left (traj z)) *m \S('e_2 - Right (traj z)) ^+ 2.
Proof.
move=> [/= traj0][dtraj].
by move => /(_ z)/(congr1 Right); rewrite row_mxKr => ?; rewrite derive_rsubmx//=.
Qed.

Let c1 := 2^-1 / alpha1.
Let c2 := 2^-1 / gamma.

Lemma derive_V1dot (z : K) (traj : K -> 'rV_6)
  (zp1 := Left \o traj) (z2 := Right \o traj) :
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
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

Lemma Gamma1_traj (y : K -> 'rV_6) t :
  solves_equation (tilt_eqn alpha1 gamma) y state_space_tilt -> state_space_tilt (y t).
Proof.
move=> iss.
case: iss.
move=> y033 [dy deriv_y].
rewrite -(@thm11a _ _ _ gamma_gt0 alpha1_gt0)//=.
exists y; split => //.
by exists t.
Qed.

Lemma norm_u1 (traj : K -> 'rV_6) (z : K) (z2 := Right \o traj)
    (zp1 := Left \o traj)  (u := 'e_2 - z2 z) :
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt -> norm u = 1.
Proof.
move=> dtraj.
suff: state_space_tilt (row_mx (zp1 z) (z2 z)) by rewrite /state_space_tilt/= row_mxKr.
rewrite /zp1 /z2 hsubmxK /=.
by apply:Gamma1_traj.
Qed.

Lemma deriveV1 (x : K -> 'rV[K]_6) t :
 solves_equation (tilt_eqn alpha1 gamma) x state_space_tilt -> (forall t, differentiable x t) ->  
 LieDerivative (V1 alpha1 gamma) (fun a => x) 0 t = V1dot (x t).
Proof.
rewrite /tilt_eqn.
move=> tilt_eqnx dif1.
rewrite /V1.
rewrite LieDerivativeD; last 3 first.
  apply/differentiableM => //=.
  apply/differentiable_norm_squared => //.
  rewrite /tilt_eqn.
  exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
  by apply: differentiable_lsubmx.
  apply/differentiableM => //=.
  apply/differentiable_norm_squared => //=. 
  exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
  apply/differentiable_rsubmx => //.
  by [].
under [X in LieDerivative X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _ _]eq_fun do rewrite mulrC.
rewrite LieDerivativeMl => //; last first.
  apply/differentiable_norm_squared.
  exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).  
  apply/differentiable_lsubmx => //.
rewrite LieDerivativeMl => //; last first.
  apply/differentiable_norm_squared => //=.
  exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_rsubmx => //.
rewrite -fctE /=.
rewrite !LieDerivative_norm /=; last 6 first.
  apply/differentiable_rsubmx => //.
  apply (dif1 t).
  move => t0.
  apply/differentiable_rsubmx => //.
  apply/differentiable_lsubmx => //.
  apply (dif1 t).
  move => t0.
  apply/differentiable_lsubmx => //.
  rewrite -derive_V1dot.
  rewrite /c1 /c2.
  by rewrite !invfM.
  by [].
Qed.

(* TODO: Section general properties of our system *)

Lemma angvel_sqr (traj : K -> 'rV_6) (z : K)  (z2 := fun r : K => Right (traj r) : 'rV_3)
  (w := (z2 z) *m \S('e_2)) (u := 'e_2 - z2 z) :
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
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
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  norm (Right (traj z) *m \S('e_2) *m - \S('e_2 - Right (traj z))) =
  norm (Right (traj z) *m \S('e_2)).
Proof.
move=> dtraj.
rewrite mulmxN normN.
pose zp1 := fun r => Left (traj r).
pose z2 := fun r => Right (traj r).
set w := (z2 z) *m \S('e_2).
have Gamma1_traj t : state_space_tilt (traj t) by apply/Gamma1_traj.
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

Lemma V1dot_ub (traj : K -> 'rV_6) (z : K) (zp1 := Left \o traj) (z2 := Right \o traj)
  (w := z2 z *m \S('e_2))
  (u1 : 'rV[K]_2 := \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i) :
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  V1dot (traj z) <= (- u1 *m u2 *m u1^T) 0 0.
Proof.
move=> dtraj.
rewrite mxE.
rewrite /V1dot.
rewrite mxE norm_spin mxE addrA expr2 mulmxA.
have -> : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2).
  by rewrite spinD spinN -tr_spin !mulmxDr !mul_tr_spin !addr0.
rewrite -/w -dotmulNv addrC -mulmxN -expr2.
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
rewrite !sum2E/= ![in leRHS]mxE !sum2E/= ![in leRHS]mxE /=.
rewrite !mulr1 mulrN mulNr opprK mulrDl mulNr -expr2.
rewrite [in leLHS] addrCA -!addrA lerD2l mulrDl (mulNr (norm w)).
rewrite -expr2 !addrA lerD2r !(mulrN , mulNr) opprK -mulrA.
rewrite [in leRHS](mulrC (_ / 2)) (mulrC 2^-1) -mulrDr -splitr.
by rewrite [leRHS]mulrC.
Qed.

(* TODO: rework of this proof is needed *)
Lemma near0_le0 (traj : K -> 'rV_6) :
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  traj 0 = point1 ->
  \forall z \near 0^',
    (LieDerivative (fun x => norm (Left x) ^+ 2 / (2 * alpha1)) (fun a=> traj) 0  +
     LieDerivative (fun x => norm (Right x) ^+ 2 / (2 * gamma)) (fun a => traj) 0) z <= 0.
Proof.
move=> dtraj traj0.
rewrite fctE !invfM /=.
near=> z.
under [X in LieDerivative X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _ _]eq_fun do rewrite mulrC.
move: dtraj => [H0 [Hderiv Htilt]].
have Hz_derivable : derivable traj z 1.
  by apply: Hderiv.
rewrite LieDerivativeMl; last first.
  by apply derivable1_diffP.
  apply/differentiable_norm_squared => //=; last first.
    (* en temps superieur a zero?*)
    apply/differentiable_lsubmx => //.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
rewrite LieDerivativeMl; last first.
  by apply derivable1_diffP.
apply/differentiable_norm_squared; last first.
  apply/differentiable_rsubmx => //.
  exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
rewrite /= !LieDerivative_norm; last 6 first.
  by apply/differentiable_rsubmx => //.
  by apply/derivable1_diffP => //.
  move => t.
  apply/differentiable_rsubmx => //.
  apply/differentiable_lsubmx => //.
   by apply/derivable1_diffP => //.
  move => t.
  apply/differentiable_lsubmx => //.
rewrite derive_V1dot //.
pose zp1 := Left \o traj.
pose z2 := Right \o traj.
set w := (z2 z) *m \S('e_2).
pose u1 : 'rV[K]_2 := \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i.
apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
  by rewrite V1dot_ub.
have := @defposmxu2 K.
rewrite defposmxP => def.
have [->|H] := eqVneq u1 0.
  by rewrite mulNmx mul0mx mulNmx mul0mx mxE mxE oppr0.
have Hpos := def u1 H.
rewrite -oppr_ge0 -oppr_le0 opprK ltW//.
by rewrite -oppr_gt0 mulNmx !mulNmx mxE opprK Hpos.
Unshelve. all: try by end_near. 
Qed.

Lemma V1_point_is_lnsd (y : K -> 'rV_6) :
  solves_equation (tilt_eqn alpha1 gamma) y state_space_tilt->
  y 0 = point1 ->
  locnegsemidef (LieDerivative (V1 alpha1 gamma) (fun a => y) 0 ) 0.
Proof.
move=> [y033] [dy dtraj] traj0.
have Gamma1_traj t : state_space_tilt (y t).
  apply/Gamma1_traj.
  by split => //.
rewrite /locnegsemidef /V1.
rewrite LieDerivativeD /=; last 3 first.
  apply: differentiableM; last 2 first.
    rewrite /=.
    apply: differentiable_norm_squared; last 2 first.
      exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
      apply/differentiable_lsubmx => //.
    apply: differentiable_cst; last first.
      apply: differentiableM; last 2 first.
      apply: differentiable_norm_squared=> //.
        exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
        apply/differentiable_rsubmx => //.
    apply: differentiable_cst.
    by apply derivable1_diffP.
split; last first.
  admit.
under [X in LieDerivative X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _ _]eq_fun do rewrite mulrC.
rewrite LieDerivativeMl; last first.
  by apply derivable1_diffP.
  apply/differentiable_norm_squared; last 2 first.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_lsubmx => //.
rewrite LieDerivativeMl; last first.
 by apply derivable1_diffP.
 apply/differentiable_norm_squared; last first.
 apply/differentiable_rsubmx => //.
 exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
rewrite /= !derivative_LieDerivative_eq0; last 4 first.
  apply/differentiable_norm_squared; last first.
   apply/differentiable_rsubmx => //.
   exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
    apply/differentiable_norm_squared; last first.
    apply/differentiable_lsubmx => //.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
by rewrite scaler0 scaler0 add0r.
Admitted.

Lemma V1_point_is_lnd (y : K -> 'rV_6) 
   (z : K)
   (zp1 := Left \o y) (z2 := Right \o y)
  (w := z2 z *m \S('e_2))
  (u1: 'rV[K]_2 := 
     \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i ) :
  u1 != 0 ->
  solves_equation (tilt_eqn alpha1 gamma) y state_space_tilt->
  y 0 = point1 ->
  lnd (LieDerivative (V1 alpha1 gamma) (fun a => y) 0 ) 0.
Proof.
move=> neq0 [y033] [dy dtraj] traj0.
have Gamma1_traj t : state_space_tilt (y t).
  apply/Gamma1_traj.
  by split => //.
rewrite /lnd.
split; last first.
near=> z0.
rewrite deriveV1.
have Hle : V1dot (y z) <= (- u1 *m u2 *m u1^T) 0 0.
  by apply: V1dot_ub.
have := @defposmxu2 K.
rewrite defposmxP => def.
have Hpos : 0 <  (u1 *m u2 *m u1^T) 0 0  by apply: def.
have Hneg : -  (u1 *m u2 *m u1^T) 0 0 < 0. by rewrite oppr_lt0.
rewrite lt_neqAle.
have sol : solves_equation (tilt_eqn alpha1 gamma) y state_space_tilt by split => //.
apply/andP; split; last first.
    apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
    have Hle_z0 : V1dot (y z0) <= (- u1 *m u2 *m u1^T) 0 0.
    replace z0 with z; last by admit.
    by [].
    admit.
have -> : (- u1 *m u2 *m u1^T) 0 0 = - (u1 *m u2 *m u1^T) 0 0.
  rewrite !mxE -sumrN.
  under [in RHS]eq_bigr do rewrite -mulNr.
  under eq_bigr do rewrite mulNmx.
  admit.
  by apply/ltW => //.
  replace z0 with z.
  admit.
  admit.
by [].
move => t.
apply/derivable1_diffP => //.
rewrite /V1.
rewrite !invfM /=.
rewrite LieDerivativeD /=; last 2 first.
  apply: differentiableM; last 2 first.
    rewrite /=.
    apply: differentiable_norm_squared; last 2 first.
      exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
      apply/differentiable_rsubmx => //.
    apply: differentiable_cst; last first.
      by apply derivable1_diffP.
under [X in LieDerivative X _ _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _ _]eq_fun do rewrite mulrC.
rewrite LieDerivativeMl; last first.
  by apply derivable1_diffP.
  apply/differentiable_norm_squared; last 2 first.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_lsubmx => //.
rewrite LieDerivativeMl; last first.
 by apply derivable1_diffP.
 apply/differentiable_norm_squared; last first.
   apply/differentiable_rsubmx => //.
     exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
rewrite /= !derivative_LieDerivative_eq0; last 4 first.
   apply/differentiable_norm_squared; last 2 first.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_rsubmx => //.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
   apply/differentiable_norm_squared; last 2 first.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_lsubmx => //.
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
by rewrite scaler0 scaler0 add0r.
apply/differentiableM.
apply/differentiable_norm_squared; last 2 first.
    exact (fun z => gamma *: ((Right z - Left z) *m \S('e_2 - Right z) ^+ 2)).
    apply/differentiable_lsubmx => //.
by apply: differentiable_cst.
Unshelve. all: by end_near. 
Admitted.





Definition is_lyapunov_stable_at {K : realType} {n}
  (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
  (A : set 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> K)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0 A,
      is_lyapunov_candidate V setT x0 &
      forall traj1 traj2 : (K -> 'rV[K]_n.+1),
        solves_equation f traj1 A ->
        traj1 0 = x0 ->
        locnegsemidef (LieDerivative V (fun a => traj1) 0 ) 0].
Lemma V1_is_lyapunov_stable :
  is_lyapunov_stable_at (tilt_eqn alpha1 gamma) state_space_tilt (V1 alpha1 gamma) point1.
Proof.
split.
- by apply: equilibrium_point1 => //.
- exact: V1_is_lyapunov_candidate.
- move=> traj1 ? ? .
  by apply: V1_point_is_lnsd => //.
Qed.

(* thm 4.6 p136*)
Definition hurwitz n (A : 'M[K]_n.+1) : Prop := (forall a, eigenvalue A a -> a < 0).

(* thm 4.7 p139 + fact: it is exponentially stable*)
Definition locally_exponentially_stable_at n (eqn : 'rV[K]_n.+1 -> 'rV[K]_n.+1) (point : 'rV[K]_n.+1) : Prop :=
  hurwitz (jacobian eqn point).

Lemma eqn33_is_locally_exponentially_stable_at_0 : locally_exponentially_stable_at (eqn33' alpha1 gamma) point1.
Proof.
rewrite /locally_exponentially_stable_at /jacobian /hurwitz.
move => a.
move/eigenvalueP => [u] /[swap] u0 H.
have a_eigen : eigenvalue (jacobian (eqn33' alpha1 gamma) point1) a.
  apply/eigenvalueP.
  exists u. 
    exact: H.
  exact: u0.
have : root (char_poly (jacobian (eqn33' alpha1 gamma) point1)) a.
  rewrite -eigenvalue_root_char.
  exact : a_eigen.
rewrite /eqn33' /jacobian.
Admitted.

End Lyapunov.
