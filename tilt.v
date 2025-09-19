From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import boolp classical_sets functions reals.
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

Definition locposdef {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z > 0.

Definition is_lyapunov_candidate {K : realType} {n} (V : 'rV[K]_n.+1 -> K)
 (x0 : 'rV[K]_n.+1) := locposdef V x0.

(* locally positive semi definite (NB* not used yet) *)
Definition lpsd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z >= 0.

(* locally negative semidefinite *)
Definition locnegsemidef {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z <= 0.

(* locally negative definite (NB: not used yet) *)
Definition lnd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z < 0.

Section derive_help.
Local Open Scope classical_set_scope.

Lemma derivable_dotmul {R : realFieldType} {n}
    (u v : R -> 'rV[R]_n.+1) t :
  derivable u t 1 -> derivable v t 1 ->
  derivable (fun x => u x *d v x) t 1.
Proof.
move=> ut1 vt1/=.
rewrite /dotmul.
rewrite (_ : (fun x : R => _) =
    \sum_k (fun x : R => (u x)``_k * (v x) 0 k)); last first.
  apply/funext => x.
   rewrite !mxE.
   under eq_bigr do rewrite !mxE.
   elim/big_ind2 : _ => //= f a g b -> ->.
   by rewrite fctE.
apply: derivable_sum => i.
by apply: derivableM => //=; exact: derivable_coord.
Qed.

Lemma derive_norm {K : realType} n (u : K^o -> 'rV[K^o]_n.+1) (t : K) :
  u t != 0 ->
  derivable u t 1 ->
  (1 \*o (@GRing.exp K ^~ 2) \o @norm K n.+1 \o u)^`() t =
  2 * (fun t => ('D_1 u t *m  (u t)^T)``_0) t :> K.
Proof.
move=> u0 ut1.
rewrite [LHS]derive1E deriveMl/=; last first.
  apply/derivable1_diffP.
  apply/(@differentiable_comp _ _ _ _ (fun x => norm (u x)) (fun x => x ^+ 2)) => //=.
  rewrite /norm.
  apply/(@differentiable_comp _ _ _ _ _ (fun x => Num.sqrt x)) => //=.
    apply/derivable1_diffP.
    exact/derivable_dotmul.
  apply/derivable1_diffP.
  apply/ex_derive.
  apply: is_derive1_sqrt.
  rewrite dotmulvv.
  by rewrite exprn_gt0// norm_gt0.
rewrite -derive1E mul1r.
under eq_fun do rewrite -dotmulvv.
rewrite dotmulP mxE /= mulr1n.
rewrite derive1E.
rewrite derive_dotmul ; last 2 first.
  exact: ut1.
  exact: ut1.
rewrite dotmulC.
by field.
Qed.

End derive_help.

Section gradient.

Definition jacobian1 {R : numFieldType} n (f : 'rV[R]_n.+1 -> R)
    : 'rV_n.+1 -> 'cV_n.+1 :=
  jacobian (scalar_mx \o f).
(* not used*)
(*Definition partial {R : realType} {n : nat} (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) i :=
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
Qed.*)

(* NB: not used *)
(*Definition err_vec {R : ringType} n (i : 'I_n.+1) : 'rV[R]_n.+1 :=
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
Qed.*)

End gradient.

Section LieDerivative.

(* TODO isnt it just a directional derivative?*)
Definition LieDerivative {R : realFieldType} n (V : 'rV[R]_n.+1 -> R)
    (x : R -> 'rV[R]_n.+1) (t : R) : R :=
  (jacobian1 V (x t))^T *d 'D_1 x t.

Lemma LieDerivativeMl {R : realType} n (f : 'rV_n.+1 -> R) (x : R -> 'rV_n.+1)
    (k : R) :
  (forall t, differentiable f (x t)) ->
  LieDerivative (k *: f) x = k *: LieDerivative f x.
Proof.
move=> dfx.
rewrite /LieDerivative /jacobian1 /jacobian.
rewrite !fctE.
apply/funext => y.
rewrite /dotmul.
rewrite (_ : (fun v : 'rV_n.+1 => (k *: f v)%:M) =
             k *: (fun v : 'rV_n.+1 => (f v)%:M)); last first.
  apply/funext => v //=.
  by rewrite fctE scale_scalar_mx.
rewrite [X in ((lin1_mx X)^T *m ('D_1 x y)^T) 0 0 = _](@diffZ R _ _ _ _ _ ); last first.
  apply/differentiable_comp.
    exact: dfx.
  exact: differentiable_scalar_mx.
rewrite -!trmx_mul.
rewrite ( _ : lin1_mx (k \*: 'd _ _) =
         k *: lin1_mx ('d (fun x0 : 'rV_n.+1 => (f x0)%:M) (x y))); last first.
  by apply/matrixP => i j; rewrite !mxE.
by rewrite mxE [in RHS]mxE -scalemxAr mxE.
Qed.

Lemma LieDerivativeD {K : realType} n (f g : 'rV_n.+1 -> K) (x : K -> 'rV_n.+1) :
  (forall t, differentiable f (x t)) ->
  (forall t, differentiable g (x t)) ->
  LieDerivative (f + g) x = LieDerivative f x + LieDerivative g x.
Proof.
move=> dfx dgx.
rewrite /LieDerivative /jacobian1 !fctE /dotmul /jacobian.
apply/funext => t.
rewrite (_ : (fun x0 : 'rV_n.+1 => (f x0 + g x0)%:M) =
    (fun x0 : 'rV_n.+1 => (f x0)%:M) + (fun x0 : 'rV_n.+1 => (g x0)%:M)); last first.
  apply/funext => v //=.
  apply/matrixP => i j.
  by rewrite !mxE mulrnDl.
rewrite [X in ((lin1_mx X )^T *m ('D_1 x t)^T) 0 0 = _ ](@diffD K _ _ _ _ (x t)) ; last 2 first.
  apply/differentiable_comp => //.
  exact/differentiable_scalar_mx.
  apply/differentiable_comp => //.
  exact/differentiable_scalar_mx.
rewrite -trmx_mul.
rewrite ( _ : lin1_mx ('d _ (x t) \+ 'd _ (x t)) =
  lin1_mx ('d (@scalar_mx _ _ \o f) (x t)) + lin1_mx ('d (@scalar_mx _ _ \o g) (x t))); last first.
  apply/matrixP => i j.
  rewrite mxE [RHS]mxE // [in LHS] /= [LHS]mxE.
  by congr +%R; rewrite mxE.
rewrite [in LHS] mulmxDr /= mxE mxE. by congr +%R;
  rewrite -trmx_mul [RHS]mxE.
Qed.

Lemma derivative_LieDerivative_eq0 {K : realType} n
    (f : 'rV_n.+1 -> K) (x : K -> 'rV[K]_n.+1) (t : K) :
  derivable x t 1 ->
  'D_1 x t = 0 -> LieDerivative f x t = 0.
Proof.
move=> xt1 dtraj.
rewrite /LieDerivative /jacobian1 /dotmul dotmulP /dotmul -trmx_mul.
by rewrite dtraj mul0mx !mxE.
Qed.

Local Notation Left := (@lsubmx _ 1 3 3).
Local Notation Right := (@rsubmx _ 1 3 3).

(* sqrt est l'inverse de la fonction carree..*)
Lemma derivable_sqrt {K: realType} (u : K) : u > 0 -> derivable Num.sqrt (u) 1.
Proof.
move => gt0.
apply: ex_derive.
apply: (is_derive1_sqrt gt0).
Qed.

Lemma differentiable_sqrt {K: realType} (u : K) : u > 0 ->
  differentiable Num.sqrt u.
Proof. move=> u0; exact/derivable1_diffP/derivable_sqrt. Qed.

Lemma differentiable_norm {K : realType} n (f : 'rV[K]_n.+1 -> 'rV_3)
    y :
  f y != 0 ->
  (forall y, differentiable f y) ->
  differentiable (fun x0 : 'rV_n.+1 => norm (f x0)) y.
Proof.
move => fxt0 dif1.
rewrite /norm -fctE.
apply: differentiable_comp; last first.
  apply/derivable1_diffP.
  apply/derivable_sqrt.
  by rewrite dotmulvv expr2 mulr_gt0 //= !norm_gt0 //.
exact: differentiable_dotmul.
Qed.

Lemma LieDerivative_norm {K : realType} (f : 'rV[K]_6 -> 'rV_3)
  (x : K -> 'rV[K]_6) (t : K) :
   (f \o x) t != 0 ->
    differentiable x t -> (forall t, differentiable f t) ->
    LieDerivative (fun y => (norm (f y)) ^+ 2) x t =
    (2%:R *: 'D_1 (f \o x) t *m (f (x t))^T) 0 0.
Proof.
rewrite /LieDerivative.
rewrite /jacobian1.
rewrite /dotmul.
rewrite -trmx_mul.
move => f0 difx diff1.
rewrite -derivemxE; last first.
  apply/differentiable_comp; last first.
    exact: differentiable_scalar_mx.
  rewrite -fctE /=.
  by apply: differentiableM; apply/differentiable_norm => //=.
have := derive_norm.
rewrite //=.
(*move=> /( congr1 (fun z => z t)).*)
rewrite -scalemxAl [X in _ -> _ = X]mxE.
move => <-//; last first.
  apply/diff_derivable.
  by apply: differentiable_comp.
rewrite derive1Ml; last 1 first.
  apply/diff_derivable.
  under eq_fun do rewrite expr2.
  apply: differentiableM => /=;
  apply: (@differentiable_comp _ _ _ _ x (norm \o f)) => //;
  by apply: differentiable_norm.
rewrite fctE /=.
rewrite mul1r.
rewrite !mxE.
rewrite derive1E.
transitivity ( ('D_('D_1 x t) (fun y : 'rV_6 => (norm (f y) ^+ 2)) (x t)) ).
  under eq_fun do rewrite scalar_mxM.
  rewrite derive_mx ?mxE; last first.
    apply: derivable_mulmx => //=; apply: derivable_scalar_mx;
    by apply/diff_derivable; apply: differentiable_norm.
  rewrite /=.
  under [in RHS]eq_fun do rewrite expr2.
  under eq_fun do rewrite -scalar_mxM.
  by under eq_fun do rewrite mxE eqxx mulr1n.
rewrite deriveE ; last first.
  by apply: differentiableM; apply: differentiable_norm => //.
rewrite derive_mx//=; last first.
  by apply: diff_derivable.
rewrite deriveE ; last first.
  apply: differentiableM => /=.
    rewrite /norm.
    (* differentiable norm needs to be generalized*)
    apply: differentiable_comp; last first.
      apply/derivable1_diffP.
      apply/derivable_sqrt.
      by rewrite dotmulvv expr2 mulr_gt0 // norm_gt0 //.
    apply/derivable1_diffP.
    by apply/derivable_dotmul => //=;
      apply/derivable1_diffP; apply: differentiable_comp.
  rewrite /norm.
  apply: differentiable_comp; last first.
    apply/derivable1_diffP.
    apply/derivable_sqrt.
    by rewrite dotmulvv expr2 mulr_gt0 // norm_gt0 //.
  apply/derivable1_diffP.
  by apply/derivable_dotmul => //=;
    apply/derivable1_diffP; apply: differentiable_comp.
transitivity(('d (fun y : 'rV_6 => norm (f y) ^+ 2) (x t ) \o ('d x t)) 1).
  rewrite -derive_mx //=; last by apply: diff_derivable.
  by rewrite deriveE.
rewrite -diff_comp //=.
rewrite -fctE /=.
by apply: differentiableM; by apply: differentiable_norm.
Qed.

End LieDerivative.

(* not used, can be shown to be equivalent to LieDerivative *)
(*Definition LieDerivative_partial {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (a : R -> 'rV[R]_n.+1) (t : R) : R :=
  \sum_(i < n.+1) (partial V (a t) i * ('D_1 a t) ``_ i).*)

Section ode_equation.
Context {K : realType} {n : nat}.
Let T := 'rV[K]_n.+1.

Variable f : (K -> T) -> K -> T.

Definition solves_equation (z : K -> T) (A : set T) : Prop :=
   z 0 \in A  /\ (forall t, derivable z t (1:K)%R) /\ forall t, 'D_1 z t = f z t.

Definition is_equilibrium_point x := solves_equation (cst x).

Definition equilibrium_points A := [set p : T | is_equilibrium_point p A ].

Definition state_space A :=
  [set p : T | exists y, solves_equation y A /\ exists t, p = y t ].

End ode_equation.

Definition is_lyapunov_stable_at {K : realType} {n}
  (f : (K -> 'rV[K]_n.+1) -> K -> 'rV[K]_n.+1)
  (A : set 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> K)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0 A,
      is_lyapunov_candidate V x0 &
      forall traj1 traj2 : (K -> 'rV[K]_n.+1),
        solves_equation f traj1 A ->
        traj1 0 = x0 ->
        locnegsemidef (LieDerivative V traj1) 0].

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
Definition y_a t := - x1 t  *m \S( w t) + 'D_1 x1 t + g0 *: x2 t. (* local frame of the sensor*)
End ya.

Definition S2 {K : realType} := [set x : 'rV[K]_3 | norm x = 1].

Section ya_E.
Context {K : realType}.
Variable R : K -> 'M[K]_3.
Hypothesis RSO : forall t, R t \is 'SO[K]_3.
Variable v : K -> 'rV[K]_3.
Variable g0 : K.
Let w t := ang_vel R t.

(* needs a different v,should be a different lemma..*)
Lemma ya_E t : ('D_1 v t + g0 *: 'e_2) *m R t = y_a v R g0 t.
Proof.
rewrite mulmxDl /y_a/= /x2.
rewrite -scalemxAl.
congr +%R.
rewrite -ang_vel_mxE/=; [|admit|admit].
(*
rewrite [in RHS]derive_mulmx; [|admit|admit].
rewrite derive1mx_ang_vel//; [|admit|admit].
rewrite ang_vel_mxE//; [|admit|admit].
rewrite addrCA.
rewrite -mulmxE.
rewrite -mulNmx.
rewrite [X in _ = _ X]addrC.
rewrite !mulNmx.
rewrite -mulmxA.
by rewrite subrr addr0.
by rewrite /x2 scalemxAl.*)
Admitted.

End ya_E.

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
(*Lemma dRu t (u : K -> 'rV[K]_3) (T : K -> 'M[K]_3) (w' := ang_vel T)
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
Admitted.*)

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
        admit.
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
  let zp1 := Left zp1_z2 in let z2 := Right zp1_z2 in
  (norm zp1)^+2 / (2 * alpha1) + (norm z2)^+2 / (2 * gamma).

Lemma V1_is_lyapunov_candidate : is_lyapunov_candidate V1 point1.
Proof.
rewrite /locposdef; split.
- by rewrite /V1 /point1 lsubmx_const rsubmx_const norm0 expr0n/= !mul0r add0r.
- near=> z_near.
  simpl in *.
  have z_neq0 : z_near != 0 by near: z_near; exact: nbhs_dnbhs_neq.
  rewrite /V1.
  have /orP[lz0|rz0] : (Left z_near != 0) || (Right z_near != 0).
  + rewrite -negb_and.
    apply: contra z_neq0 => /andP[/eqP l0 /eqP r0].
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

Lemma derive_zp1 (z : K) (traj : K -> 'rV_6) : solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  'D_1 (Left \o traj) z = - alpha1 *: Left (traj z).
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

Lemma deriveV1 (x : K -> 'rV[K]_6) t : solves_equation (tilt_eqn alpha1 gamma) x state_space_tilt -> (forall t, differentiable x t) ->
  LieDerivative (V1 alpha1 gamma) x t = V1dot (x t).
Proof.
move=> tilt_eqnx dif1.
rewrite /V1.
rewrite LieDerivativeD; last 2 first.
  move=> t0.
  apply: differentiableM => //=.
  apply: differentiableM => //=.
    admit.
    admit.
  move=> t0.
  apply: differentiableM => //=.
  apply: differentiableM => //=.
    admit.
    admit.
rewrite !invfM /=.
rewrite fctE.
under [X in LieDerivative X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _]eq_fun do rewrite mulrC.
rewrite LieDerivativeMl; last first.
  move => t0.
  apply: differentiableM => //=.
    admit.
    admit.
rewrite LieDerivativeMl; last first.
  move => t0.
   apply: differentiableM => //=.
    admit.
    admit.
rewrite !fctE !LieDerivative_norm /=; last 6 first.
  admit.
  by [].
  apply/derivable1_diffP.
  apply: differentiable_rsubmx => /= x0.
  by [].
  admit.
  by [].
  apply/derivable1_diffP.
  apply: differentiable_lsubmx => /= x0.
  by [].
by rewrite derive_V1dot.
Admitted.

(* TODO: Section general properties of our system *)
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
rewrite [in leRHS](mulrC _ (norm w)).
rewrite mulrC [norm (zp1 z) * _]mulrC.  
rewrite -mulrDl [in leRHS](mulrC (2 ^-1)).
by rewrite -mulrDr -div1r -splitr mulr1.
Qed.

(* TODO: rework of this proof is needed *)
Lemma near0_le0 (traj : K -> 'rV_6) :
  solves_equation (tilt_eqn alpha1 gamma) traj state_space_tilt ->
  traj 0 = point1 ->
  \forall z \near 0^',
    (LieDerivative (fun x => norm (Left x) ^+ 2 / (2 * alpha1)) traj +
     LieDerivative (fun x => norm (Right x) ^+ 2 / (2 * gamma)) traj) z <= 0.
Proof.
move=> dtraj traj0.
rewrite !fctE !invfM /=.
near=> z.
under [X in LieDerivative X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _]eq_fun do rewrite mulrC.
rewrite LieDerivativeMl; last first.
  admit.
rewrite LieDerivativeMl; last first.
  admit.
rewrite /= !fctE !LieDerivative_norm; last 6 first.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
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
Admitted.

Lemma V1_point_is_lnsd (y : K -> 'rV_6) :
  solves_equation (tilt_eqn alpha1 gamma) y state_space_tilt->
  y 0 = point1 ->
  locnegsemidef (LieDerivative (V1 alpha1 gamma) y) 0.
Proof.
move=> [y033] [dy dtraj] traj0.
have Gamma1_traj t : state_space_tilt (y t).
  apply/Gamma1_traj.
  by split => //.
rewrite /locnegsemidef /V1.
rewrite LieDerivativeD /=; last 2 first.
  move => t.
  apply: differentiableM; last 2 first.
    rewrite /=.
    apply: differentiableM; last 2 first.
      apply: differentiable_norm.
        admit.
        admit.
      apply: differentiable_norm.
        admit.
        admit.
    rewrite -fctE.
    apply: differentiable_cst; last first.
    move => t.
    apply: differentiableM; last 2 first.
      apply: differentiableM; last 2 first.
      apply: differentiable_norm.
        admit.
        admit.
      apply: differentiable_norm.
        admit.
        admit.
    rewrite -fctE.
    apply: differentiable_cst.
split; last first.
  apply/near0_le0; last by [].
  by split => //.
rewrite !invfM /=.
rewrite !fctE.
under [X in LieDerivative X _ _ + _]eq_fun do rewrite mulrC.
under [X in _ + LieDerivative X _ _]eq_fun do rewrite mulrC.
rewrite LieDerivativeMl; last first.
  admit.
rewrite LieDerivativeMl; last first.
  admit.
rewrite /= !fctE !derivative_LieDerivative_eq0; last 4 first.
  by [].
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
  by [].
  rewrite [LHS]dtraj /tilt_eqn/= traj0 /point1.
  by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
by rewrite scaler0 scaler0 add0r.
Admitted.

Lemma V1_is_lyapunov_stable :
  is_lyapunov_stable_at (tilt_eqn alpha1 gamma) state_space_tilt (V1 alpha1 gamma) point1.
Proof.
split.
- by apply: equilibrium_point1 => //.
- exact: V1_is_lyapunov_candidate.
- move=> traj1 ? ? ?.
  by apply: V1_point_is_lnsd => //.
Qed.

End Lyapunov.
