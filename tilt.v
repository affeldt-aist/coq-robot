From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

(* PR: to MathComp *)

Lemma lsubmx_const  {R : nmodType} (r : R) m n1 n2 : lsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma rsubmx_const  {R : nmodType} (r : R) m n1 n2 : rsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma derive_sqrt {K : realType} :
  (Num.sqrt^`())%classic = (fun t => (2 * Num.sqrt t)^-1) :> (_ -> K).
Proof.
apply/funext => i.
rewrite derive1E /=.
rewrite invrM.
(* utiliser la reciproque de la fonction carree?*)
Admitted.

Definition defposmx {R : realType}  m (mat : 'M[R]_(m,m)) : Prop :=
  mat \is sym m R /\ forall a : R, eigenvalue mat a -> a > 0.

Lemma defposmxP {R : realType}  m (mat : 'M[R]_(m,m)) : 
  defposmx mat <-> (forall x : 'rV[R]_m, x != 0 -> (x *m mat *m x^T) 0 0 > 0).
Proof.
split.
  move => [].
  move => matsym.
  move => eigen.
  move => x xneq0.
  Search "eigenvalue".
  apply/eigen.
  apply/eigenvalueP.
  exists x => //.
  rewrite /=.
  apply/matrixP.
  move => i j.
Admitted.

Lemma CauchySchwarz_vec {R : realType} {n : nat} : forall (a b : 'rV[R]_n.+1), (a *d b)^+2 <= (a *d a) * (b *d b).
Proof.
move => a b.
suffices: 0 <= (b *d b) * (a *d a) - (a *d b) ^+ 2.
  rewrite -subr_ge0.
  move => h.
  rewrite mulrC in h.
  apply h.
rewrite subr_ge0.
rewrite expr2.
rewrite mulrC.
rewrite !dotmulvv.
rewrite /=.
rewrite -expr2.
case: (boolP (b == 0)) => [/eqP b0|hb].
  rewrite b0.
  rewrite dotmulv0 expr0n.
  rewrite norm0.
  rewrite expr0n // /=.
  rewrite mul0r.
  done.
pose t := (a *d b) / (norm b ^+ 2).
have h : 0 <= norm (a - t *: b) ^+ 2.
  rewrite exprn_ge0 //.
  by rewrite norm_ge0.
rewrite -(dotmulvv (a - t *: b)) in h.
rewrite dotmulBl dotmulBr dotmulvv in h.
rewrite dotmulvZ in h.
rewrite -dotmulvv in h.
rewrite /t in h.
have h1 : 0 <= a *d a - (a *d b) ^+ 2 / norm b ^+ 2.
  move: h.
  rewrite dotmulBr dotmulvZ.
  rewrite (dotmulC ((a *d b / norm b ^+ 2) *: b) a).
  rewrite dotmulvZ dotmulC.
  rewrite dotmulvv /t.
  rewrite expr2.
  rewrite /=.
  rewrite -!expr2.
  rewrite dotmulZv.
  rewrite dotmulvv.
  rewrite divfK /=; last first.
    by rewrite sqrf_eq0 norm_eq0.
  rewrite subrr.
  rewrite subr0.
  rewrite !expr2.
  by rewrite mulrAC.
have h2 : 0 <= norm b ^+ 2 * (a *d a) - (a *d b) ^+ 2.
  have pos: 0 < norm b ^+ 2. 
    rewrite exprn_gt0 //.
    by rewrite norm_gt0.
  suff: norm b ^+ 2 * (a *d a - (a *d b) ^+ 2 / norm b ^+ 2) = 
      norm b ^+ 2 * (a *d a) - (a *d b) ^+ 2.
    move=> eq_step.
    rewrite -eq_step.
    by apply: mulr_ge0; [rewrite ltW | exact h1].
  rewrite mulrBr.
  congr (_ - _)%R.
  by rewrite mulrCA divff ?mulr1// sqrf_eq0 norm_eq0.
rewrite -subr_ge0 mulrC.
rewrite dotmulvv in h2.
by rewrite mulrC in h2.
Qed.

Lemma young_inequality_vec {R : realType} {n : nat} : forall  (a b : 'rV[R]_n.+1), 
  (a *d b) <= (2^-1 * (norm(a))^+2) + (2^-1 * (norm(b))^+2).
Proof.
move => a b.
have normage0 : 0 <= (norm(a))^+2.
  rewrite expr2.
  by rewrite mulr_ge0 // norm_ge0.
have normbge0 : 0 <= (norm(b))^+2.
  rewrite expr2.
  by rewrite mulr_ge0 // norm_ge0.
rewrite -!dotmulvv.
have: 0 <= norm(a - b)^+2.
  rewrite expr2.
  by rewrite mulr_ge0 // norm_ge0.
rewrite -dotmulvv.
rewrite dotmulD.
rewrite !dotmulvv.
move => h.
rewrite -mulr_natl in h.
have h2 : 2 * (a *d b)  <= norm a ^+ 2 + norm (- b) ^+ 2.
  rewrite -subr_ge0.
  rewrite dotmulvN mulrN in h.
  by rewrite addrAC.
rewrite -ler_pdivlMl// in h2.
rewrite -mulrDr.
by rewrite normN in h2.
Qed.

Local Open Scope classical_set_scope.
Lemma derivemx_derive {R : realFieldType} (V : normedModType R) m n
   (f : V -> 'M[R]_(m.+1, n.+1)) (x0 : V) (v : V) (i : 'I_m.+1) (j : 'I_n.+1) :
  'D_v f x0 i j = 'D_v (fun x => f x i j) x0.
Proof.
apply/esym/cvg_lim => //=.
apply/cvgrPdist_le => /= e e0.
near=> t.
Admitted.
Local Close Scope classical_set_scope.

Lemma derive1mxE' {R : realFieldType} {n : nat} (M : R -> 'rV[R]_n.+1) t :
  derive1mx M t = M^`()%classic t.
Proof.
apply/rowP => i.
rewrite /derive1mx !mxE.
rewrite !derive1E.
by rewrite derivemx_derive.
Qed.

Local Open Scope classical_set_scope.

Definition locposdef {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z > 0.

(* locally positive semi definite*)
Definition lpsd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z >= 0.

(*locally negative semidefinite *)
Definition locnegsemidef {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z <= 0.

(*locally negative definite*)
Definition lnd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z < 0.

Definition partial {R : realType} {n : nat} (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) i :=
  lim (h^-1 * (f (a + h *: 'e_i) - f a) @[h --> 0^'])%classic.

Definition gradient_partial {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :=
  \row_(i < n.+1) partial f a i.

Lemma partial_diff {R : realType} n (f : 'rV[R]_n.+1 -> 'rV[R]_1)  (a : 'rV[R]_n.+1)
    (i : 'I_n.+1) :
  partial (fun x => (f x) 0 0) a i =
  ('D_'e_i (fun x : 'rV[R]_n.+1 => (f x) : 'rV[R]_1) a) 0 0.
Proof.
rewrite derivemx_derive/=.
rewrite /partial.
rewrite /derive /=.
by under eq_fun do rewrite (addrC a).
Qed.

Definition LieDerivative {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (a : R -> 'rV[R]_n.+1) (t : R) : R :=
  \sum_(i < n.+1) (partial V (a t) i * (derive1mx a t) ``_ i).

Definition jacobian1 {R : realType} n (f : 'rV[R]_n.+1 -> 'rV[R]_1) :=
  jacobian f.

Lemma gradient_partial_jacobian1 {R : realType} n (f : 'rV[R]_n.+1 -> 'rV[R]_1) (a : 'rV[R]_n.+1):
  gradient_partial (fun x : 'rV[R]_n.+1 => (f x) 0 0) a = (jacobian1 f a)^T.
Proof.
rewrite /jacobian1.
apply/rowP => i.
rewrite /gradient_partial mxE mxE /jacobian mxE -deriveE; last first.
  admit.
by rewrite partial_diff.
Admitted.

Lemma gradient_partial_sum {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :
  gradient_partial f a = \sum_(i < n.+1) partial f a i *: 'e_i.
Proof.
rewrite /gradient_partial [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

Section derive_help.

Definition err_vec {R : ringType} n (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Lemma err_vecE {R : ringType} n (i : 'I_n.+1) :
  err_vec i = 'e_i :> 'rV[R]_n.+1.
Proof.
apply/rowP => j.
by rewrite !mxE eqxx /= eq_sym.
Qed.


Local Open Scope classical_set_scope.
Lemma derive_norm {K : realType} n (u : K^o -> 'rV[K^o]_n.+1) :
  (forall t, norm (u t) != 0) ->
  (2^-1 \*o (@GRing.exp K ^~ 2) \o @norm K n.+1 \o u)^`() =
  (fun t => (derive1mx u t *m  (u t)^T)``_0) :> (K -> K).
Proof.
move=> u0; apply/funext => t.
rewrite [LHS]derive1E.
rewrite deriveMl/=; last first.
  admit.
rewrite -derive1E.
rewrite (@derive1_comp _ (@norm _ _ \o u ) (@GRing.exp K ^~ 2)) ; last 2 first.
  admit.
  admit.
rewrite exp_derive1.
rewrite derive1_comp /=; last 2 first.
  admit.
  admit.
rewrite !derive_sqrt.
rewrite !expr1.
rewrite !(mulrA 2^-1).
rewrite mulVf ?pnatr_eq0// mul1r.
rewrite !dotmulvv.
rewrite sqrtr_sqr.
rewrite normr_norm.
rewrite !mulrA /=.
have -> : norm (u t) / (2 * norm (u t)) = 2^-1.
  by rewrite invfM// mulrCA divff ?mulr1.
set X := (X in X^`()%classic).
have dot : X t =  norm(u t)^+2 by rewrite /X dotmulvv.
rewrite /X.
rewrite !derive1mx_dotmul; last 2 first.
  admit.
  admit.
rewrite dotmulP /=.
set y := derive1mx u t *d u t.
have -> : y + u t *d derive1mx u t = 2 * y.
  by rewrite mulr_natl mulr2n dotmulC.
by rewrite mulrA mulVf ?pnatr_eq0// mul1r mxE eqxx mulr1n.
Admitted.

End derive_help.

Definition LieDerivative_jacobian1 {R : realType} n (V : 'rV[R]_n.+1 -> 'rV[R]_1)
    (x : R -> 'rV[R]_n.+1) (t : R) : R :=
  let xdot_t := derive1mx x t in
  (jacobian1 V (x t))^T *d xdot_t.

Lemma LieDerivative_jacobian1Ml {R : realType} n
    (f : 'rV_n.+1 -> 'cV_1) (x : R -> 'rV_n.+1) (k : R) : 
  LieDerivative_jacobian1 (k *: f) x = k *: LieDerivative_jacobian1 f x.
Proof.
rewrite /LieDerivative_jacobian1 /jacobian1 /jacobian.
rewrite !fctE.
apply/funext => y.
rewrite /dotmul.
rewrite [X in ((lin1_mx X )^T *m (derive1mx x y)^T) 0 0 = _](@diffZ R _ _ _ _ _ ); last first.
  admit.
rewrite -!trmx_mul ( _ : lin1_mx (k \*: 'd f (x y)) = k *: lin1_mx ('d f (x y))); last first.
  apply/matrixP => i j.
  by rewrite !mxE.
rewrite mxE [in RHS]mxE.
by rewrite -scalemxAr mxE.
Admitted.

Lemma LieDerivative_jacobian1D {K : realType} n
    (f g : 'rV_n.+1 -> 'cV_1) (x : K -> 'rV_n.+1) :
  LieDerivative_jacobian1 (f + g) x =
  LieDerivative_jacobian1 f x + LieDerivative_jacobian1 g x.
Proof.
rewrite /LieDerivative_jacobian1 /jacobian1 !fctE /dotmul /jacobian.
apply/funext => t.
rewrite [X in ((lin1_mx X )^T *m (derive1mx x t)^T) 0 0 = _ ](@diffD K _ _ f g (x t)) ; last 2 first.
  admit. 
  admit.
rewrite -trmx_mul.
rewrite ( _ : lin1_mx ('d f (x t) \+ 'd g (x t)) =
  lin1_mx ('d f (x t)) + lin1_mx ('d g (x t))); last first.
  apply/matrixP => i j.
  rewrite mxE.
  rewrite [RHS]mxE //.
  rewrite [in LHS] /=.
  rewrite [LHS]mxE.
  by congr (_+_); rewrite mxE.
rewrite [in LHS] mulmxDr /=.
rewrite mxE mxE.
by congr (_+_); 
  rewrite -trmx_mul [RHS]mxE.
Admitted.

Lemma LieDerivative_jacobian1_eq0_equilibrium {K : realType} n
    (f : 'rV_n.+1 -> 'cV_1) (x : K -> 'rV[K]_n.+1) (t : K) :
  'D_1 x t = 0 -> LieDerivative_jacobian1 f x t = 0.
Proof.
move => dtraj.
rewrite /LieDerivative_jacobian1 /jacobian1 /dotmul dotmulP /dotmul -trmx_mul.
by rewrite derive1mxE' /= mxE mxE /= derive1E dtraj mul0mx /= mxE /=.
Qed.

Lemma LieDerivative_jacobian1_norm {K : realType} (f : 'rV[K]_6 -> 'rV_3) 
  (x : K -> 'rV[K]_6) (t : K) :
  LieDerivative_jacobian1 (fun y => ((norm (f y)) ^+ 2)%:M) x t =
    (2%:R *: derive1mx (f \o x) t *m (f (x t))^T) 0 0.
Proof.
rewrite /LieDerivative_jacobian1 /jacobian1 /dotmul.
rewrite /jacobian dotmulP /dotmul -trmx_mul.
rewrite !derive1mxE' /= mxE mxE /= !fctE.
rewrite !derive1E.
rewrite mulr1n.
rewrite -scalemxAl.
rewrite [RHS]mxE.
apply: (@mulfI _ 2^-1); first by rewrite invr_eq0// pnatr_eq0.
rewrite mulrA mulVf ?pnatr_eq0// mul1r.
set h := (fun x0 : 'rV_6 => (norm (f x0) ^+ 2)%:M).
set tmp : {linear 'rV_6 -> 'rV_1} := 'd h (x t).
rewrite -[in RHS]derive1E.
have : forall t0 : K^o, norm (f (x t0)) != 0.
  admit.
move=> /derive_norm.
move=> /(congr1 (fun z => z t)).
rewrite /=.
rewrite derive1mxE'.
move=> <-.
rewrite derive1E.
rewrite deriveMl//=; last admit.
congr *%R.
rewrite /tmp /h.
rewrite [in RHS]deriveE; last first.
  admit.
have /= := (@diff_comp _ _ _ _ x (fun z => (norm (f z) ^+ 2%R))).
move=> ->; last 2 first.
  admit.
  admit.
rewrite /=.
rewrite -[in RHS]deriveE; last first.
  admit.
rewrite -/h.
have -> : ('D_1 x t *m lin1_mx 'd h (x t)) =
      'D_('d x t 1) (fun z : 'rV_6 => (norm (f z) ^+ 2%R)%:M) (x t).
  have := (@derivemxE K 5 0 h (x t) ('d x t 1)).
  move=> ->; last admit.
  congr (_ *m _).
  rewrite deriveE//.
  admit.
rewrite derivemx_derive/=.
congr ('D_('d x t 1) _ (x t)).
apply/funext => v.
by rewrite mxE eqxx mulr1n.
Admitted.

Section ode.
Context {K : realType}.
Let T := 'rV[K]_6.
Local Open Scope classical_set_scope.

Variable f : K -> (K -> T) -> T.

Definition is_solution (x : K -> T) : Prop :=
  forall t, derive1mx x t = f t x.

Definition is_equilibrium_point p := is_solution (cst p).

Definition equilibrium_points := [set p : T | is_equilibrium_point p].

Definition state_space :=
  [set p : T | exists y, is_solution y /\ p \in range y].

End ode.

Definition is_lyapunov_function {K : realType} (n := 5)
  (f : K -> (K -> 'rV[K]_n.+1) -> 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> 'rV[K]_1)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0,
 locposdef (fun z => (V z) 0 0) x0 &
  forall traj : K -> 'rV[K]_n.+1,
    is_solution f traj ->
    traj 0 = x0 ->
   locnegsemidef (LieDerivative_jacobian1 V traj) 0].

Local Close Scope classical_set_scope.

Section problem_statement.
Context {K : realType}.
Variable g0 : K.
Hypothesis g0_pos : 0 < g0.
Variable  m : 'rV[K]_3.
Variable R : K -> 'M[K]_3.
Variable w : 'rV[K]_3. (* angular velocity *)
Variable v : K -> 'rV[K]_3.

Definition ez : 'rV[K]_3 := 'e_2.
Definition x2 t := ez *m (R t)^T.
Definition x3 t := m *m (R t)^T.
Definition rhs24 t := m *m (R t)^T.
Definition rhs23 t :=
  v t *m \S(w) + derive1mx v t + g0 *: ez *m (R t)^T.
Definition eqn25 t := derive1mx R t = R t *m \S(w).

End problem_statement.

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
by rewrite mulmx0 sub0r -mul_scalar_mx -mulNmx; congr (_ *m _) ; rewrite scalemx1 rmorphN /=.
Qed.

Lemma fact215 ( v w : 'rV[K]_3) : \S(w *m \S(v)) = \S(w) * \S(v) - \S(v) * \S(w).
Proof.
by rewrite spinE spin_crossmul.
Qed.

Lemma fact216 (v w : 'rV[K]_3): \S(w *m \S(v)) = v^T *m w - w^T *m v.
Proof.
by rewrite fact215 !fact212 -!/(_ *d _) dotmulC opprB addrA subrK.
Qed.
Search (\S(_)).
Lemma fact217 (v : 'rV[K]_3): \S(v) ^+ 3 = - (norm v ^+2) *: \S(v).
  exact: spin3.
Qed.

Lemma fact214 (R : 'M[K]_3) (v_ : seq 'rV[K]_3) : R \is 'SO[K]_3 -> R^T * (\prod_(i <- v_) \S( i )) * R =  (\prod_(i <- v_) \S( i *m R)).
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

Section Gamma1.
Context {K : realType}.
Local Open Scope classical_set_scope.

Definition Gamma1 := [set x : 'rV[K]_6 | norm (@rsubmx _ 1 3 3 x) = 1].

End Gamma1.
  
Section eqn33.
Variable K : realType.
Variable alpha1 : K.
Variable gamma : K.
Hypothesis gamma_gt0 : 0 < gamma.
Hypothesis alpha1_gt0 : 0 < alpha1.

Local Notation Lsubmx := (@lsubmx K 1 3 3).
Local Notation Rsubmx := (@rsubmx K 1 3 3).

Definition eqn33 (zp1_z2_point : K -> 'rV[K]_6) t : 'rV[K]_6 :=
  let zp1_point := Lsubmx \o zp1_z2_point in
  let z2_point := Rsubmx \o zp1_z2_point in
  row_mx (- alpha1 *: zp1_point t)
         (gamma *: (z2_point t - zp1_point t) *m \S('e_2%:R - z2_point t) ^+ 2).

(* cauchy lipschitz par F1 qui definit un champ de vecteur lisse : 
il existe une solution depuis tout point:
gamma1 ⊆ state_space*)
(* prouver invariance geometrique, tangence donc les trajectoires restent dans gamma1:
 state_space ⊆ gamma1
Definition xi1 t (zp1_zp2 : K -> 'rV[K]_6) : Gamma1 :=
  let zp1*)

Lemma thm11a : state_space (fun a b => eqn33 b a) = Gamma1.
Proof.
apply/seteqP; split.
- move=> p.
  rewrite /state_space /Gamma1 /eqn33 /is_solution /=.
  move=> [y0 [Heq Hrange]].
  admit.
- move => p.
  rewrite /state_space /Gamma1 /eqn33 /is_solution /=.
  move => y.
  rewrite /state_space /Gamma1 /eqn33 /is_solution.
  admit.
Admitted.

Definition point1 : 'rV[K]_6 := 0.
Definition point2 : 'rV[K]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2%:R).

Lemma equilibrium_point1 : is_equilibrium_point (fun a b => eqn33 b a) point1.
Proof.
move => t ; rewrite derive1mx_cst /eqn33 /point1 ; apply/eqP ; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP. split.
  rewrite scaler_eq0; apply/orP; right; apply/eqP/rowP; move => i; by rewrite !mxE.
  apply/eqP/rowP; move => i; apply/eqP; set N := (X in _ *: X *m _); have : N = 0.
    rewrite /N /=; apply /rowP; move => a; by rewrite !mxE subr0.
  move => n; by rewrite n scaler0 mul0mx.
Qed.

Lemma equilibrium_point2 : is_equilibrium_point (fun a b => eqn33 b a) point2.
Proof.
move => t; rewrite derive1mx_cst; apply /eqP; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
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
rewrite -[Lsubmx point2]/N N0 subr0.
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

Open Scope classical_set_scope.
(* this lemma asks for lyapunov + lasalle*)
Lemma tractories_converge (y : K -> 'rV[K]_6) : is_solution (fun a b => eqn33 b a) y ->
  y t @[t --> +oo] --> point1 \/ y t @[t --> +oo] --> point2.
Proof.
move=> is_sol_y.
Abort.

End eqn33.

Open Scope classical_set_scope.

Section Lyapunov.
Local Open Scope classical_set_scope.

(*Lemma LieDerivative_gradientE {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (x : R -> 'rV[R]_n.+1) :
  LieDerivative_gradient_partial V x = LieDerivative V x.
Proof.
apply/funext => t; rewrite /LieDerivative_gradient /LieDerivative.
rewrite gradientE dotmulsuml; apply: eq_bigr => /= i _.
rewrite dotmulE (bigD1 i)//= big1 ?addr0; last first.
  by move=> j ji; rewrite !mxE/= (negbTE ji) mulr0 mul0r.
by rewrite !mxE/= eqxx mulr1.
Qed.*)

Context {K : realType}.
Variable x1_hat : K -> 'rV[K]_3.
Variable x2_hat : K -> 'rV[K]_3.
Variable alpha1 : K.
Variable gamma : K.
Variable g0 : K.
Hypothesis g0_pos : 0 < g0.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.
Variable R : K -> 'M[K]_3.
Variable v : K -> 'rV[K]_3.
Definition x1 := v.

Definition p1 t : 'rV[K]_3 :=
  let x1_t := x1 t in
  let x2_t := x2 R t  in
  let x1_hat_t := x1_hat t in
  x2_t + (alpha1 / g0) *: (x1_t - x1_hat_t).

Definition x2_tilde t : 'rV[K]_3 :=
  let x2_t := x2 R t in
  let x2_hat_t := x2_hat t in
  (x2_t - x2_hat_t). (* dependance des conditions intiales de ^x2 qui doit etre sur S2.*)

Local Notation Lsubmx := (@lsubmx K 1 3 3).
Local Notation Rsubmx := (@rsubmx K 1 3 3).

Definition zp1_z2_eq t (zp1_z2 : K -> 'rV[K]_6) : 'rV[K]_6 :=
  let zp1 := Lsubmx \o zp1_z2 in
  let z2 := Rsubmx \o zp1_z2 in
  row_mx (p1 t *m R t) (x2_tilde t *m R t).

Definition V1 (zp1_z2 : 'rV[K]_6) : 'rV[K]_1 :=
  let zp1 := Lsubmx zp1_z2 in
  let z2 := Rsubmx zp1_z2 in
  ((norm zp1)^+2 / (2%:R * alpha1) + (norm z2)^+2 / (2%:R * gamma))%:M.

Definition V1dot (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := Lsubmx zp1_z2 in
  let z2 := Rsubmx zp1_z2 in
  - (norm zp1)^+2 + (z2 *m (\S('e_2%:R - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2%:R - z2))^+2 *m zp1^T)``_0.

Lemma deriveV1 (x : K -> 'rV[K]_6) t : is_solution (fun a b => @eqn33 K alpha1 gamma b a) x ->
  LieDerivative_jacobian1 V1 x t = V1dot (x t).
Proof.
move=> eqn33x.
pose zp1 := fun r => Lsubmx (x r).
pose z2 := fun r => Rsubmx (x r).
rewrite /V1.
(*rewrite LieDerivative_gradient_jacobianD.
rewrite [X in LieDerivative_gradient_jacobian X] LieDerivative_gradient_jacobianMl.*)
  rewrite /V1.
  rewrite [X in LieDerivative_jacobian1 X _ _](_ : _ =
    (fun zp1_z2 : 'rV_6 =>
     (norm (Lsubmx zp1_z2) ^+ 2 / (2 * alpha1))%:M)
    +
    (fun zp1_z2 : 'rV_6 =>
     (norm (Rsubmx zp1_z2) ^+ 2 / (2 * gamma))%:M)
    ); last first.
    apply/funext => y/=.
    rewrite fctE.
    by rewrite raddfD.
  rewrite LieDerivative_jacobian1D.
  rewrite !invfM /=.
  set c1 := (2^-1 / alpha1).
  set c2 := (2^-1 / gamma).
  rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 * c1)%:M) =
               (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M)) ; last first.
  apply/funext => y.
  by rewrite -scale_scalar_mx.
  rewrite !fctE.
   have func_eq: (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M) = 
              (fun zp1_z2 : 'rV_6 => c1 *: (norm (Lsubmx zp1_z2) ^+ 2)%:M).
   move => n.
   apply/funext => zp1_z2.
   by rewrite scalar_mxM -!mul_scalar_mx scalar_mxC.
   rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 * c2)%:M) =
                (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 *: c2)%:M)) ; last first.
  apply/funext => y.
  by rewrite -scale_scalar_mx.
   rewrite func_eq.
    have func_eq2: (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 *: c2)%:M) = 
              (fun zp1_z2 : 'rV_6 => c2 *: (norm (Rsubmx zp1_z2) ^+ 2)%:M).
   move => n.
   apply/funext => zp1_z2.
   by rewrite scalar_mxM -!mul_scalar_mx scalar_mxC.
   rewrite func_eq2.
  rewrite !LieDerivative_jacobian1Ml.
   rewrite !fctE.
rewrite !LieDerivative_jacobian1_norm /=.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -[Lsubmx \o x]/zp1.
rewrite -[Rsubmx \o x]/z2.
have H1 : derive1mx zp1 t = (- alpha1 *: Lsubmx (x t)).
  have := eqn33x t.
  rewrite /eqn33.
  admit. (* from eqn33? *)
have H2 : derive1mx z2 t = (gamma *: (Rsubmx (x t) - Lsubmx (x t)) *m \S('e_2 - Rsubmx (x t)) ^+ 2).
  admit.
rewrite H1.
rewrite -scalemxAl.
rewrite mxE.
rewrite [X in X + _](mulrA (alpha1^-1) (- alpha1)).
rewrite mulrN. 
rewrite mulVf ?gt_eqF// mulN1r.
rewrite H2.
rewrite -scalemxAl.
rewrite mulmxA.
rewrite -scalemxAl.
rewrite [in X in _ + X]mxE.
rewrite scalerA.
rewrite mulVf ?gt_eqF//.
rewrite scale1r.
have -> : ((Lsubmx (x t)) *m (Lsubmx (x t))^T) 0 0 = norm (Lsubmx (x t)) ^+2.
  rewrite sqr_sqrtr.
    rewrite dotmulP.
    by rewrite mxE eqxx mulr1n.
  rewrite dotmulvv.
  by rewrite sqr_ge0.
rewrite /V1dot.
congr +%R.
set Lmx := lsubmx _.
set Rmx := rsubmx _.
rewrite -2![in RHS]mulmxA.
rewrite -mulmxBr.
rewrite -mulmxBr.
rewrite -linearB/=.
rewrite -[X in _ = (X *m (_ *m _)) 0 0]trmxK.
rewrite -[X in _ = (_ *m (X *m _)) 0 0]trmxK.
rewrite mulmxA.
rewrite -trmx_mul.
rewrite -trmx_mul.
rewrite [RHS]mxE.
rewrite -(mulmxA (Rmx - Lmx)).
rewrite mulmxE.
rewrite -expr2.
have -> : (\S('e_2 - Rmx) ^+ 2)^T = \S('e_2 - Rmx) ^+ 2.
  apply/esym/eqP.
  rewrite -symE.
  exact: sqr_spin_is_sym.
by rewrite mulmxA.
Admitted.

Lemma V1_is_lyapunov : is_lyapunov_function (fun a b => @eqn33 K alpha1 gamma b a) V1 (@point1 K).
Proof.
split; first exact: equilibrium_point1.
- rewrite /locposdef; split.
  + by rewrite /V1 /point1 lsubmx_const rsubmx_const norm0 expr0n/= !mul0r add0r mxE /=.
  + near=> z_near.
    simpl in *.
    have z_neq0 : z_near != 0 by near: z_near; exact: nbhs_dnbhs_neq.
    rewrite /V1.
    have /orP[lz0|rz0] : (Lsubmx z_near != 0) || (Rsubmx z_near != 0).
      rewrite -negb_and.
      apply: contra z_neq0 => /andP[/eqP l0 /eqP r0].
      rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
      by apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?; rewrite mxE.
    + set rsub := Rsubmx z_near.
      have : norm rsub >= 0 by rewrite norm_ge0.
      set lsub := Lsubmx z_near.
      move => nor.
      have normlsub : norm lsub > 0 by rewrite norm_gt0.
      rewrite mxE /= ltr_pwDl//.
        by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
      by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
    - rewrite mxE /= ltr_pwDr//.
        by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0// norm_gt0.
      by rewrite divr_ge0 ?exprn_ge0 ?norm_ge0// mulr_ge0// ltW.
- move=> traj dtraj traj0.
  rewrite /locnegsemidef.
  rewrite /V1.
  rewrite [x in (LieDerivative_jacobian1 x)] (_ : _ = (fun x0 : 'rV_6 =>
               (norm (Lsubmx x0) ^+ 2 / (2 * alpha1))%:M) \+
               (fun x0 => (norm (Rsubmx x0) ^+ 2 / (2 * gamma))%:M)); last first.
      by apply/funext => ?/=; rewrite !raddfD.
  rewrite LieDerivative_jacobian1D /=.
  split.
   rewrite !invfM /=.
  set c1 := (2^-1 / alpha1).
  set c2 := (2^-1 / gamma).
  rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 * c1)%:M) =
               (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M)) ; last first.
  apply/funext => y.
  by rewrite -scale_scalar_mx.
  rewrite !fctE.
   have func_eq: (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M) = 
              (fun zp1_z2 : 'rV_6 => c1 *: (norm (Lsubmx zp1_z2) ^+ 2)%:M).
   move => n.
   apply/funext => zp1_z2.
   by rewrite scalar_mxM -!mul_scalar_mx scalar_mxC.
   rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 * c2)%:M) =
     (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 *: c2)%:M)) ; last first.
  apply/funext => y.
  by rewrite -scale_scalar_mx.
   rewrite func_eq.
    have func_eq2: (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 *: c2)%:M) = 
              (fun zp1_z2 : 'rV_6 => c2 *: (norm (Rsubmx zp1_z2) ^+ 2)%:M).
   move => n.
   apply/funext => zp1_z2.
   by rewrite scalar_mxM -!mul_scalar_mx scalar_mxC.
   rewrite func_eq2.
  rewrite !LieDerivative_jacobian1Ml /=.
  rewrite !fctE.
  rewrite !LieDerivative_jacobian1_eq0_equilibrium.
  by rewrite scaler0 scaler0 add0r.
   rewrite /is_solution /eqn33 in dtraj.
   rewrite -derive1E.
   rewrite -derive1mxE'.
   rewrite dtraj/= traj0 /point1.
   by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
  rewrite /is_solution /eqn33 in dtraj.
   rewrite -derive1E.
   rewrite -derive1mxE'.
   rewrite dtraj/= traj0 /point1.
   by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
  + near=> z.
    rewrite !fctE.
    rewrite !invfM /=.
    set c1 := (2^-1 / alpha1).
    set c2 := (2^-1 / gamma).
    rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 * c1)%:M) =
      (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M)) ; last first.
      apply/funext => y.
      by rewrite -scale_scalar_mx.
    have func_eq: (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M) = 
              (fun zp1_z2 : 'rV_6 => c1 *: (norm (Lsubmx zp1_z2) ^+ 2)%:M).
   move => n.
   apply/funext => zp1_z2.
   by rewrite scalar_mxM -!mul_scalar_mx scalar_mxC.
   rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 * c2)%:M) =
     (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 *: c2)%:M)) ; last first.
  apply/funext => y.
  by rewrite -scale_scalar_mx.
   rewrite func_eq.
    have func_eq2: (fun zp1_z2 : 'rV_6 => (norm (Rsubmx zp1_z2) ^+ 2 *: c2)%:M) = 
              (fun zp1_z2 : 'rV_6 => c2 *: (norm (Rsubmx zp1_z2) ^+ 2)%:M).
   move => n.
   apply/funext => zp1_z2.
   by rewrite scalar_mxM -!mul_scalar_mx scalar_mxC.
   rewrite func_eq2.
  rewrite !LieDerivative_jacobian1Ml /=.
  rewrite !fctE.
  rewrite !LieDerivative_jacobian1_norm.
  pose zp1 := fun r => Lsubmx (traj r).
  pose z2 := fun r => Rsubmx (traj r).
  rewrite -[Lsubmx \o traj]/zp1.
  rewrite -[Rsubmx \o traj]/z2.
  have: c1 *: (2 *: derive1mx zp1 z *m (Lsubmx (traj z))^T) 0 0 + 
          c2 *: (2 *: derive1mx z2 z *m (Rsubmx (traj z))^T) 0 0 
             = V1dot (traj z).
  rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
  rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC mulVf ?pnatr_eq0// div1r.
  have H1 : derive1mx zp1 z = (- alpha1 *: Lsubmx (traj z)).
    admit. (* from eqn33? *)
  have H2 : derive1mx z2 z = (gamma *: (Rsubmx (traj z) - Lsubmx (traj z)) *m \S('e_2 - Rsubmx (traj z)) ^+ 2).
    admit.
  rewrite H1 -scalemxAl mxE [X in X + _](mulrA (alpha1^-1) (- alpha1)) mulrN mulVf ?gt_eqF// mulN1r.
  rewrite H2 -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE scalerA mulVf ?gt_eqF// scale1r.
  have -> : ((Lsubmx (traj z)) *m (Lsubmx (traj z))^T) 0 0 = norm (Lsubmx (traj z)) ^+2.
    rewrite sqr_sqrtr /dotmul.
    admit.
    admit.
  rewrite /V1dot.
  congr +%R.
  set Lmx := lsubmx _.
  set Rmx := rsubmx _.
  rewrite -2![in RHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
  rewrite -[X in _ = (X *m (_ *m _)) 0 0]trmxK -[X in _ = (_ *m (X *m _)) 0 0]trmxK.
  rewrite mulmxA -trmx_mul -trmx_mul [RHS]mxE -(mulmxA (Rmx - Lmx)) mulmxE -expr2.
  have -> : (\S('e_2 - Rmx) ^+ 2)^T = \S('e_2 - Rmx) ^+ 2.
    apply/esym/eqP.
    rewrite -symE.
    exact: sqr_spin_is_sym.
  by rewrite mulmxA.
move=> ->.
(* this form matches the one in the paper, we can safely proceed
 TODO survey of available properties: Young, Cauchy Schwartz? Forme quadratique? 
 Calcul des valeurs propres d'une matrice?
 Matrice definie positive?
 Conclure sur le signe d'une equation comme ca?*)
rewrite /V1dot.
rewrite -/(zp1 z).
rewrite -/(z2 z).
set w := (z2 z) *m \S('e_2).
pose u1 : 'rV[K]_2 := \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i.
pose u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2)
  [eta (fun=> 0) with (0,0) |-> 1,
                      (0,1) |-> -2^-1,
                      (1,0) |-> -2^-1,
                      (1,1) |-> 1] (i,j).
apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
  rewrite mxE.
  have eq0T : z2 z *m \S(z2 z)^T = 0.
    apply: trmx_inj.
    rewrite trmx_mul.
    rewrite trmxK.
    rewrite spin_mul_tr.
    by rewrite trmx0.
  have H2 : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2).
    rewrite spinD.
    rewrite spinN.
    rewrite -tr_spin.
    rewrite !mulmxDr.
    rewrite !eq0T.
    by rewrite !addr0.
  have H1 : (z2 z *m \S('e_2 - z2 z)^+2 *m (z2 z)^T) 0 0 = - (norm w)^+2.
    rewrite /w.
    rewrite spinD.
    rewrite spinN.
    rewrite -tr_spin.
    rewrite mulmxA.
    rewrite !mulmxDr.
    rewrite mulmxDl.
    rewrite !eq0T.
    rewrite !addr0.
    rewrite -dotmulvv.
    rewrite /dotmul.
    rewrite trmx_mul.
    rewrite mxE [X in _ + X = _](_ : _ = 0) ?addr0; last first.
      rewrite tr_spin.
      rewrite -mulmxA.
      rewrite mulNmx.
      rewrite spin_mul_tr.
      by rewrite mulmxN mulmx0 oppr0 mxE.
    rewrite tr_spin.
    rewrite mulNmx.
    rewrite mulmxN [in RHS]mxE opprK.
    by rewrite mulmxA.
  rewrite H1.
  rewrite mxE.
  rewrite addrA.
   rewrite expr2.
  rewrite mulmxA.
  rewrite H2.
  rewrite -/w.
  rewrite -dotmulNv.
  rewrite addrC.
  rewrite -mulmxN.
  rewrite -expr2.
  set a :=   (w *m - \S('e_2 - z2 z)).
  have neg_spin: norm (w *m - \S('e_2 - z2 z)) = norm (w).
    rewrite orth_preserves_norm //.
    admit.
  rewrite /a.
  have cauchy : ((w *m - \S('e_2 - z2 z) *d (zp1 z))%:M : 'rV_1) 0 0 <= norm(w *m - (\S('e_2 - z2 z))) *
                norm(zp1 z).
    rewrite mxE /= mulr1n.
    rewrite (le_trans (ler_norm _)) //.
    rewrite -ler_sqr // ; last first.
      by rewrite nnegrE //  mulr_ge0 ?norm_ge0 //.
      rewrite exprMn.
      rewrite sqr_normr.
      rewrite (le_trans (CauchySchwarz_vec _ _)) //.
      by rewrite !dotmulvv.
  apply: (@le_trans _ _  (norm (w *m - \S('e_2 - z2 z)) * norm (zp1 z)  + (- norm (zp1 z) ^+ 2 - norm w ^+ 2))).
    rewrite lerD2r.
    rewrite (le_trans _ (cauchy)) //.
    by rewrite mxE eqxx mulr1n.
  rewrite neg_spin.
  rewrite /a .
  rewrite /u1 /u2.
  rewrite ![in leRHS]mxE.
  rewrite !sum2E/=.
  rewrite ![in leRHS]mxE.
  rewrite !sum2E/=.
  rewrite ![in leRHS]mxE.
  rewrite /=.
  rewrite !mulr1.
  rewrite mulrN.
  rewrite mulNr.
  rewrite opprK.
  rewrite mulrDl.
  rewrite mulNr.
  rewrite -expr2.
  rewrite [in leLHS] addrCA.
  rewrite -!addrA.
  rewrite lerD2l.
  rewrite mulrDl.
  rewrite (mulNr (norm w)).
  rewrite -expr2.
  rewrite !addrA.
  rewrite lerD2r.
  rewrite !(mulrN , mulNr).
  rewrite opprK.
  rewrite -mulrA.
  rewrite [in leRHS](mulrC _ (norm w)).
  rewrite -mulrDr.
  rewrite [in leRHS](mulrC (2 ^-1)).
  rewrite -mulrDr.
  Search (2^-1).
  rewrite -div1r.
  rewrite -splitr mulr1.
  by [].
have def: defposmx u2.
admit.
rewrite defposmxP in def.
have u2neq0 : u2 != 0.
admit.
case H: (u1 == 0).
  move/eqP: H => ->.
  rewrite mulNmx.
  rewrite mul0mx.
  by rewrite mulNmx mul0mx mxE mxE oppr0.
  move: H => /negP H. 
  have u1_neq0 : u1 != 0 by apply/negP.
  move: (def u1 u1_neq0) => Hpos.
  rewrite -oppr_ge0.
  rewrite -oppr_le0.
  rewrite opprK.
  apply ltW.
  rewrite -oppr_gt0.
  rewrite mulNmx.
  rewrite !mulNmx.
  rewrite mxE.
  rewrite opprK.
  by rewrite Hpos.
End Lyapunov.
