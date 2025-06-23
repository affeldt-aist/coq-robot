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

Parameter K : realType.
Parameter W : Frame.t K. (* world frame *)
Parameter L : Frame.t K. (* sensor frame *)
Parameter v : K -> 'rV[K]_3. (* linear velocity *)
Parameter w : 'rV[K]_3. (* angular velocity *)
Parameter g0 : K. (* standard gravity constant *)
Parameter R : K -> 'M[K]_3. (* orientation of the IMU w.r.t. the world *)
Definition ez : 'rV[K]_3 := 'e_2.
Definition x1 := v.
Parameter m : 'rV[K]_3.
Definition x2 t := ez *m (R t)^T.
Definition x3 t := m *m (R t)^T.
Axiom g0_pos : 0 < g0.
Parameter alpha1 : K.
Parameter gamma : K.
Axiom gamma_gt0 : 0 < gamma.
Axiom alpha1_gt0 : 0 < alpha1.
Section problem_statement.

Definition rhs23 t :=
  v t *m \S(w) + derive1mx v t + g0 *: ez *m (R t)^T.

Definition rhs24 t := m *m (R t)^T.

Definition eqn25 t := derive1mx R t = R t *m \S(w).

End problem_statement.

Section basic_facts.

Lemma fact212 (v w : 'rV[K]_3) : \S(v) * \S(w) = w^T *m v - (v *m w^T)``_0 *: 1.
Proof.
apply/matrix3P/and9P; split; apply/eqP;
  rewrite !(mxE,sum3E,spinij,sum1E); Simp.r.
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

Search "cV".
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

Section eqn33.

Definition eqn33 t (zp1_z2_point : K -> 'rV[K]_6) : 'rV[K]_6 :=
  let zp1_point t := @lsubmx _ 1 3 3 (zp1_z2_point t) in
  let z2_point t := @rsubmx _ 1 3 3 (zp1_z2_point t) in
  row_mx (- alpha1 *: zp1_point t)
         (gamma *: (z2_point t - zp1_point t) *m \S('e_2%:R - z2_point t) ^+ 2).

(* cauchy lipschitz par F1 qui definit un champ de vecteur lisse : 
il existe une solution depuis tout point:
gamma1 ⊆ state_space*)
(* prouver invariance geometrique, tangence donc les trajectoires restent dans gamma1:
 state_space ⊆ gamma1
Definition xi1 t (zp1_zp2 : K -> 'rV[K]_6) : Gamma1 :=
  let zp1*)

Lemma thm11a : state_space eqn33 = Gamma1.
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

Check equilibrium_points _.

Lemma equilibrium_point1 : is_equilibrium_point eqn33 point1.
Proof.
move => t ; rewrite derive1mx_cst /eqn33 /point1 ; apply/eqP ; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP. split.
  rewrite scaler_eq0; apply/orP; right; apply/eqP/rowP; move => i; by rewrite !mxE.
  apply/eqP/rowP; move => i; apply/eqP; set N := (X in _ *: X *m _); have : N = 0.
    rewrite /N /=; apply /rowP; move => a; by rewrite !mxE subr0.
  move => n; by rewrite n scaler0 mul0mx.
Qed.

From mathcomp Require Import fintype.
Lemma equilibrium_point2 : is_equilibrium_point eqn33 point2.
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
  rewrite -/N N0 subr0.
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
exact gamma_gt0.
Qed.

Open Scope classical_set_scope.
(* this lemma asks for lyapunov + lasalle*)
Lemma tractories_converge (y : K -> 'rV[K]_6) : is_solution eqn33 y ->
  y t @[t --> +oo] --> point1 \/ y t @[t --> +oo] --> point2.
Proof.
move=> is_sol_y.
Abort.

End eqn33.
Section derive_help.

Definition err_vec {R : ringType} n (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Lemma err_vecE {R : ringType} n (i : 'I_n.+1) :
  err_vec i = 'e_i :> 'rV[R]_n.+1.
Proof.
apply/rowP => j.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Definition partial {R : realType} {n : nat} (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) i :=
  lim (h^-1 * (f (a + h *: 'e_i) - f a) @[h --> 0^'])%classic.

Definition gradient_partial {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :=
  \row_(i < n.+1) partial f a i.

Definition gradient_jacobian {R : realType} n (f : 'rV[R]_n.+1 -> 'rV[R]_1) :=
  jacobian (fun x =>  (f x)).

Local Open Scope classical_set_scope.
Lemma derivemx_derive {R : realFieldType} (V : normedModType R) m n (f : V -> 'M[R]_(m.+1, n.+1)) (x0 : V) (v : V)
   (i : 'I_m.+1) (j : 'I_n.+1) :
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

Lemma gradientEE {R : realType} n (f : 'rV[R]_n.+1 -> 'rV[R]_1) (a : 'rV[R]_n.+1) :
  gradient_partial (fun x => (f x) 0 0) a = (gradient_jacobian f a)^T.
Proof.
rewrite /gradient_jacobian.
apply/rowP => i.
rewrite /gradient_partial mxE mxE /jacobian mxE -deriveE; last first.
  admit.
by rewrite partial_diff.
Admitted.

Lemma gradient_sum {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :
  gradient_partial f a = \sum_(i < n.+1) partial f a i *: 'e_i.
Proof.
rewrite /gradient_partial [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

Lemma lsubmx0 {R : nmodType} m n1 n2 : @lsubmx R m n1 n2 0 = 0.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma rsubmx0 {R : nmodType} m n1 n2 : @rsubmx R m n1 n2 0 = 0.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma dotmulsuml {R : ringType} [n : nat] (u : 'rV_n) (b : 'I_n -> 'rV[R]_n) :
  (\sum_(i < n) b i) *d u = (\sum_(i < n) b i *d u).
Proof.
elim/big_ind2 : _ => //=.
  by rewrite dotmul0v.
move=> x y r s <- <-.
by rewrite dotmulDl.
Qed.

Lemma derive_sqrt {K : realType} :
  (Num.sqrt^`())%classic = (fun t => (2 * Num.sqrt t)^-1) :> (_ -> K).
Proof.
apply/funext => i.
rewrite derive1E /=.
rewrite invrM.
Admitted.

Local Open Scope classical_set_scope.
Lemma derive_norm n (u : K^o -> 'rV[K^o]_n.+1) :
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

Section Lyapunov.
(* locally positive definite around x that is an equilibrium point *)

From mathcomp.analysis Require Import topology normedtype.
Open Scope classical_set_scope.

Definition locposdef {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z > 0.

(* locally positive semi definite*)
Definition lpsd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z >= 0.

(*locally negative semidefinite *)
Definition lnsd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z <= 0.

(*locally negative definite*)
Definition lnd  {R : realType} (T : normedModType R) (V : T -> R) (x : T) : Prop :=
  V x = 0 /\ \forall z \near 0^', V z < 0.

Local Open Scope classical_set_scope.

Definition LieDerivative {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (a : R -> 'rV[R]_n.+1) (t : R) : R :=
  \sum_(i < n.+1) (partial V (a t) i * (derive1mx a t) ``_ i).

Definition LieDerivative_gradient_jacobian {R : realType} n (V : 'rV[R]_n.+1 -> 'rV[R]_1)
    (x : R -> 'rV[R]_n.+1) (t : R) : R :=
  let xdot_t := derive1mx x t in
  (gradient_jacobian V (x t) )^T *d xdot_t.

(*Lemma LieDerivative_gradientE {R : realType} n (V : 'rV[R]_n.+1 -> R)
    (x : R -> 'rV[R]_n.+1) :
  LieDerivative_gradient V x = LieDerivative V x.
Proof.
apply/funext => t; rewrite /LieDerivative_gradient /LieDerivative.
rewrite gradientE dotmulsuml; apply: eq_bigr => /= i _.
rewrite dotmulE (bigD1 i)//= big1 ?addr0; last first.
  by move=> j ji; rewrite !mxE/= (negbTE ji) mulr0 mul0r.
by rewrite !mxE/= eqxx mulr1.
Qed.
*)

Definition is_lyapunov_function (n := 5)
  (f : K -> (K -> 'rV[K]_n.+1) -> 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> 'rV[K]_1)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0,
 locposdef (fun z => (V z) 0 0) x0 &
  forall traj : K -> 'rV[K]_n.+1,
    is_solution f traj ->
    traj 0 = x0 ->
   lnsd (fun t => (LieDerivative_gradient_jacobian V traj t)) 0].

Variable x1_hat : K -> 'rV[K]_3.
Variable x2_hat : K -> 'rV[K]_3.
Hypothesis alpha1_gt0 : 0 < alpha1.
Hypothesis gamma_gt0 : 0 < gamma.

Definition p1 t : 'rV[K]_3 :=
  let x1_t := x1 t in
  let x2_t := x2 t in
  let x1_hat_t := x1_hat t in
  x2_t + (alpha1 / g0) *: (x1_t - x1_hat_t).

Definition x2_tilde t : 'rV[K]_3 :=
  let x2_t := x2 t in
  let x2_hat_t := x2_hat t in
  (x2_t - x2_hat_t). (* dependance des conditions intiales de ^x2 qui doit etre sur S2.*)

Definition zp1_z2_eq t (zp1_z2 : K -> 'rV[K]_6) : 'rV[K]_6 :=
  let zp1 t := @lsubmx K 1 3 3 (zp1_z2 t) in
  let z2 t := @rsubmx K 1 3 3 (zp1_z2 t) in
  row_mx ((p1 t) *m R t) ((x2_tilde t) *m R t).

Definition V1 (zp1_z2 : 'rV[K]_6) : 'rV[K]_1 :=
  let zp1 := @lsubmx K 1 3 3 (zp1_z2) in
  let z2 := @rsubmx K 1 3 3 (zp1_z2) in
  ((norm (zp1))^+2 / (2%:R * alpha1) + (norm (z2))^+2 / (2%:R * gamma))%:M.

Definition ffun_to_rV6 (f : {ffun 'I_1 * 'I_6 -> K}) : 'rV_6 :=
  \row_(i < 6) f (ord0, i).

Definition V1dot (zp1_z2 : 'rV[K]_6) : K :=
  let zp1 := @lsubmx K 1 3 3 (zp1_z2) in
  let z2 := @rsubmx K 1 3 3 (zp1_z2) in
  - (norm zp1)^+2 + (z2 *m (\S('e_2%:R - z2))^+2 *m z2^T
                    - z2 *m (\S('e_2%:R - z2))^+2 *m zp1^T)``_0.

Lemma LieDerivative_gradient_jacobianD {R : realType} n
    (f g : 'rV_n.+1 -> 'cV_1) (x : R -> 'rV_n.+1) :
  LieDerivative_gradient_jacobian (f + g) x =
  LieDerivative_gradient_jacobian f x + LieDerivative_gradient_jacobian g x.
Admitted.

Lemma deriveV1 (x : K -> 'rV[K]_6) t : is_solution eqn33 x ->
  LieDerivative_gradient_jacobian V1 x t = V1dot (x t).
Proof.
move=> eqn33x.
pose zp1 := fun r => @lsubmx K 1 3 3 (x r).
pose z2 := fun r => @rsubmx K 1 3 3 (x r).
transitivity (alpha1^-1 * (('D_1 zp1 t) *d zp1 t) +
              (gamma^-1 * (('D_1 z2 t) *d z2 t))).
  rewrite /V1.
  rewrite [X in LieDerivative_gradient_jacobian X _ _](_ : _ =
    (fun zp1_z2 : 'rV_6 =>
     (norm (@lsubmx _ 1 3 3 zp1_z2) ^+ 2 / (2 * alpha1))%:M)
    +
    (fun zp1_z2 : 'rV_6 =>
     (norm (@rsubmx _ 1 3 3 zp1_z2) ^+ 2 / (2 * gamma))%:M)
    ); last first.
    apply/funext => y/=.
    rewrite fctE.
    by rewrite raddfD.
  rewrite LieDerivative_gradient_jacobianD; congr +%R.
    rewrite /LieDerivative_gradient_jacobian.
    rewrite /gradient_jacobian.
    rewrite /dotmul.
    rewrite -trmx_mul.
    rewrite -derivemxE; last first.
      admit.
    rewrite [X in 'D_(derive1mx x t) X _](_ : _ =
      ((2 * alpha1)^-1%:M \*o
       (fun x0 : 'rV_6 => (norm (@lsubmx _ 1 3 3 x0) ^+ 2)%:M))); last first.
        admit.
    transitivity (((2 * alpha1)^-1 *:
      'D_(derive1mx x t) (fun x0 : 'rV_6 => (norm (@lsubmx _ 1 3 3 x0) ^+ 2)%:M : 'rV_1) (x t))^T 0 0).
      admit.
    transitivity ((((2 * alpha1)^-1 *:
      'D_(derive1mx x t) (fun x0 : 'rV_6 => (norm (@lsubmx _ 1 3 3 x0) ^+ 2)) (x t))%:M : 'rV_1)^T 0 0).
      admit.
    rewrite (@deriveX K 'rV[K]_6 (fun x0 : 'rV_6 => norm (@lsubmx _ 1 3 3 x0)) 1 (x t) (derive1mx x t)); last first.
      admit.
    rewrite !scalerA mulrA invfM expr1 (mulrAC 2^-1) mulVf ?pnatr_eq0// div1r.
    rewrite -scalerA !mxE eqxx mulr1n; congr *%R.
Abort.


Lemma V1_is_lyapunov : is_lyapunov_function eqn33 V1 point1.
Proof.
split; first exact: equilibrium_point1.
- rewrite /locposdef; split.
  + by rewrite /V1 /point1 lsubmx0 rsubmx0 norm0 expr0n/= !mul0r add0r mxE /=.
  + near=> z_near.
    simpl in *.
    set z_rv := ffun_to_rV6 (\val z_near).
    have z_neq0 : z_near != 0 by near: z_near; exact: nbhs_dnbhs_neq.
    have z_mat_neq0 : z_rv != 0.
      apply: contra z_neq0 => /eqP H.
      apply/eqP/rowP => i; rewrite !mxE.
      by move/rowP : H => /(_ i); rewrite !mxE.
    rewrite /V1.
    have /orP[lz0|rz0] : (@lsubmx _ _ 3 3 z_near != 0) || (@rsubmx _ _ 3 3 z_near != 0).
      rewrite -negb_and.
      apply: contra z_neq0 => /andP[/eqP l0 /eqP r0].
      rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
      by apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP => ? ?; rewrite mxE.
    + set rsub := @rsubmx _ _ 3 3 z_near.
      have : norm rsub >= 0 by rewrite norm_ge0.
      set lsub :=  @lsubmx _ _ 3 3 z_near.
      move => nor.
      have normlsub : norm lsub > 0 by rewrite norm_gt0.
      rewrite mxE /= ltr_pwDl//.
        by rewrite divr_gt0 ?exprn_gt0// mulr_gt0.
      by rewrite divr_ge0 ?exprn_ge0// mulr_ge0// ltW.
    - rewrite mxE /= ltr_pwDr//.
        by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0// norm_gt0.
      by rewrite divr_ge0 ?exprn_ge0 ?norm_ge0// mulr_ge0// ltW.
- move=> traj dtraj traj0.
  rewrite /lnsd /LieDerivative_gradient_jacobian.
  rewrite traj0 /point1.
  split.
  + rewrite derive1mxE' /gradient_jacobian /V1.
    rewrite !derive1E.
    rewrite /dotmul.
    rewrite -trmx_mul /= mxE.
    rewrite /is_solution /derive1mx /eqn33 in dtraj.
    set f_expr := fun x : 'rV_6 =>
                     (norm (@lsubmx K 1 3 3 x) ^+ 2 / (2 * alpha1) +
                      norm (@rsubmx K 1 3 3 x) ^+ 2 / (2 * gamma))%:M.
    pose phi := fun t => f_expr (traj t).
    rewrite /traj0.
    have eq_point1 : 'D_1 traj 0 = 0.
      rewrite /dtraj /traj0.
      have deriv_at_0: \matrix_(i, j) (fun x : K => traj x i j)^`() 0 =
        row_mx (- alpha1 *: (@lsubmx K 1 3 3 (traj 0)))
         (gamma *: ((@rsubmx K 1 3 3 (traj 0)) - (@lsubmx K 1 3 3 (traj 0))) *m
          \S('e_2 - (@rsubmx K 1 3 3 (traj 0))) ^+ 2).
        exact: dtraj.
      have deriv_at_point1 : 'D_1 traj 0 =
        row_mx (- alpha1 *: @lsubmx K 1 3 3 (traj 0))
         (gamma *: (@rsubmx K 1 3 3 (traj 0) - @lsubmx K 1 3 3 (traj 0)) *m
          \S('e_2 - @rsubmx K 1 3 3 (traj 0)) ^+ 2).
        rewrite -deriv_at_0.
        rewrite -derive1E /=.
        apply/matrixP => i j; rewrite !mxE.
        rewrite ord1.
        by rewrite derive1E derivemx_derive// -derive1E.
      have eq_zero: row_mx (- alpha1 *: @lsubmx K 1 3 3 point1)
        (gamma *: (@rsubmx K 1 3 3 point1 - @lsubmx K 1 3 3 point1) *m
         \S('e_2 - @rsubmx K 1 3 3 point1) ^+ 2) = 0.
        have := equilibrium_point1 0.
        rewrite /is_equilibrium_point /eqn33.
        move => H.
        rewrite /point1. apply/matrixP => i j.
        rewrite !linear0 addr0.
        rewrite addr0. rewrite scaler0 mul0mx.
        by rewrite row_mx0.
      have traj_deriv_zero: 'D_1 traj 0 = 0.
        rewrite deriv_at_point1.
        rewrite traj0.
        by rewrite eq_zero.
      by rewrite traj_deriv_zero.
    rewrite eq_point1.
    rewrite mul0mx /=.
    by rewrite mxE.
  + near=> z.
    rewrite derive1mxE'.
    rewrite /gradient_jacobian /=.
    rewrite /dotmul /=.
    rewrite /is_solution /derive1mx /eqn33 in dtraj.
    rewrite -trmx_mul /=. rewrite mxE /=.
    rewrite /V1 /=.
    rewrite -derivemxE /=; last first.
      admit.
    rewrite [x in ('D_ _ x _)] (_ : _ = (fun x0 : 'rV_6 =>
               (norm (@lsubmx K 1 3 3 x0) ^+ 2 / (2 * alpha1))%:M) \+
               (fun x0 => (norm (@rsubmx K 1 3 3 x0) ^+ 2 / (2 * gamma))%:M)); last first.
      by apply/funext => v/=; rewrite !raddfD.
    rewrite deriveD /=; last 2 first.
      admit.
      admit.
    rewrite mxE.
    rewrite [x in ('D_ _ x _) ](_ : _ = alpha1^-1 * 2^-1 \*:
        (fun x0 : 'rV_6 => (norm (@lsubmx K 1 3 3 x0) ^+ 2)%:M : 'rV[K]_1)); last first.
      apply/funext => x/=.
      by rewrite mulrC invfM (mulrC _ alpha1^-1) scale_scalar_mx.
    rewrite !deriveZ /=; last first.
      admit.
    under [in X in _ + X] eq_fun => x0.
      rewrite [_ / (2 * gamma)]mulrC.
      over.
    rewrite /=.
    rewrite [X in _ + X <= 0] (_ : _ =
      (2 * gamma)^-1 *: 'D_((traj^`())%classic z)
        (fun x0 : 'rV[K]_6 => (norm (@rsubmx K 1 3 3 x0) ^+ 2)%:M : 'rV[K]_1) (traj z) 0 0); last first.
      admit.
    pose f := fun x0 : 'rV_6 => (norm (@lsubmx K 1 3 3 x0))%:M : 'rV[K]_1.
    pose F := fun x0 : 'rV_6 => (f x0) ^+ 2.
    set dF_l : 'rV[K]_1 := 'D_((traj^`())%classic z)
             (fun x0 : 'rV_6 => (norm (@lsubmx K 1 3 3 x0) ^+ 2)%:M) (traj z).
    rewrite !mxE.
    set a := alpha1^-1 * 2^-1.
    set b := (2 * gamma)^-1.
    set dF_r : 'rV[K]_1 := 'D_((traj^`())%classic z)
               (fun x0 : 'rV[K]_6 => (norm (@rsubmx K 1 3 3 x0) ^+ 2)%:M) (traj z).
    have: dF_l``_0 = (2 *: (@lsubmx K 1 3 3 (traj z)) 0 0).
    rewrite /dF_l.
    set u := fun t => @lsubmx K 1 3 3 (traj t).
    have Hderiv :
      ((2^-1 \*o (GRing.exp (R:=K))^~ 2 \o norm (n:=3)) \o u)^`() =
        (fun t => (derive1mx u t *m (u t)^T) 0 0).
      apply: derive_norm => t.
      rewrite norm_eq0.
      admit.
    have: dF_r``_0 = 2 * (@rsubmx K 1 3 3 (traj z)) 0 0.
      set v := fun t => @rsubmx K 1 3 3 (traj t).
      have -> : dF_r``_0 = ((fun t => (derive1mx v t *m (v t)^T) 0 0) z).
        rewrite /dF_r. rewrite -!derive1mxE'.
        set g := fun (x0 : 'rV_6) => ((norm (@rsubmx K 1 3 3 x0)) ^+ 2)%:M.
        have : ('D_(derive1mx traj z) g (traj z)) 0 0
               = ((fun t => norm (v t)) ^+ 2)^`() z.
          rewrite derivemx_derive//.
          rewrite derive1E//=.
          admit.
        move => etc.
        rewrite /g.
        rewrite etc.
        rewrite derive1E.
        rewrite deriveX /=.
          admit.
        admit.
      admit.
   admit.
rewrite /v /derive1mx.
move => d.
rewrite /a /b /=.
rewrite -oppr_ge0 /=.
have ab_pos : 0 < a + b.
 rewrite addr_gt0//.
   by rewrite mulr_gt0 ?invr_gt0.
 by rewrite invr_gt0 ?mulr_gt0.
have : (@lsubmx K 1 3 3 (traj z))``_0 = (dF_l``_0 / 2).
  have Hrsubmx_eq : (@rsubmx K 1 3 3 (traj z))``_0 = (dF_r``_0) / 2.
    admit.
  admit.
admit.
Admitted.

End Lyapunov.
