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
Context {K : realType} {T : normedModType K}.
Local Open Scope classical_set_scope.

Variable f : K -> (K -> T) -> T.

Definition is_solution (x : K -> T) : Prop :=
  forall t, x^`() t = f t x.

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
apply/seteqP. split.  
  - move=> p.
    rewrite /state_space /Gamma1 /eqn33 /is_solution /=.
    move=> y. 
    Search (norm) 1.
    destruct y as [y0 [Heq Hrange]].
    admit.
    move => p.
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
move => t ; rewrite derive1_cst /eqn33 /point1 ; apply/eqP ; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP. split.
  rewrite scaler_eq0; apply/orP; right; apply/eqP/rowP; move => i; by rewrite !mxE.
  apply/eqP/rowP; move => i; apply/eqP; set N := (X in _ *: X *m _); have : N = 0.
    rewrite /N /=; apply /rowP; move => a; by rewrite !mxE subr0.
  move => n; by rewrite n scaler0 mul0mx.
Qed.

From mathcomp Require Import fintype.
Lemma equilibrium_point2 : is_equilibrium_point eqn33 point2.
Proof.
move => t; rewrite derive1_cst; apply /eqP; rewrite eq_sym (@row_mx_eq0 _ 1 3 3); apply/andP.
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

Definition err_vec {R : ringType} n (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Definition partial {R : realType} {n : nat} (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) i :=
  lim (h^-1 * (f (a + h *: err_vec i) - f a) @[h --> 0^'])%classic.

Definition gradient {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :=
  \row_(i < n.+1) partial f a i.

Lemma gradientE {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :
  gradient f a = \sum_(i < n.+1) partial f a i *: 'e_i.
Proof.
rewrite /gradient [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

Lemma lsubmx0 {R : nmodType} m n1 n2 : @lsubmx R m n1 n2 0 = 0.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma rsubmx0 {R : nmodType} m n1 n2 : @rsubmx R m n1 n2 0 = 0.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

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

Definition LieDerivative {R : realType} n (V : 'rV[R]_n.+1 -> R) (x : R -> 'rV[R]_n.+1) (t : R) : R :=
  let xdot_t := (x^`()) t in
  gradient V (x t) *d xdot_t.

Definition is_lyapunov_function n
  (f : K -> (K -> 'rV[K]_n.+1) -> 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> K)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0,
  locposdef V x0 &
  forall traj : K -> 'rV[K]_n.+1,
    is_solution f traj ->
    traj 0 = x0 ->
    lnsd (LieDerivative V traj) 0].

Variable x1_hat : K -> 'rV[K]_3.
Variable x2_hat : K -> 'rV[K]_3.
Hypothesis alpha1_gt0 : 0 < alpha1.

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

Definition V1 (eq_result : 'rV[K]_6) : K :=
  let zp1 := @lsubmx K 1 3 3 eq_result in
  let z2 := @rsubmx K 1 3 3 eq_result in
  (norm zp1)^+2 / (2%:R * alpha1) + (norm z2)^+2 / (2%:R * gamma).
Search ( {ffun _ -> _} ).

Definition ffun_to_rV6 (f : {ffun 'I_1 * 'I_6 -> K}) : 'rV_6 :=
  \row_(i < 6) f (ord0, i).

Lemma V1_is_lyapunov : is_lyapunov_function eqn33 V1 point1.
Proof.
split; first exact: equilibrium_point1.
(*  lpd V1 point1 /\
  (forall traj : K -> 'rV_6,
   is_solution eqn33 traj -> traj 0 = point1 -> lnsd [eta LieDerivative V1 traj] 0)*)
(* v1 at point 1 is positive definite*)
- rewrite /locposdef; split.
  + by rewrite /V1 /point1 lsubmx0 rsubmx0 norm0 expr0n/= !mul0r add0r.
  (*   \forall z \near 0^', 0 <
                       norm (lsubmx z) ^+ 2 / (2 * alpha1) + norm (rsubmx z) ^+ 2 / (2 * gamma)*)
  have alpha1_pos: 0 < 2 * alpha1 by rewrite mulr_gt0 // ltr0Sn.
  have gamma_pos: 0 < 2 * gamma by rewrite mulr_gt0 //  gamma_gt0.
  near=> z_near.
  simpl in *.
  set z_rv := ffun_to_rV6 (\val z_near).
  have z_neq0 : z_near != 0 by near: z_near; exact: nbhs_dnbhs_neq.
  have z_mat_neq0 : z_rv != 0.
    rewrite /z_rv.
    rewrite /ffun_to_rV6.
    apply: contra z_neq0 => /eqP H.
    apply/eqP/rowP => i.
    rewrite !mxE.
    move/rowP : H => /(_ i).
    by rewrite !mxE//.
  rewrite /V1.
  have /orP[ lz0| rz0] : (@lsubmx _ _ 3 3 z_near != 0) || (@rsubmx _ _ 3 3 z_near != 0).
    rewrite -negb_and.
    apply: contra z_neq0 => /andP[/eqP l0 /eqP r0].
    rewrite -[eqbLHS](@hsubmxK _ _ 3 3) l0 r0.
    apply/eqP/rowP; move => i; rewrite !mxE /=; case: splitP.
      move => j k. by rewrite mxE.
    move => k i3k. by rewrite mxE.  
  - set rsub :=  @rsubmx _ _ 3 3 z_near.
    have : norm(rsub) >= 0 by rewrite norm_ge0.
    set lsub :=  @lsubmx _ _ 3 3 z_near.
    move => nor.
    have : norm(lsub) > 0.
    rewrite lt_neqAle.
    by rewrite eq_sym norm_eq0 lz0 /= norm_ge0.
    move => normlsub.
    Search (_ < _ + _).
    apply: ltr_pwDl.
    rewrite divr_gt0 //.
      by rewrite exprn_gt0 //.
      rewrite divr_ge0 //.
      by rewrite exprn_ge0 //.
      by apply ltW.
  - apply: ltr_pwDr.
      rewrite divr_gt0 //.
      rewrite exprn_gt0 //.
      rewrite lt_neqAle.
      Search (norm) 0.
      rewrite eq_sym.
      by rewrite norm_eq0 rz0 /= norm_ge0.
      rewrite divr_ge0 // ?exprn_ge0 // ?norm_ge0 //.
      by apply ltW.
- move => traj dtraj.
  rewrite /LieDerivative /V1 /point1 /lnsd.
  move => traj0.
  rewrite gradientE; elim/big_ind : _ => //.
  split.
    by rewrite dotmul0v.
    near=> z_near.
    rewrite gradientE; elim/big_ind : _ => //.
    by rewrite dotmul0v.
    move => x y s v.
    rewrite dotmulDl /= -oppr_ge0 -oppr_le0 /= opprK -oppr_ge0 opprD addr_ge0.
    by [].
    by rewrite oppr_ge0.
    by rewrite oppr_ge0.
    move => i f. 
    rewrite /partial.
    rewrite !sqr_norm.
    elim/big_ind : _ => //.
    elim/big_ind : _ => //.
    rewrite !mul0r !add0r /=.
    have /cvg_lim: (h^-1 * (norm (lsubmx ((traj z_near 
   + h *: (\row_j (i == j)%:R : 'rV_6)) : 'rV_(3+3))) ^+ 2 / (2 * alpha1) + 
   norm (rsubmx ((traj z_near + h *: (\row_j (i == j)%:R : 'rV_6)) : 'rV_(3+3))) ^+ 2 / (2 * gamma) - 0) 
   @[h --> 0^']) --> (0:K).
    set v := (\row_j (i == j)%:R : 'rV_6).
    have v_structure: v = \row_j (i == j)%:R.
    by rewrite /v.
    have taylor: forall h, 
    norm (traj z_near + h *: v) ^+ 2 = 
    norm (traj z_near) ^+ 2 + 
    2 * h * dotmul (traj z_near) v + 
    h^2 * norm v ^+ 2.
      move=> h.
      rewrite !dotmulE.
      have norm_expand: norm (traj z_near + h *: v) ^+ 2 = 
    (traj z_near + h *: v) *d (traj z_near + h *: v).
        rewrite !dotmulE.
        rewrite /norm /= dotmulE.
        rewrite sqr_sqrtr //.
        apply: sumr_ge0 => k _.
        rewrite sqr_ge0.
        by [].
      rewrite norm_expand.
      rewrite dotmulDl dotmulDr.
      rewrite -!dotmulE /=.
      rewrite dotmulDr.
      rewrite dotmulZv dotmulvZ.
      rewrite (dotmulC v (traj z_near)).
      rewrite dotmulvZ dotmulZv.
      rewrite mulrDl. 
      rewrite mulrA -expr2.
      rewrite -!dotmulvv. 
      rewrite mul1r.  
      rewrite -mulr2n.   
      ring.
      have /cvg_lim: h^-1 *
    ((norm (lsubmx ((traj z_near + h *: v) : 'rV_(3 + 3))) ^+ 2) / (2 * alpha1) +
     (norm (rsubmx ((traj z_near + h *: v) : 'rV_(3 + 3))) ^+ 2) / (2 * gamma) - 0)
    @[h --> 0^'] --> 0.
      pose F h := h^-1 *
    ((norm (lsubmx ((traj z_near + h *: v) : 'rV_(3 + 3))) ^+ 2) / (2 * alpha1) +
     (norm (rsubmx ((traj z_near + h *: v) : 'rV_(3 + 3))) ^+ 2) / (2 * gamma) - 0).
      have split_norm :
    forall u : 'rV_(3 + 3),
      norm u ^+ 2 = norm (lsubmx u) ^+ 2 + norm (rsubmx u) ^+ 2.
      move=> u.
      admit.
      admit.
  (* generalize to lsubmx and rsubmx*)
      admit.
      admit.
      move => x y s v.
      admit.
      move => i0 t.
       have equilibrium : eqn33 z_near traj = 0.
       admit.
  admit.
    move => x y s v.
    admit.
    move => i0 t.
    admit.
    move => x y s v.
    split.
    admit.
    near=> z.
     rewrite gradientE; elim/big_ind : _ => //.
     by rewrite dotmul0v.
     move=> x0 y0 b a.
     rewrite dotmulDl.
     Search "dotmul".
     rewrite -[X in X <= 0]addr0.
     rewrite -subr_le0.
     have : 0 - (x + y) = (-x) + (-y).
     Search "oppr".
     rewrite opprD.
     by rewrite add0r.
     move => i.
     rewrite subr0 addr0.
     rewrite -dotmulDl.
     admit.
     move=> i0 t.
     admit.
     move => i0 t.
     split.
     rewrite traj0 /=.
     rewrite /partial !sqr_norm /=.
      elim/big_ind : _ => //.
       elim/big_ind : _ => //.
       rewrite mul0r.
       rewrite add0r.
       rewrite mul0r.
       admit.
       move=> x y s v.
       rewrite mul0r add0r /=.
       admit.
       move => i tr.
       rewrite mul0r add0r.
       admit.
       move => x y s v.
       admit.
       move => i tru.
  admit.
     near=> z_near.
      rewrite gradientE; elim/big_ind : _ => //.
      by rewrite dotmul0v.
    move => x0 y0 tr a.
    
    admit.
    move => i tru.
    rewrite /partial expr2.
    rewrite !sqr_norm.
     elim/big_ind : _ => //.
     rewrite !mul0r addr0.
     admit.
     move => x0 y0 s v.
     admit.
     move => i1 tr.
     rewrite !expr2   .
     admit.
Admitted.

End Lyapunov.
