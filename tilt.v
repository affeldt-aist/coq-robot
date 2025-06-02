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

Section problem_statement.
Context {K : realType}.
Variable W : Frame.t K. (* world frame *)
Variable L : Frame.t K. (* sensor frame *)
Variable v : K -> 'rV[K]_3. (* linear velocity *)
Variable w : 'rV[K]_3. (* angular velocity *)
Variable g0 : K. (* standard gravity constant *)
Variable R : K -> 'M[K]_3. (* orientation of the IMU w.r.t. the world *)
Let ez : 'rV[K]_3 := 'e_2.
Variable m : 'rV[K]_3.

Definition rhs23 t :=
  v t *m \S(w) + derive1mx v t + g0 *: ez *m (R t)^T.

Definition rhs24 t := m *m (R t)^T.

Definition eqn25 t := derive1mx R t = R t *m \S(w).

Definition x1 := v.

Definition x2 t := ez *m (R t)^T.

Definition x3 t := m *m (R t)^T.

End problem_statement.

Section basic_facts.
Context {K : realType}.

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

About subr0.
Search "subr0".
Locate subr0.
Lemma fact213 (v w : 'rV[K]_3) : \S(v) * \S(w) * \S(v) = - (v *m w^T) ``_0 *: \S(v).
Proof.
  rewrite fact212.
  rewrite mulrBl.
  rewrite -mulmxE.
  Search (_*m_) (_*_).
  rewrite -mulmxA.
  have: v *m \S(v) = 0.
  apply: trmx_inj.
  Search ( _ *m _^T).
  rewrite trmx_mul.
  Search ( \S(_)^T ).
  rewrite tr_spin.
  Search (\S(_) ) 0.
  rewrite mulNmx.
  About mulNmx.
  rewrite spin_mul_tr.
  (*Unset Printing Notations.*)
  rewrite trmx0.
  rewrite oppr0.
  by [].
  move => ->.
  rewrite mulmx0.
  rewrite sub0r.
  Search (_*m _) (_*: _).
  Search ( _%:A).
  rewrite -mul_scalar_mx.
  rewrite -mulNmx.
  congr (_ *m _).
  rewrite scalemx1.
  rewrite rmorphN /=. (* simpl*)
  by [].
Qed.
Lemma fact215 ( v w : 'rV[K]_3) : \S(w *m \S(v)) = \S(w) * \S(v) - \S(v) * \S(w).
Proof.
  Search ( \S(_ )).
  Search (_*v_) (_*m_).
  rewrite spinE.
  rewrite spin_crossmul.
  by [].
Qed.

Lemma fact216 (v w : 'rV[K]_3): \S(w *m \S(v)) = v^T *m w - w^T *m v.
Proof.
  rewrite fact215.
  
  rewrite !fact212.
  Search (_%:A).
  rewrite -!/(_ *d _).
  Search (_^T).
  Search "dotmulC".
  rewrite dotmulC.
  rewrite opprB.
  rewrite addrA.
  rewrite subrK.
  by [].
Qed.
Search (\S(_)).
Lemma fact217 (v : 'rV[K]_3): \S(v) ^+ 3 = - (norm v ^+2) *: \S(v).
  (*Set Printing All.*)
  exact: spin3.
Qed.

Search "cV".
(* ligne!, R est une matrice de rotation, chaque v_i est un vecteur >
 trouver la notation indicielle  *)
Lemma fact214 (R : 'M[K]_3) (v_ : seq 'rV[K]_3) : R \is 'SO[K]_3 -> R^T * (\prod_(i <- v_) \S( i )) * R =  (\prod_(i <- v_) \S( i *m R)).
(* cest spin_similarity mais avec une somme. neutraliser la somme?*)
Proof.
move => RSO.
elim/big_ind2 : _ => //.
  rewrite -!mulmxE.
  rewrite mulmx1.
  rewrite rotation_tr_mul.
  by [].
  by [].
- move => a b c d.
  move => H1 H2.
  rewrite -H1 //.
  rewrite -H2 //.
  rewrite -!mulmxE.
  About rotation_tr_mul.
  (*Set Printing Parentheseses*)
  Search "mulrC".
  Search "mulmxA".
  Search "rotation_tr_mul".
  Search "trmx".

  rewrite -!rotation_inv.
  rewrite !mulmxA.
  rewrite -mulmxA -(mulmxA).
  admit.
  About spin_similarity.
  Print is_true.
- (*move => i _.
  exact: spin_similarity.*)
  Admitted.
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

Definition equilibrium_points := [set p : T | is_solution (cst p)].

Definition state_space :=
  [set p : T | exists y, is_solution y /\ p \in range y].

End ode.

Section eqn33.
Context {K : realType}.
Variable alpha1 : K.
Hypothesis alpha1_gt0 : 0 < alpha1.
Variable gamma : K.
Hypothesis gamma_gt0 : 0 < gamma.
Local Open Scope classical_set_scope.

Definition eqn33 t (zp1_z2 : K -> 'rV[K]_6) : 'rV[K]_6 :=
  let zp1 t := @lsubmx _ 1 3 3 (zp1_z2 t) in
  let z2 t := @rsubmx _ 1 3 3 (zp1_z2 t) in
  row_mx (- alpha1 *: zp1 t)
         (gamma *: (z2 t - zp1 t) *m \S('e_2%:R - z2 t) ^+ 2).

Lemma thm11a : state_space eqn33 = Gamma1.
Proof.
apply/seteqP; split.
  move=> p.
  rewrite /state_space /Gamma1/=.
  admit.
admit.
Admitted.

Definition point1 : 'rV[K]_6 := 0.
Definition point2 : 'rV[K]_6 := @row_mx _ _ 3 _ 0 (2 *: 'e_2%:R).

Lemma equilibrium_point1 : point1 \in equilibrium_points eqn33.
Proof.
Admitted.

Lemma equilibrium_point2 : point2 \in equilibrium_points eqn33.
Proof.
Admitted.

Lemma tractories_converge (y : K -> 'rV[K]_6) : is_solution eqn33 y ->
  y t @[t --> +oo] --> point1 \/ y t @[t --> +oo] --> point2.
Proof.
move=> is_sol_y.
Abort.

End eqn33.
