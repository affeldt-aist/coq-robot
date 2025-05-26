From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import boolp classical_sets reals topology normedtype derive.
Require Import ssr_ext euclidean rigid frame skew derive_matrix.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Definition S2 (K : realType) : Type := { x : 'rV[K]_3 | norm x = 1 }.

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

Lemma fact212 (v w : 'rV[K]_3) : \S(v) *m \S(w) = w^T *m v - (v *m w^T)``_0 *: 1.
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

End basic_facts.
