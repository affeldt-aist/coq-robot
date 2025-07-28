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

(* spin and matrix/norm properties *)

Lemma tr_sqr_spin {R : realFieldType} (u : 'rV[R]_3) :
  (\S(u) ^+ 2)^T = \S(u) ^+ 2.
Proof. by apply/esym/eqP; rewrite -symE; exact: sqr_spin_is_sym. Qed.

Lemma mul_tr_spin {R : comNzRingType} (u : 'rV[R]_3) : u *m \S(u)^T = 0.
Proof. by apply: trmx_inj; rewrite trmx_mul trmxK spin_mul_tr trmx0. Qed.

Lemma CauchySchwarz_vec {R : realType} {n : nat} (a b : 'rV[R]_n.+1) :
  (a *d b)^+2 <= (a *d a) * (b *d b).
Proof.
suffices: 0 <= (b *d b) * (a *d a) - (a *d b) ^+ 2.
  rewrite -subr_ge0.
  rewrite mulrC.
  exact.
rewrite subr_ge0 expr2 mulrC !dotmulvv /= -expr2.
have [->|hb] := eqVneq b 0.
  rewrite dotmulv0 expr0n.
  rewrite norm0.
  rewrite expr0n //=.
  by rewrite mul0r.
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
  rewrite dotmulvZ dotmulC dotmulvv /t expr2 -!expr2 dotmulZv dotmulvv.
  rewrite divfK /=; last first.
    by rewrite sqrf_eq0 norm_eq0.
  by rewrite subrr subr0 !expr2 mulrAC.
have h2 : 0 <= norm b ^+ 2 * (a *d a) - (a *d b) ^+ 2.
  have pos: 0 < norm b ^+ 2.
    by rewrite exprn_gt0 // norm_gt0.
  suff: norm b ^+ 2 * (a *d a - (a *d b) ^+ 2 / norm b ^+ 2) =
      norm b ^+ 2 * (a *d a) - (a *d b) ^+ 2.
    move=> eq_step.
    rewrite -eq_step.
    by apply: mulr_ge0; [rewrite ltW | exact h1].
  rewrite mulrBr.
  congr (_ - _)%R.
  by rewrite mulrCA divff ?mulr1// sqrf_eq0 norm_eq0.
rewrite -subr_ge0 mulrC.
by rewrite dotmulvv mulrC in h2.
Qed.

(* not used *)
Lemma young_inequality_vec {R : realType} {n : nat} (a b : 'rV[R]_n.+1) :
  (a *d b) <= (2^-1 * (norm a)^+2) + (2^-1 * (norm b)^+2).
Proof.
have normage0 : 0 <= (norm a)^+2.
  rewrite expr2.
  by rewrite mulr_ge0 // norm_ge0.
have normbge0 : 0 <= (norm(b))^+2.
  rewrite expr2.
  by rewrite mulr_ge0 // norm_ge0.
rewrite -!dotmulvv.
have: 0 <= norm(a - b)^+2.
  rewrite expr2.
  by rewrite mulr_ge0 // norm_ge0.
rewrite -dotmulvv dotmulD !dotmulvv.
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

Lemma dotmulspin1 {R : numFieldType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
  (u *m \S(v)) *d v = 0.
Proof.
apply/eqP.
rewrite dotmulC dotmul_trmx -normalvv normal_sym mul_tr_spin normalvv.
by rewrite dotmulv0.
Qed.

Lemma dotmulspin2 {R : numFieldType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
  (u *m \S(v)) *d u = 0.
Proof.
apply/eqP.
rewrite -normalvv normal_sym spinE -normalmN (@lieC _ (vec3 R)) /= opprK.
by rewrite crossmul_normal.
Qed.

Lemma ortho_spin {R : numFieldType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
  (u - v) *d (v *m \S(u))= 0.
Proof. by rewrite dotmulBl dotmulC dotmulspin1 dotmulC dotmulspin2 subr0. Qed.

Lemma norm_squared {R : rcfType} n (u : 'rV[R]_n) :
  (u *m (u)^T) 0 0 = norm u ^+2.
Proof. by rewrite -dotmulvv /dotmul. Qed.

Lemma derive1mx_rsubmx {R : realType} :
  forall (f : R -> 'rV[R]_(3 + 3)) (t : R),
  'D_1 (fun x => rsubmx (f x)) t = @rsubmx R _ 3 3 ('D_1 f t).
Proof.
move=> f t.
apply/matrixP => i j.
rewrite !mxE /=.
rewrite /rsubmx /=.
(*under eq_fun do rewrite mxE mxE.
symmetry.
by under eq_fun do rewrite mxE.
Qed.*) Admitted.

Lemma derive1mx_lsubmx {R : realType} :
  forall (f : R -> 'rV[R]_(3 + 3)) (t : R),
  'D_1 (fun x => lsubmx (f x)) t = @lsubmx R _ 3 3 ('D_1 f t).
Proof.
move=> f t.
(*rewrite /derive1mx.
rewrite -!derive1mx_matrix /=.
apply/matrixP => i j.
rewrite !mxE /=.
rewrite /lsubmx /=.
under eq_fun do rewrite mxE mxE.
symmetry.
by under eq_fun do rewrite mxE.
Qed.*) Admitted.
