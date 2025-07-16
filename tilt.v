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

(* spin and matrix/norm properties*) 
Lemma sqr_spin_tr  {R : realType} (u : 'rV[R]_3) : (\S(u) ^+ 2)^T = \S(u) ^+ 2.
Proof. apply/esym/eqP; rewrite -symE ; exact: sqr_spin_is_sym. Qed.

Lemma tr_spin_mul {R : realType} (u : 'rV[R]_3) : u *m \S(u)^T = 0.
Proof. by apply: trmx_inj ; rewrite trmx_mul trmxK spin_mul_tr trmx0. Qed.

Lemma norm_spin {R : realType} (u : 'rV[R]_3) (v : 'rV[R]_3) :  (u *m \S(v - u) ^+ 2 *m (u)^T) 0 0 = - norm (u *m \S(v)) ^+ 2.
Proof.
rewrite spinD spinN -tr_spin mulmxA !mulmxDr mulmxDl !tr_spin_mul.
rewrite !addr0 -dotmulvv /dotmul trmx_mul.
rewrite mxE [X in _ + X = _](_ : _ = 0) ?addr0; last first.
by rewrite tr_spin -mulmxA mulNmx spin_mul_tr mulmxN mulmx0 oppr0 mxE.
by rewrite tr_spin mulNmx mulmxN [in RHS]mxE opprK mulmxA.
Qed. 

Lemma dotmulspin1 {R : realType} (u : 'rV[R]_3) (v : 'rV[R]_3) : (u *m \S(v)) *d v = 0.
Proof. by apply/eqP ; rewrite dotmulC dotmul_trmx -normalvv normal_sym tr_spin_mul normalvv dotmulv0. Qed.

Lemma dotmulspin2 {R : realType} (u : 'rV[R]_3) (v : 'rV[R]_3) : (u *m \S(v)) *d u = 0.
Proof. by apply/eqP ; rewrite -normalvv normal_sym spinE -normalmN (@lieC _ (vec3 R)) /= opprK crossmul_normal. Qed.

Lemma ortho {R : realType} (a : 'rV[R]_3) (b : 'rV[R]_3) : (a - b) *d (b *m \S(a))= 0.
Proof. by rewrite dotmulBl dotmulC dotmulspin1 dotmulC dotmulspin2 subr0. Qed.

Lemma sqr_spin {R : realType} (u : 'rV[R]_3) (norm_u1 : norm u = 1) : \S(u) *m \S(u) = u^T *m u - 1%:M.
Proof.
have sqrspin : \S(u) ^+ 2 = u^T *m u - (norm u ^+ 2)%:A by rewrite sqr_spin.
rewrite expr2 norm_u1 expr2 mulr1 in sqrspin.
rewrite mulmxE sqrspin.
  apply/matrixP => i j.
  rewrite mxE /= [in RHS]mxE /=.
  congr (_+_).
  rewrite mxE mxE /= mul1r.
  rewrite [in RHS]mxE [in RHS]mxE /= -mulNrn.
  rewrite mxE -mulNrn.
  by [].
Qed.

Lemma norm_squared {R : realType} (n : nat) (u : 'rV[R]_n.+1) : (u *m (u)^T) 0 0  = norm (u) ^+2.
Proof. by rewrite -dotmulvv /dotmul. Qed.

Lemma sqr_inj {R : rcfType} : {in Num.nneg &, injective (fun x : R => x ^+ 2)}.
Proof. by move=> x y x0 y0 /(congr1 (@Num.sqrt R)); rewrite !sqrtr_sqr! ger0_norm. Qed.

(* PR: to MathComp *)
Lemma char_poly2 (R : numFieldType) (M : 'M[R]_2) : char_poly M = 'X^2 - (\tr M)%:P * 'X + (\det M)%:P.
Proof.
set P := (RHS).
apply/polyP => -[|[|[|i]]]; last first.
- have := (rwP (leq_sizeP (char_poly M) i.+3)).2.
  rewrite size_char_poly => /(_ erefl) /(_ i.+3) => ->//.
  rewrite (rwP (leq_sizeP P i.+3)).2//.
  rewrite /P -addrA size_addl ?size_polyXn//.
  rewrite -mulNr size_MXaddC; case: ifPn => // _.
  by rewrite ltnS -polyCN size_polyC; case: (_ == _).
- rewrite /P -[in RHS]addrA [RHS]coefD coefXn/= coefD -mulrN coefCM coefC/= coefN coefX/= oppr0 mulr0 !addr0.
  rewrite /char_poly det_mx22//.
  rewrite /char_poly_mx !mxE/= mulr1n mulr0n sub0r mulNr opprK sub0r mulrN.
  rewrite coefD coefN coefCM coefC/= mulr0 subr0.
  by rewrite coefM sum3E !coefE/= !(subr0,mul0r,mulr0,addr0,mulr1,add0r).
- rewrite char_poly_trace//.
  by rewrite /P -addrA addrCA !coefD coefN coefCM coefX/= mulr1 coefC/= addr0 coefXn addr0.
- rewrite char_poly_det sqrrN expr1n mul1r.
  by rewrite /P !coefD coefC/= coefN coefCM coefX mulr0 subr0 coefXn/= add0r.
Qed.

Lemma lsubmx_const  {R : nmodType} (r : R) m n1 n2 : lsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma rsubmx_const  {R : nmodType} (r : R) m n1 n2 : rsubmx (const_mx r : 'M_(m, n1 + n2)) = const_mx r.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

From mathcomp Require Import sequences exp realfun.

(* is it really interesting to generalize is_deriveX ?).*)
Lemma derive1_powR {K : realType} (r : K) : 1 < r -> (fun a => if a == 0 then 0 else a `^ r)^`()%classic = (fun x => if x == 0 then 0 else r * x `^ (r - 1)).
Proof.
rewrite /powR /=.
move => r1.
apply/funext => x.
case: (x == 0) => [|].
rewrite derive1E.
apply: derive_val.
have: is_derive (0 : K) (1 : K) (fun a => if a == 0 then 0 else a `^ r) 0.
rewrite /=.
Admitted.

Global Instance is_derive1_sqrt {K : realType} (x : K) : 0 < x -> is_derive x 1 Num.sqrt (2 * Num.sqrt x)^-1.
Proof.
move=> x_gt0.
have sqrtK : {in Num.pos, cancel (@Num.sqrt K) (fun x => x ^+ 2)}.
  by move=> a a0; rewrite sqr_sqrtr// ltW.
rewrite -[x]sqrtK//.
apply: (@is_derive_inverse K (fun x => x ^+ 2)).
- near=> z.
  rewrite sqrtr_sqr gtr0_norm//.
  have [xz|zx|->] := ltgtP z (Num.sqrt x); last first.
  + by rewrite sqrtr_gt0.
  + by rewrite (lt_trans _ zx)// sqrtr_gt0.
  + move: xz.
    near: z.
    exists (Num.sqrt x / 2).
      rewrite /=.
      rewrite mulr_gt0 //.
      by rewrite sqrtr_gt0 x_gt0.
      rewrite invr_gt0.
      by [].
    move=> r/=.
    move=> /[swap] rx.
    rewrite gtr0_norm ?subr_gt0//.
    rewrite ltrBlDl.
    rewrite -ltrBlDr.
    apply: le_lt_trans.
    rewrite subr_ge0.
    rewrite ger_pMr.
    rewrite invf_le1.
    by rewrite ler1n.
    by [].
    by rewrite sqrtr_gt0.
- near=> z.
  exact: exprn_continuous.
- rewrite !sqrtK//; split.
    exact: exprn_derivable (* TODO: renaming *).
  by rewrite exp_derive (* TODO: renaming -> issue *) expr1 scaler1.
- by rewrite mulf_neq0 ?pnatr_eq0// gt_eqF// sqrtr_gt0 exprn_gt0// sqrtr_gt0.
Unshelve. all: by end_near. 
Qed.

Lemma derive_sqrt {K : realType} (r : K) : 0 < r ->
   (Num.sqrt^`())%classic r = (2 * Num.sqrt r)^-1 :> K.
Proof.
move=> r0.
rewrite derive1E.
apply: derive_val.
exact: is_derive1_sqrt.
Qed.

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
  apply/eigen.
  apply/eigenvalueP.
  exists x => //.
  rewrite /=.
  apply/matrixP.
  move => i j.
(* theoreme spectral?*)
Admitted.

Lemma CauchySchwarz_vec {R : realType} {n : nat} : forall (a b : 'rV[R]_n.+1), (a *d b)^+2 <= (a *d a) * (b *d b).
Proof.
move => a b.
suffices: 0 <= (b *d b) * (a *d a) - (a *d b) ^+ 2.
  rewrite -subr_ge0.
  move => h.
  rewrite mulrC in h.
  apply h.
rewrite subr_ge0 expr2 mulrC !dotmulvv /= -expr2.
case: (boolP (b == 0)) => [/eqP b0|hb].
  rewrite b0.
  rewrite dotmulv0 expr0n.
  rewrite norm0.
  rewrite expr0n // /=.
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

Section derive_help.
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
by rewrite /derive1mx !mxE !derive1E derivemx_derive.
Qed.

Lemma partial_diff {R : realType} n (f : 'rV[R]_n.+1 -> 'rV[R]_1)  (a : 'rV[R]_n.+1)
    (i : 'I_n.+1) :
  partial (fun x => (f x) 0 0) a i =
  ('D_'e_i (fun x : 'rV[R]_n.+1 => (f x) : 'rV[R]_1) a) 0 0.
Proof.
rewrite derivemx_derive/= /partial /derive /=.
by under eq_fun do rewrite (addrC a).
Qed.

Lemma gradient_partial_sum {R : realType} n (f : 'rV[R]_n.+1 -> R) (a : 'rV[R]_n.+1) :
  gradient_partial f a = \sum_(i < n.+1) partial f a i *: 'e_i.
Proof.
rewrite /gradient_partial [LHS]row_sum_delta.
by under eq_bigr do rewrite mxE.
Qed.

Definition err_vec {R : ringType} n (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Lemma err_vecE {R : ringType} n (i : 'I_n.+1) :
  err_vec i = 'e_i :> 'rV[R]_n.+1.
Proof.
apply/rowP => j.
by rewrite !mxE eqxx /= eq_sym.
Qed.

Local Open Scope classical_set_scope.
Lemma derive_norm {K : realType} n (u : K^o -> 'rV[K^o]_n.+1) (t : K) :
  (2^-1 \*o (@GRing.exp K ^~ 2) \o @norm K n.+1 \o u)^`() t =
  (fun t => (derive1mx u t *m  (u t)^T)``_0) t :> K.
Proof.
rewrite [LHS]derive1E deriveMl/=; last first.
  admit.
rewrite -derive1E.
under eq_fun do rewrite -dotmulvv.
rewrite dotmulP mxE /= mulr1n derive1mx_dotmul ; last 2 first.
admit.
admit.
rewrite [X in _ * (_ + X) =  _]dotmulC.
by field.
Admitted.

End derive_help.

Section LieDerivative.

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
  rewrite mxE [RHS]mxE // [in LHS] /= [LHS]mxE.
  by congr (_+_); rewrite mxE.
rewrite [in LHS] mulmxDr /= mxE mxE.
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
rewrite /LieDerivative_jacobian1.
rewrite /jacobian1.
rewrite /dotmul.
rewrite -trmx_mul.
rewrite -derivemxE; last first.
  admit.
have := derive_norm.
(*move=> /( congr1 (fun z => z t)).*)
rewrite -scalemxAl [X in _ -> _ = X]mxE.
move => <-.
rewrite derive1Ml; last first.
  admit.
rewrite mulrA divff // ?pnatr_eq0 // mul1r.
rewrite !mxE.
rewrite derive1E.
transitivity ( ('D_(derive1mx x t) (fun y : 'rV_6 => (norm (f y) ^+ 2)) (x t)) ).
  admit.
rewrite deriveE ; last first.
  admit.
rewrite derive1mxE'.
rewrite derive1E.
rewrite deriveE ; last first.
  admit.
transitivity(('d (fun y : 'rV_6 => norm (f y) ^+ 2) (x t ) \o ('d x t)) 1).
by [].
rewrite -diff_comp; last 2 first. 
  admit.
  admit.
rewrite deriveE //.
admit.
Admitted.

End LieDerivative.

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

Definition is_lyapunov_candidate {K : realType} (n := 5)
   (V : 'rV[K]_n.+1 -> 'rV[K]_1)
   (x0 : 'rV[K]_n.+1) :=
   locposdef (fun z => (V z) 0 0) x0.

Definition eq_is_lyapunov_stable {K : realType} (n := 5)
  (f : K -> (K -> 'rV[K]_n.+1) -> 'rV[K]_n.+1)
  (V : 'rV[K]_n.+1 -> 'rV[K]_1)
  (x0 : 'rV[K]_n.+1) : Prop :=
  [/\ is_equilibrium_point f x0,
  is_lyapunov_candidate V x0 &
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

Definition Gamma1 := [set x : 'rV[K]_6 | norm ('e_2 - @rsubmx _ 1 3 3 x) = 1].

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
*)
Lemma thm11a : state_space (fun a b => eqn33 b a) = Gamma1.
Proof.
(* il existe une solution depuis tout point*) 
apply/seteqP; split.
- move=> p.
  rewrite /state_space /Gamma1 /eqn33 /is_solution /=.
  move=> [y0 [Heq Hrange]].
  admit.
(* toute image d'une trajectoire est dans gamma
nagumo theorem *)
- move => p.
  rewrite /state_space /Gamma1 /eqn33 /is_solution /=.
  move => norme.
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

Lemma derive_lsubE (z : K) (traj : K -> 'rV_5%R.+1) (zp1 := fun r => Lsubmx (traj r)):  (fun r : K => Lsubmx (traj r))^`() z = Lsubmx ((traj^`())%classic z).
Proof.
apply/matrixP => i j.
rewrite !derive1E.
rewrite !deriveE ; last 2 first.
  admit.
  admit.
rewrite diff_comp ; last 2 first.
  admit.
  admit.
rewrite /= -!deriveE /=.
rewrite !derivemx_derive /=.
Admitted.

Lemma derive_rsubE (z : K) (traj : K -> 'rV_5%R.+1) (zp1 := fun r => Rsubmx (traj r)) : (fun r : K => Rsubmx (traj r))^`() z = Rsubmx ((traj^`())%classic z).
Proof.
apply/matrixP => i j.
rewrite !derive1E !deriveE ; last 2 first.
  admit.
  admit.
rewrite diff_comp ; last 2 first.
  admit.
  admit.
Admitted.

Lemma derive_zp1 (z : K) (traj : K -> 'rV_5%R.+1) (zp1 := fun r => Lsubmx (traj r))  (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) :
  derive1mx zp1 z = (- alpha1 *: Lsubmx (traj z)).
Proof.
rewrite /zp1.
move : dtraj.
rewrite /is_solution /eqn33.
move=> /(_ z).
move=> /(congr1 Lsubmx).
rewrite row_mxKl.
rewrite !derive1mxE' => <-.
apply: derive_lsubE.
Qed.

Lemma derive_z2  (z : K) (traj : K -> 'rV_5%R.+1) (z2 := fun r => Rsubmx (traj r))  (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) :
   derive1mx z2 z = 
              (gamma *: (Rsubmx (traj z) - Lsubmx (traj z)) *m \S('e_2 - Rsubmx (traj z)) ^+ 2).
Proof.
rewrite /z2; move: dtraj; rewrite /is_solution /eqn33; move => /(_ z).
move => /(congr1 Rsubmx).
rewrite row_mxKr.
rewrite !derive1mxE' => <-.
apply: derive_rsubE.
Qed.

Lemma derive_V1dot (c1 := (2^-1 / alpha1)) (c2 := (2^-1 / gamma)) (z : K) (traj : K -> 'rV_5%R.+1) (zp1 := fun r => Lsubmx (traj r))
 (z2 := fun r => Rsubmx (traj r)) (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) 
  :  c1 *: (2 *: derive1mx zp1 z *m (Lsubmx (traj z))^T) 0 0 + 
        c2 *: (2 *: derive1mx z2 z *m (Rsubmx (traj z))^T) 0 0
      = V1dot (traj z).
Proof.
rewrite -scalemxAl mxE (scalerA c1 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite -scalemxAl [in X in _ + X]mxE (scalerA c2 2) mulrAC mulVf ?pnatr_eq0// div1r.
rewrite derive_zp1 // -scalemxAl mxE [X in X + _](mulrA (alpha1^-1) (- alpha1)) mulrN mulVf ?gt_eqF// mulN1r.
rewrite derive_z2 // -scalemxAl mulmxA -scalemxAl [in X in _ + X]mxE scalerA mulVf ?gt_eqF// scale1r.
rewrite norm_squared /V1dot.
congr +%R.
set Lmx := lsubmx _.
set Rmx := rsubmx _.
rewrite -2![in RHS]mulmxA -mulmxBr -mulmxBr -linearB/=.
rewrite -[X in _ = (X *m (_ *m _)) 0 0]trmxK -[X in _ = (_ *m (X *m _)) 0 0]trmxK.
rewrite mulmxA -trmx_mul -trmx_mul [RHS]mxE -(mulmxA (Rmx - Lmx)) mulmxE -expr2.
rewrite sqr_spin_tr.
by rewrite mulmxA.
Qed.

Lemma deriveV1 (x : K -> 'rV[K]_6) t : is_solution (fun a b => @eqn33 K alpha1 gamma b a) x ->
  LieDerivative_jacobian1 V1 x t = V1dot (x t).
Proof.
move=> eqn33x.
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
rewrite func_eq2 !LieDerivative_jacobian1Ml !fctE !LieDerivative_jacobian1_norm /=.
by rewrite derive_V1dot //.
Qed.

Lemma defposmxu2 (  u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2)
  [eta (fun=> 0) with (0,0) |-> 1,
                      (0,1) |-> -2^-1,
                      (1,0) |-> -2^-1,
                      (1,1) |-> 1] (i,j)): defposmx u2.
Proof.
rewrite /defposmx /u2.
split.
  - rewrite /= symE.
    apply/eqP/matrixP.
    move => i j.
    rewrite !mxE.
    case: ifPn => [/eqP[->{i} ->{j}//]|].
    case: ifPn => [/eqP[->{i} ->{j}//]|].
    case: ifPn => [/eqP[->{i} ->{j}//]|].
    case: ifPn => [/eqP[->{i} ->{j}//]|].
    by move: i j => [[|[|//]]] /= ? [[|[|]]].
  - move=> a.
    move/eigenvalueP => [u] /[swap] u0 H.
    have a_eigen : eigenvalue u2 a.
    apply/eigenvalueP.
    exists u. rewrite /u2.
    exact: H. exact: u0.
    have a_root : root (char_poly u2) a.
      rewrite -eigenvalue_root_char.
      exact : a_eigen.
    rewrite char_poly2 in a_root.
    have tr_u2 : \tr u2 = 2.
      rewrite /u2.
      rewrite /= //.
      rewrite /mxtrace /=.
      by rewrite sum2E/= !mxE/=.
    have det_u2 : \det u2 = 3/4.
      rewrite /u2 det_mx22 /= !mxE /=.
      by field.
    rewrite tr_u2 det_u2 rootE in a_root.
    have char_poly_fact : 'X^2 - 2%:P * 'X + (3/4)%:P = ('X - (1%:R / 2)%:P) * ('X - (3%:R / 2)%:P) :> {poly K}.
      rewrite mulrBr mulrBl -expr2 -!addrA; congr +%R.
      rewrite mulrBl opprB addrCA addrC; congr +%R.
        by rewrite -[RHS]polyCM; congr (_%:P); by field.
      rewrite [in RHS]mulrC -opprD -mulrDr mulrC; congr (- (_ * _)).
      by rewrite -polyCD; congr (_%:P); by field.
    rewrite char_poly_fact hornerM !hornerXsubC in a_root.
    move: a_root.
    rewrite mulf_eq0 => /orP [Ha1 | Ha2].
      rewrite subr_eq0 in Ha1.
      move/eqP : Ha1 => Ha1.
      by rewrite Ha1 divr_gt0.
    rewrite subr_eq0 in Ha2.
    move/eqP : Ha2 => Ha2.
    rewrite Ha2.
    by rewrite divr_gt0.
Qed.

Lemma V1_is_lyapunov_candidate :  is_lyapunov_candidate V1 (point1 K).
Proof.
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
Unshelve. all: by end_near.
Qed.

(* TODO: Section general properties of our system *) 

Lemma Gamma1_traj (traj : K -> 'rV_5%R.+1) (z : K)  (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) t : 
      Gamma1 (traj t). 
Proof.
rewrite -(thm11a gamma_gt0 alpha1_gt0 ).
  rewrite /state_space/=.
  exists traj.
  split => //.
  rewrite inE/=.
  by exists t.
Qed.

Lemma norm_u1 (traj : K -> 'rV_5%R.+1) (z : K) (z2 := fun r => Rsubmx (traj r)) (zp1 := fun r => Lsubmx (traj r)) (u := 'e_2 - z2 z) 
                (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) : norm u = 1. 
  rewrite /u.
  suff: Gamma1 (row_mx (zp1 z) (z2 z)).
  rewrite /Gamma1/=.
  by rewrite row_mxKr.
  rewrite /zp1 /z2.
  rewrite hsubmxK /=.
  apply/Gamma1_traj.
  rewrite //.
  by rewrite //.
Qed.

Lemma Hsq (traj : K -> 'rV_5%R.+1) (z : K)  (z2 := fun r => Rsubmx (traj r)) ( w := (z2 z) *m \S('e_2)) (u := 'e_2 - z2 z) 
  (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) : (w *m \S(u)) *d (w *m \S(u)) = (w *d w) * (u *d u) - (w *d u) ^+ 2.
Proof.
rewrite /dotmul !trmx_mul !tr_spin !mulNmx mulmxN opprK mulmxN !dotmulP.
have key_ortho : (z2 z *m \S('e_2)) *d u = 0.
 by rewrite dotmulC ; apply/ortho.
rewrite key_ortho expr2.
rewrite [in RHS]mxE.
rewrite [X in _ =  - (w *m (\S('e_2) *m (z2 z)^T)) 0 0 * (u *d u)%:M 0 0 - 0%:M 0 0 * X]mxE mulr1n mulr0 subr0/=.
rewrite /u -/w /dotmul.
have Hw_ortho : (w *d u) = 0 by rewrite /u dotmulC ortho.
rewrite !mulmxA dotmulP dotmulvv norm_u1 // expr2 mulr1.
rewrite [X in _ =  - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1n /=.
rewrite [X in _ =   - (w *m \S('e_2) *m (z2 z)^T) 0 0 * X]mxE /= mulr1.
have wu0 : w *m u^T *m u = 0 by rewrite dotmulP Hw_ortho mul_scalar_mx scale0r.
rewrite -[in LHS](mulmxA w) sqr_spin; last first.
  by rewrite -/u norm_u1.
rewrite [in LHS]mulmxBr mulmxA wu0 sub0r.
by rewrite 2!mulNmx mulmx1 mxE.
Qed.

Lemma neg_spin (traj : K -> 'rV_5%R.+1) (z : K)  (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj ): 
  norm (Rsubmx (traj z) *m \S('e_2) *m - \S('e_2 - Rsubmx (traj z))) =
  norm (Rsubmx (traj z) *m \S('e_2)).
Proof.
rewrite mulmxN normN.
pose zp1 := fun r => Lsubmx (traj r).
pose z2 := fun r => Rsubmx (traj r).
set w := (z2 z) *m \S('e_2).
have Gamma1_traj t : Gamma1 (traj t) by apply/Gamma1_traj.
rewrite /norm.
rewrite !dotmulvv [RHS]sqrtr_sqr sqrtr_sqr.
have Hnorm_sq : norm (w *m \S('e_2 - Rsubmx (traj z))) ^+ 2 = norm w ^+ 2. 
  rewrite -!dotmulvv Hsq // !dotmulvv norm_u1 /= //.
  rewrite -!dotmulvv expr2 !mul1r mulr1.
  have wu0 : w *d ('e_2 - Rsubmx (traj z)) = 0. 
    rewrite dotmulC.
    by rewrite ortho.
  by rewrite wu0 expr2 mul0r subr0 //.
 rewrite !normr_norm.
  by move/sqr_inj : Hnorm_sq => ->//; rewrite ?nnegrE ?norm_ge0.
Qed.

Lemma bornage (traj : K -> 'rV_5%R.+1) (z : K) (zp1 := fun r => Lsubmx (traj r)) (z2 := fun r => Rsubmx (traj r)) 
  ( w := (z2 z) *m \S('e_2))
  (u1 : 'rV[K]_2 := \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i)
  (u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2)
  [eta (fun=> 0) with (0,0) |-> 1,
                      (0,1) |-> -2^-1,
                      (1,0) |-> -2^-1,
                      (1,1) |-> 1] (i,j))
   (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) : 
- norm (zp1 z) ^+ 2 +
  (z2 z *m \S('e_2 - z2 z) ^+ 2 *m (z2 z)^T - z2 z *m \S('e_2 - z2 z) ^+ 2 *m (zp1 z)^T) 0 0 <=
  (- u1 *m u2 *m u1^T) 0 0.
Proof.
apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)).
  rewrite mxE.
  have H2 : z2 z *m \S('e_2 - z2 z) = z2 z *m \S('e_2) by rewrite spinD spinN -tr_spin !mulmxDr !tr_spin_mul !addr0.
  rewrite norm_spin mxE addrA expr2 mulmxA H2 -/w -dotmulNv addrC -mulmxN -expr2.
  have cauchy : ((w *m - \S('e_2 - z2 z) *d (zp1 z))%:M : 'rV_1) 0 0 <= 
                norm(w *m - (\S('e_2 - z2 z))) * norm(zp1 z).
    rewrite mxE /= mulr1n (le_trans (ler_norm _)) //.
    rewrite -ler_sqr // ; last first.
    by rewrite nnegrE //  mulr_ge0 ?norm_ge0 //.
  by rewrite exprMn sqr_normr (le_trans (CauchySchwarz_vec _ _)) // !dotmulvv.
  apply: (@le_trans _ _  (norm (w *m - \S('e_2 - z2 z)) * norm (zp1 z)  + (- norm (zp1 z) ^+ 2 - norm w ^+ 2))).
    rewrite lerD2r.
    rewrite (le_trans _ (cauchy)) //.
    by rewrite mxE eqxx mulr1n.
  rewrite neg_spin /u1 /u2 //.
  rewrite ![in leRHS]mxE !sum2E/= ![in leRHS]mxE !sum2E/= ![in leRHS]mxE /=.
  rewrite !mulr1 mulrN mulNr opprK mulrDl mulNr -expr2.
  rewrite [in leLHS] addrCA -!addrA lerD2l mulrDl (mulNr (norm w)).
  rewrite -expr2 !addrA lerD2r !(mulrN , mulNr) opprK -mulrA.
  rewrite [in leRHS](mulrC _ (norm w)) -mulrDr [in leRHS](mulrC (2 ^-1)).
  by rewrite -mulrDr -div1r -splitr mulr1.
by [].
Qed.

Lemma u2neq0 ( u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2)
                           [eta (fun=> 0) with (0,0) |-> 1,
                               (0,1) |-> -2^-1,
                               (1,0) |-> -2^-1,
                               (1,1) |-> 1] (i,j)) : u2 != 0.
Proof.
  apply/matrix0Pn.
  exists 1.
  exists 1.
  by rewrite mxE /= oner_neq0.
Qed.

(* TODO: rework of this proof is needed *) 
Lemma bornage_near (traj : K -> 'rV_5%R.+1)  (zp1 := fun r => Lsubmx (traj r))
 (z2 := fun r => Rsubmx (traj r)) (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) 
  (traj0 : traj 0 = point1 K) :  \forall z \near 0^', (LieDerivative_jacobian1
                          (fun x0 : 'rV_6 => (norm (Lsubmx x0) ^+ 2 / (2 * alpha1))%:M) traj +
                        LieDerivative_jacobian1
                          (fun x0 : 'rV_6 => (norm (Rsubmx x0) ^+ 2 / (2 * gamma))%:M) traj) z <=
                       0.
Proof.
near=> z. 
rewrite !fctE !invfM /=.
set c1 := (2^-1 / alpha1).
set c2 := (2^-1 / gamma).
rewrite (_ : (fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 * c1)%:M) =
(fun zp1_z2 : 'rV_6 => (norm (Lsubmx zp1_z2) ^+ 2 *: c1)%:M)) ; last first. (* TODO: Lemma?*)
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
rewrite func_eq2 !LieDerivative_jacobian1Ml /= !fctE !LieDerivative_jacobian1_norm derive_V1dot //.
set w := (z2 z) *m \S('e_2).
pose u1 : 'rV[K]_2 := \row_(i < 2) [eta (fun=> 0) with 0 |-> norm (zp1 z), 1 |-> norm w] i.
pose u2 : 'M[K]_(2,2) := \matrix_(i < 2, j < 2)
                           [eta (fun=> 0) with (0,0) |-> 1,
                               (0,1) |-> -2^-1,
                               (1,0) |-> -2^-1,
                               (1,1) |-> 1] (i,j).

apply: (@le_trans _ _ ((- u1 *m u2 *m u1^T) ``_ 0)). 
  by rewrite bornage. 
move: defposmxu2 => /= def.
rewrite defposmxP in def.
move : u2neq0 => _.
case H: (u1 == 0).
  move/eqP: H => ->.
  by rewrite mulNmx mul0mx mulNmx mul0mx mxE mxE oppr0.
move: H => /negP H. 
have u1_neq0 : u1 != 0 by apply/negP.
move: (def u1 u1_neq0) => Hpos.
rewrite -oppr_ge0 -oppr_le0 opprK.
apply ltW.
by rewrite -oppr_gt0 mulNmx !mulNmx mxE opprK Hpos.
Unshelve. all: try by end_near. 
Qed.

Lemma V1_point_is_lnsd (traj : K -> 'rV_5%R.+1)  (dtraj : is_solution (fun a : K => (eqn33 alpha1 gamma)^~ a) traj) 
  (traj0 : traj 0 = point1 K) : locnegsemidef (LieDerivative_jacobian1 V1 traj) 0.
Proof.
have Gamma1_traj t : Gamma1 (traj t) by apply/Gamma1_traj.
rewrite /locnegsemidef /V1.
rewrite [x in (LieDerivative_jacobian1 x)] (_ : _ = (fun x0 : 'rV_6 =>
               (norm (Lsubmx x0) ^+ 2 / (2 * alpha1))%:M) \+
               (fun x0 => (norm (Rsubmx x0) ^+ 2 / (2 * gamma))%:M)); last first. by apply/funext => ?/=; rewrite !raddfD.
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
  rewrite !LieDerivative_jacobian1Ml /= !fctE !LieDerivative_jacobian1_eq0_equilibrium; last 3 first.
    by rewrite scaler0 scaler0 add0r.
    rewrite /is_solution /eqn33 in dtraj.
    rewrite -derive1E -derive1mxE'.
    rewrite dtraj/= traj0 /point1.
    by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
    rewrite /is_solution /eqn33 in dtraj.
    rewrite -derive1E -derive1mxE'.
    rewrite dtraj/= traj0 /point1.
    by rewrite rsubmx_const lsubmx_const !subr0 !scaler0 mul0mx row_mx0.
apply/bornage_near.
by rewrite //.
by rewrite //.
Qed.

Lemma V1_is_lyapunov_stable : eq_is_lyapunov_stable (fun a b => @eqn33 K alpha1 gamma b a) V1 (@point1 K).
Proof.
split; first exact: equilibrium_point1.
- apply V1_is_lyapunov_candidate.
- apply/V1_point_is_lnsd.
Qed.

End Lyapunov.
