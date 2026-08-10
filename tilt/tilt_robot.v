From HB Require Import structures.
From mathcomp Require Import boot order algebra ring_tactic.
From mathcomp Require Import interval_inference.
From mathcomp Require Import boolp classical_sets functions reals.
From mathcomp Require Import topology normedtype derive realfun.
Require Import ssr_ext euclidean rigid frame skew derive_matrix tilt_analysis.

(**md**************************************************************************)
(* # Additions to the RobotRocq library                                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.
Local Open Scope ring_scope.

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
rewrite mulmx0 sub0r.
rewrite scaleNr.
rewrite -[in RHS]mul_scalar_mx.
congr (- (_ *m _)).
by rewrite scalemx1.
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

Lemma fact214 (M : 'M[K]_3) (v_ : seq 'rV[K]_3) : M \is 'SO[K]_3 ->
  M^T * (\prod_(i <- v_) \S( i )) * M = (\prod_(i <- v_) \S(i *m M)).
Proof.
move=> MSO.
elim/big_ind2 : _ => //.
  by rewrite -!mulmxE mulmx1 rotation_tr_mul.
- move => a b c d H1 H2.
  rewrite -H1 // -H2 // -!mulmxE -!rotation_inv // !mulmxA -[M^-1 *m b *m M *m M^-1]mulmxA.
  rewrite mulmxV.
    rewrite unitmxE.
    apply: orthogonal_unit.
    exact: rotation_sub.
  by rewrite -[M^-1 *m b *m 1%:M *m d]mulmxA mul1mx.
- move => i true.
  exact: spin_similarity.
Qed.

End basic_facts.

(* spin and matrix/norm properties *)

Lemma tr_sqr_spin {R : realFieldType} (u : 'rV[R]_3) :
  (\S(u) ^+ 2)^T = \S(u) ^+ 2.
Proof. by apply/esym/eqP; rewrite -symE; exact: sqr_spin_is_sym. Qed.

Lemma mul_tr_spin {R : comNzRingType} (u : 'rV[R]_3) : u *m \S(u)^T = 0.
Proof. by apply: trmx_inj; rewrite trmx_mul trmxK spin_mul_tr trmx0. Qed.

Lemma norm_spin {R : rcfType} (u : 'rV[R]_3) (v : 'rV[R]_3) :
  (u *m \S(v - u) ^+ 2 *m (u)^T) 0 0 = - `|u *m \S(v)|_e ^+ 2.
Proof.
rewrite spinD spinN -tr_spin mulmxA !mulmxDr mulmxDl !mul_tr_spin !addr0.
rewrite -dotmulvv /dotmul trmx_mul.
rewrite mxE [X in _ + X = _](_ : _ = 0) ?addr0.
  by rewrite tr_spin -mulmxA mulNmx spin_mul_tr mulmxN mulmx0 oppr0 mxE.
by rewrite tr_spin mulNmx mulmxN [in RHS]mxE opprK mulmxA.
Qed.

Lemma sqr_spin {R : rcfType} (u : 'rV[R]_3) (norm_u1 : `|u|_e = 1) :
  \S(u) *m \S(u) = u^T *m u - 1%:M.
Proof.
have sqrspin : \S(u) ^+ 2 = u^T *m u - (`|u|_e ^+ 2)%:A by rewrite sqr_spin.
rewrite expr2 norm_u1 expr2 mulr1 in sqrspin.
rewrite mulmxE sqrspin.
  apply/matrixP => i j ; rewrite mxE /= [in RHS]mxE /=.
  congr (_+_); rewrite mxE mxE /= mul1r.
  by rewrite [in RHS]mxE [in RHS]mxE /= -mulNrn mxE -mulNrn.
Qed.

Lemma CauchySchwarz_rV {R : rcfType} {n : nat} (a b : 'rV[R]_n) :
  (a *d b) ^+ 2 <= (a *d a) * (b *d b).
Proof.
suffices: 0 <= (b *d b) * (a *d a) - (a *d b) ^+ 2.
  rewrite subr_ge0.
  by rewrite mulrC.
rewrite subr_ge0 expr2 mulrC !dotmulvv /= -expr2.
have [->|hb] := eqVneq b 0.
  rewrite dotmulv0 expr0n.
  rewrite enorm0.
  by rewrite expr0n mul0r.
pose t := (a *d b) / (`|b|_e ^+ 2).
have h : 0 <= `|a - t *: b|_e ^+ 2.
  by rewrite exprn_ge0// enorm_ge0.
rewrite -(dotmulvv (a - t *: b)) in h.
rewrite dotmulBl dotmulBr dotmulvv in h.
rewrite dotmulvZ in h.
rewrite -dotmulvv in h.
rewrite /t in h.
have h1 : 0 <= a *d a - (a *d b) ^+ 2 / `|b|_e ^+ 2.
  move: h.
  rewrite dotmulBr dotmulvZ.
  rewrite (dotmulC ((a *d b / `|b|_e ^+ 2) *: b) a).
  rewrite dotmulvZ dotmulC dotmulvv /t expr2 -!expr2 dotmulZv dotmulvv.
  rewrite divfK /=.
    by rewrite sqrf_eq0 enorm_eq0.
  by rewrite subrr subr0 !expr2 mulrAC.
have h2 : 0 <= `|b|_e ^+ 2 * (a *d a) - (a *d b) ^+ 2.
  have pos: 0 < `|b|_e ^+ 2.
    by rewrite exprn_gt0// enorm_gt0.
  suff: `|b|_e ^+ 2 * (a *d a - (a *d b) ^+ 2 / `|b|_e ^+ 2) =
      `|b|_e ^+ 2 * (a *d a) - (a *d b) ^+ 2.
    move=> eq_step.
    rewrite -eq_step.
    by apply: mulr_ge0; [rewrite ltW | exact h1].
  rewrite mulrBr.
  congr (_ - _)%R.
  by rewrite mulrCA divff ?mulr1// sqrf_eq0 enorm_eq0.
rewrite -subr_ge0 mulrC.
by rewrite dotmulvv mulrC in h2.
Qed.

(* not used *)
Lemma Young_inequality_rV {R : rcfType} {n : nat} (a b : 'rV[R]_n) :
  (a *d b) <= (2^-1 * (`|a|_e) ^+ 2) + (2^-1 * `|b|_e ^+ 2).
Proof.
have normage0 : 0 <= `|a|_e ^+ 2 by rewrite sqr_ge0.
have normbge0 : 0 <= `|b|_e ^+ 2 by rewrite sqr_ge0.
rewrite -!dotmulvv.
have: 0 <= `|a - b|_e ^+ 2 by rewrite sqr_ge0.
rewrite -dotmulvv dotmulD !dotmulvv.
move => h.
rewrite -mulr_natl in h.
have h2 : 2 * (a *d b)  <= `|a|_e ^+ 2 + `|- b|_e ^+ 2.
  rewrite -subr_ge0.
  rewrite dotmulvN mulrN in h.
  by rewrite addrAC.
rewrite -ler_pdivlMl// in h2.
rewrite -mulrDr.
by rewrite enormN in h2.
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

Lemma enorm_squared {R : rcfType} n (u : 'rV[R]_n) :
  (u *m u^T) 0 0 = `|u|_e ^+ 2.
Proof. by rewrite -dotmulvv /dotmul. Qed.

Global Instance is_diff_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f df : V -> 'rV[R]_(n1 + n2)) t :
  is_diff t f df ->
  is_diff t (fun x => rsubmx (f x)) (fun x => rsubmx (df x)).
Proof.
case=> diff_f dfE.
apply: DiffDef.
  by apply: differentiable_comp => //; exact: differentiable_rsubmx.
apply/funext => v.
rewrite -dfE.
rewrite -[LHS]deriveE.
  by apply: differentiable_comp => //; exact: differentiable_rsubmx.
rewrite -[in RHS]deriveE.
  by [].
rewrite derive_rsubmx/=.
  by apply: diff_derivable.
reflexivity.
Qed.

(*Global Instance is_diff_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f df : V -> 'rV[R]_(n1 + n2)) t :
  is_diff t f df ->
  is_diff t (fun x => lsubmx (f x)) (fun x => lsubmx (df x)).
Proof.
case=> diff_f dfE.
apply: DiffDef.
  by apply: differentiable_comp => //; exact: differentiable_lsubmx0.
apply/funext => v.
rewrite -dfE.
rewrite -[LHS]deriveE; last first.
  by apply: differentiable_comp => //; exact: differentiable_lsubmx0.
rewrite -[in RHS]deriveE; last first.
  by [].
rewrite derive_lsubmx//.
Abort.*)

Lemma derivable_row_mx {R : realFieldType} {n1 n2 : nat}
    (f : R -> 'rV[R]_n1) (g : R -> 'rV[R]_n2) t v :
  (forall x, derivable f x v) -> (forall x, derivable g x v) ->
  derivable (fun x : R => row_mx (f x) (g x)) t v.
Proof.
move=> /= fv gv; apply/derivable_mxP => i j.
rewrite (ord1 i)/=.
have /cvg_ex[/= l Hl]:= fv t.
have /cvg_ex[/= k Hk]:= gv t.
apply/cvg_ex => /=; exists (row_mx l k)``_j.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0) Hl.
move/cvgrPdist_le : Hk => /(_ _ e0) Hk.
move: Hl Hk; apply: filterS2 => x Hl Hk.
rewrite !mxE.
case: fintype.splitP => j1 jj1.
  apply: le_trans Hl.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
  apply: le_trans; last first.
    exact: (le_bigmax _ _ (ord0, j1)).
  by rewrite !mxE/=.
apply: le_trans Hk.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, j1)).
by rewrite !mxE/=.
Qed.

Lemma char_poly2 (R : numFieldType) (M : 'M[R]_2) :
  char_poly M = 'X^2 - (\tr M)%:P * 'X + (\det M)%:P.
Proof.
set P := (RHS).
apply/polyP => -[|[|[|i]]]; last first.
- have := (rwP (leq_sizeP (char_poly M) i.+3)).2.
  rewrite size_char_poly => /(_ erefl) /(_ i.+3) => ->//.
  rewrite (rwP (leq_sizeP P i.+3)).2//.
  rewrite /P -addrA size_polyDl ?size_polyXn//.
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

Lemma differentiable_enorm {K : realType} m n (f : 'rV[K]_m -> 'rV_n)
  (g : K -> 'rV[K]_m) t :
  differentiable f (g t) -> f (g t) != 0 ->
  differentiable (fun x => `|f x|_e) (g t) .
Proof.
move=> fgt fgt0; rewrite /enorm -fctE.
apply: differentiable_comp.
  exact: differentiable_dotmul.
apply/derivable1_diffP/derivable_sqrt.
by rewrite dotmulvv expr2 mulr_gt0 //= !enorm_gt0.
Qed.

Lemma mxnorm_enorm_le {K : realType} {n} (x : 'rV[K]_n) : `|x| <= `|x|_e.
Proof.
rewrite /Num.norm/=mx_normrE.
apply/bigmax_leP; split.
  exact: enorm_ge0.
move=> /= [i j] _ /=.
rewrite {i}ord1.
rewrite -sqrtr_sqr.
rewrite /enorm dotmulvv sqr_enorm.
rewrite ler_sqrt; first by apply sumr_ge0 => k _;apply sqr_ge0.
rewrite (bigD1 j) //=.
rewrite lerDl.
by apply sumr_ge0 => k _;apply sqr_ge0.
Qed.

Lemma continuous_enorm {K : realType} {n : nat} :
  continuous (fun u : 'rV[K]_n => `|u|_e).
Proof.
move=> /= x.
rewrite /enorm/=.
apply: (@continuous_comp _ _ _ (fun u : 'rV[K^o]_n => u *d u) sqrtr).
  apply: differentiable_continuous.
  under eq_fun do rewrite dotmulvv sqr_enorm.
  rewrite /=.
  have <- : \sum_(i < n) (fun x0 : 'rV[K]_n => x0``_i ^+ 2) =
            (fun x0 : 'rV[K]_n => \sum_(i < n) x0``_i ^+ 2).
    apply funext => x0 /=.
    exact: (big_morph (fun f : 'rV[K]_n -> K => f x0)).
  apply: differentiable_sum.
  move => i.
  have -> : (fun x0 : 'rV[K]_n => x0``_i ^+ 2) =
            (fun x0 : 'rV_n => x0``_i ) ^+2 by [].
  apply: differentiableX.
  exact: differentiable_coord.
exact: sqrt_continuous.
Qed.

Lemma derivable_enorm_squared {K : realType} n (f : K -> 'rV[K]_n) (x0 : K) :
  derivable f x0 1 ->
  derivable (fun x => `|f x|_e ^+ 2) x0 1.
Proof.
move => dif1.
apply/diff_derivable.
rewrite /=.
under eq_fun do rewrite -dotmulvv dotmulE.
have -> : (fun x : K => \sum_k (f x)``_k * (f x)``_k) =
        \sum_k (fun x => (f x)``_k * (f x)``_k ).
  apply/funext => x => //=.
  by rewrite fct_sumE.
apply/differentiable_sum => k => //=.
apply/differentiableM => //=.
  apply/derivable1_diffP.
  by apply/derivable_coord => //.
apply/derivable1_diffP.
by apply/derivable_coord => //.
Qed.

Lemma derive_enorm_squared {K : realType} n (u : K -> 'rV[K]_n) (t : K) :
  derivable u t 1 ->
  'D_1 (fun x => `|u x|_e ^+ 2) t = 2 * ('D_1 u t *d u t).
Proof.
move=> ut1.
under eq_fun do rewrite -dotmulvv.
rewrite derive_dotmul// dotmulC.
by field.
Qed.

Lemma differentiable_enorm_squared {R : rcfType} m n
    (f : 'rV[R]_m -> 'rV[R]_n) (v : 'rV[R]_m)  :
  differentiable f v ->
  differentiable (fun x => `|f x|_e ^+ 2) v.
Proof.
move=> dif1.
under eq_fun do rewrite -dotmulvv.
exact: differentiable_dotmul.
Qed.

Lemma spin_le_norm {K : rcfType} (x : 'rV[K]_3) : `|\S(x)| <= `|x|.
Proof.
rewrite {1}/Num.norm/= !mx_normrE.
apply: bigmax_le; first exact: normr_ge0.
move=> /= [i j] _/=.
by have [->|->|->] := I3_cases i; have [->|->|->] := I3_cases j;
  rewrite ?(spinij,normr0,normrN)// /Num.norm/= mx_normrE;
  exact: (le_bigmax _ _ (0, _)).
Qed.

Lemma spin_sq_norm_bound {K : rcfType} (x : 'rV[K]_3) : `|\S(x) ^+ 2| <= 3 * `|x|^+2.
Proof.
rewrite (le_trans (mx_norm_sq_le _))// ler_pM//.
suff h : `|\S(x)| <= `|x| by apply: ler_pM.
exact: spin_le_norm.
Qed.

Lemma spin_sq_dist_bound {K : rcfType} (x y: 'rV[K]_3) :
  `|\S(x)^+2 - \S(y)^+2| <= 3 * (`|x| +`|y|) * `|x-y|.
Proof.
have -> : \S(x) ^+ 2 - \S(y) ^+ 2 = \S(x) *m (\S(x) - \S(y)) + (\S(x) - \S(y)) *m \S(y).
  by rewrite mulmxBr mulmxBl addrA subrK.
rewrite mulrDr mulrDl.
apply: (le_trans (ler_normD _ _)).
rewrite -spinN -spinD.
apply: lerD.
  apply: (le_trans (mx_norm_mul _ _)).
  apply : ler_pM => //.
    apply : ler_pM => //.
    exact: spin_le_norm.
  exact: spin_le_norm.
rewrite -mulrA (mulrC `|y|) mulrA.
rewrite (le_trans (mx_norm_mul _ _))//.
rewrite ler_pM//.
  by rewrite ler_pM// spin_le_norm.
exact: spin_le_norm.
Qed.

Lemma enorm_mxnorm {K : rcfType} {n} (x : 'rV[K]_n.+1) :
  `|x|_e ^+ 2 <= n.+1%:R * `|x| ^ 2.
Proof.
rewrite sqr_enorm /=.
apply : (@le_trans _ _ (\sum_(i0 < n.+1) `|x| ^+ 2)).
  apply: ler_sum => k _.
  rewrite -sqr_normr.
  suff h : `|x ord0 k| <= `|x| by exact: ler_pM.
  rewrite {2}/Num.norm/= !mx_normrE /=.
  exact: (le_bigmax _ _ (ord0, k)).
by rewrite big_const_ord mulr_natl iter_addr_0.
Qed.
