From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ring.
From mathcomp Require Import interval_inference.
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

Lemma CauchySchwarz_vec {R : rcfType} {n : nat} (a b : 'rV[R]_n.+1) :
  (a *d b)^+2 <= (a *d a) * (b *d b).
Proof.
suffices: 0 <= (b *d b) * (a *d a) - (a *d b) ^+ 2.
  rewrite subr_ge0.
  by rewrite mulrC.
rewrite subr_ge0 expr2 mulrC !dotmulvv /= -expr2.
have [->|hb] := eqVneq b 0.
  rewrite dotmulv0 expr0n.
  rewrite norm0.
  rewrite expr0n mul0r //=.
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
Lemma young_inequality_vec {R : rcfType} {n : nat} (a b : 'rV[R]_n.+1) :
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


Lemma derivable_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1.+1 + n2.+1)) t v :
  (forall x, derivable f x v) -> derivable (fun x => rsubmx (f x)) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= r Hr]:= df1 t.
apply/cvg_ex => /=; exists (r``_(rshift n1.+1 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hr => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, rshift n1.+1 j)).
by rewrite !mxE.
Qed.

Lemma derive_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1.+1 + n2.+1)) t v :
  (forall x, derivable f x v) ->
  'D_v (fun x => rsubmx (f x)) t = @rsubmx _ _ n1.+1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE//=; last exact: derivable_rsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.

Lemma differentiable_rsubmx0 {R : realFieldType} {V : normedModType R} {n1 n2} t :
  differentiable (@rsubmx R 1 n1.+1 n2.+1) t.
Proof.
have lin_rsubmx : linear (@rsubmx R 1 n1.+1 n2.+1).
  move=> a b c.
  by rewrite linearD//= linearZ.
pose build_lin_rsubmx := GRing.isLinear.Build _ _ _ _ _ lin_rsubmx.
pose Rsubmx : {linear 'rV[R^o]_(n1.+1 + n2.+1) -> 'rV[R^o]_n2.+1} := HB.pack (@rsubmx R _ _ _) build_lin_rsubmx.
apply: (@linear_differentiable _ _ _ Rsubmx).
move=> /= u A /=.
move/nbhs_ballP=> [e /= e0 eA].
apply/nbhs_ballP; exists e => //= v uv.
apply: eA.
(* TODO: lemma *)
move: uv; rewrite /ball/= /mx_ball/ball /= => uv i j.
apply: (le_lt_trans _ (uv i (rshift n1.+1 j))).
by rewrite !mxE.
Qed.

Global Instance is_diff_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f df : V -> 'rV[R]_(n1.+1 + n2.+1)) t :
  is_diff t f df ->
  is_diff t (fun x => rsubmx (f x)) (fun x => rsubmx (df x)).
Proof.
case=> diff_f dfE.
apply: DiffDef.
  by apply: differentiable_comp => //; exact: differentiable_rsubmx0.
apply/funext => v.
rewrite -dfE.
rewrite -[LHS]deriveE; last first.
  by apply: differentiable_comp => //; exact: differentiable_rsubmx0.
rewrite -[in RHS]deriveE; last first.
  by [].
rewrite derive_rsubmx//.
Abort.

Lemma differentiable_rsubmx {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1.+1 + n2.+2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => rsubmx (f x)) t.
Proof.
move=> /= => df1.
apply: differentiable_comp => //.
exact: differentiable_rsubmx0.
Qed.

Lemma derivable_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1.+1 + n2.+1)) t v :
  (forall x, derivable f x v) -> derivable (fun x => lsubmx (f x)) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= l Hl]:= df1 t.
apply/cvg_ex => /=; exists (l``_(lshift n2.+1 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, lshift n2.+1 j)).
by rewrite !mxE.
Qed.

Lemma derive_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1.+1 + n2.+1)) t v :
  (forall x, derivable f x v) ->
  'D_v (fun x => lsubmx (f x)) t = @lsubmx _ _ n1.+1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE//=; last exact: derivable_lsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.

Lemma differentiable_lsubmx0 {R : realFieldType} {V : normedModType R} {n1 n2} t :
  differentiable (@lsubmx R 1 n1.+1 n2.+1) t.
Proof.
have lin_lsubmx : linear (@lsubmx R 1 n1.+1 n2.+1).
  move=> a b c.
  by rewrite linearD//= linearZ.
pose build_lin_lsubmx := GRing.isLinear.Build _ _ _ _ _ lin_lsubmx.
pose Lsubmx : {linear 'rV[R^o]_(n1.+1 + n2.+1) -> 'rV[R^o]_n1.+1} := HB.pack (@lsubmx R _ _ _) build_lin_lsubmx.
apply: (@linear_differentiable _ _ _ Lsubmx).
move=> /= u A /=.
move/nbhs_ballP=> [e /= e0 eA].
apply/nbhs_ballP; exists e => //= v uv.
apply: eA.
(* TODO: lemma *)
move: uv; rewrite /ball/= /mx_ball/ball /= => uv i j.
apply: (le_lt_trans _ (uv i (lshift n2.+1 j))).
by rewrite !mxE.
Qed.

Global Instance is_diff_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f df : V -> 'rV[R]_(n1.+1 + n2.+1)) t :
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
Abort.

Lemma differentiable_lsubmx {R : realFieldType} (V : normedModType R) {n1 n2}
    (f : V -> 'rV[R]_(n1.+1 + n2.+2)) t :
  (forall x, differentiable f x) ->
  differentiable (fun x => lsubmx (f x)) t.
Proof.
move=> /= => df1.
apply: differentiable_comp => //.
exact: differentiable_lsubmx0.
Qed.

Lemma derivable_row_mx {R : realFieldType} {n1 n2 : nat}
    (f : R -> 'rV[R]_n1.+1) (g : R -> 'rV[R]_n2.+1) t v :
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

Lemma derive_row_mx {R : realFieldType} {n1 n2 : nat}
     (f : R -> 'rV[R]_n1.+1) (g : R -> 'rV[R]_n2.+1) t v :
  (forall x : R, derivable f x v) ->
  (forall x : R, derivable g x v) ->
  'D_v (fun x => row_mx (f x) (g x)) t = row_mx ('D_v f t) ('D_v g t).
Proof.
move=> fv gv.
apply/matrixP => i j.
rewrite derive_mx ?mxE//=; last first.
  by apply: derivable_row_mx; [exact: fv|exact: gv].
do 2 rewrite derive_mx ?mxE//=.
case: fintype.split_ordP => /= j1 jj1; rewrite !mxE; congr ('D_v _ t).
  apply/funext => x; rewrite !mxE.
  case: fintype.split_ordP => k jE.
    congr (f x i _).
    move: jE.
    by rewrite jj1 => /(congr1 val) => /= /val_inj.
  move: jE.
  rewrite jj1 => /(congr1 val)/=.
  have /[swap] -> := ltn_ord j1.
  by rewrite ltnNge/= addSn ltnS leq_addr.
apply/funext => x; rewrite !mxE.
case: fintype.split_ordP => k jE.
  move: jE.
  rewrite jj1 => /(congr1 val)/=.
  have /[swap] <- := ltn_ord k.
  by rewrite ltnNge/= addSn ltnS leq_addr.
congr (g x i _).
move: jE.
rewrite jj1 => /(congr1 val) => /= /eqP.
by rewrite eqn_add2l => /eqP /val_inj.
Qed.

Lemma derivable_scalar_mx {R : realFieldType} n (f : 'rV[R]_n.+1 -> R)
    (a : 'rV[R]_n.+1) v :
  derivable f a v ->
  derivable (@scalar_mx _ 1 \o f) a v.
Proof.
move=> /cvg_ex[/= l fav].
apply/cvg_ex => /=.
exists (\col_(i < 1) l).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : fav => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leLHS]/Num.Def.normr/= !mx_normrE/=.
apply: bigmax_le => //= -[i j] _.
rewrite !mxE/=.
by rewrite !ord1 eqxx !mulr1n.
Qed.
