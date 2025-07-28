(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import interval_inference.
From mathcomp Require Import realalg complex fingroup perm.
From mathcomp Require Import sesquilinear.
From mathcomp Require Import boolp reals classical_sets.
From mathcomp Require Import topology normedtype landau derive trigo.
From mathcomp Require Import functions.
Require Import ssr_ext euclidean rigid skew.

(******************************************************************************)
(*                  Derivatives of time-varying matrices                      *)
(*                                                                            *)
(*    derive1mx M(t) == the derivative matrix of M(t)                         *)
(*      ang_vel_mx M == angular velocity matrix of M(t)                       *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Lemma mx_lin1N (R : ringType) n (M : 'M[R]_n) :
  mx_lin1 (- M) = -1 \*: mx_lin1 M :> ( _ -> _).
Proof. by rewrite funeqE => v /=; rewrite scaleN1r mulmxN. Qed.

Lemma mxE_funeqE (R : realFieldType) (V W : normedModType R)
    n m (f : V -> 'I_n -> 'I_m -> W) i j :
  (fun x => (\matrix_(i < n, j < m) (f x i j)) i j) =
  (fun x => f x i j).
Proof. by rewrite funeqE => ?; rewrite mxE. Qed.

Section derive_funmx.
Local Open Scope classical_set_scope.
Variable R : realFieldType.
Context {m n : nat}.

Lemma derive_funmxE (M : R -> 'M[R]_(m.+1, n.+1)) (t : R) v :
  derivable M t v ->
  'D_v M t = \matrix_(i < m.+1, j < n.+1) 'D_v (fun t => M t i j) t.
Proof.
move=> /cvg_ex[/= l Hl]; apply/cvg_lim => //=.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : (Hl) => /(_ (e / 2)).
rewrite divr_gt0// => /(_ isT)[d /= d0 dle].
near=> x.
rewrite [in leLHS]/Num.Def.normr/= mx_normrE.
apply/(bigmax_le _ (ltW e0)) => -[/= i j] _.
rewrite [in leLHS]mxE/= [X in _ + X]mxE -[X in X - _](subrK (l i j)).
rewrite -(addrA (_ - _)) (le_trans (ler_normD _ _))// (splitr e) lerD//.
- rewrite mxE.
  suff : (h^-1 *: (M (h *: v + t) i j - M t i j)) @[h --> 0^'] --> l i j.
    move/cvg_lim => /=; rewrite /derive /= => ->//.
    by rewrite subrr normr0 divr_ge0// ltW.
  apply/cvgrPdist_le => /= r r0.
  move/cvgrPdist_le : Hl => /(_ r r0)[/= s s0] sr.
  near=> y.
  have : `|l - y^-1 *: (M (y *: v + t) - M t)| <= r.
    rewrite sr//=; last by near: y; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: y; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
  by under eq_bigr do rewrite !mxE; exact: (le_bigmax _ _ (i, j)).
- rewrite mxE.
  have : `|l - x^-1 *: (M (x *: v + t) - M t)| <= e / 2.
    apply: dle => //=; last by near: x; exact: nbhs_dnbhs_neq.
    by rewrite sub0r normrN; near: x; exact: dnbhs0_lt.
  apply: le_trans.
  rewrite [in leRHS]/Num.Def.normr/= mx_normrE/=.
  under eq_bigr do rewrite !mxE.
  apply: le_trans; last exact: le_bigmax.
  by rewrite !mxE.
Unshelve. all: by end_near. Qed.

End derive_funmx.

Lemma norm_trmx (R : realFieldType) m n
  (M : 'M[R]_(m.+1, n.+1)) : `|M^T| = `|M|.
Proof.
rewrite /Num.Def.normr/= !mx_normrE.
under eq_bigr do rewrite mxE.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: bigmax_le => //=.
    apply: le_trans; last first.
      apply: le_bigmax => /=.
      exact: (ord0, ord0).
    by [].
  move=> i _.
  apply/bigmax_geP; right => /=.
  by exists (i.2, i.1).
-  apply: bigmax_le => //=.
    apply: le_trans; last first.
      apply: le_bigmax => /=.
      exact: (ord0, ord0).
    by [].
  move=> i _.
  apply/bigmax_geP; right => /=.
  by exists (i.2, i.1).
Qed.

Section derive_mx.

Variable (R : realFieldType) (V W : normedModType R).

Definition derivable_mx m n (M : R -> 'M[R]_(m.+1, n.+1)) t v :=
  forall i j, derivable (fun x : R^o => (M x) i j) t v.

Lemma derivable_mxP m n (M : R -> 'M[R]_(m.+1, n.+1)) t v :
  derivable_mx M t v <-> derivable M t v.
Proof.
split; rewrite /derivable_mx /derivable.
  move=> H.
  apply/cvg_ex => /=.
  pose l := \matrix_(i < m.+1, j < n.+1) sval (cid ((cvg_ex _).1 (H i j))).
  exists l.
  apply/cvgrPdist_le => /= e e0.
  near=> x.
  rewrite /Num.Def.normr/= mx_normrE.
    apply: (bigmax_le _ (ltW e0)) => /= i _.
  rewrite !mxE/=.
  move: i.
  near: x.
  apply: filter_forall => /= i.
  pose r_of_i := fun i => (@cvgrPdist_le _ _ _ _ (dnbhs_filter 0) _ _).1
    (svalP (cid ((cvg_ex _).1 (H i.1 i.2)))) _ e0.
  have := r_of_i i.
  done.
move=> /cvg_ex[/= l Hl] i j.
apply/cvg_ex; exists (l i j).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0] H.
near=> x.
apply: le_trans; last first.
  apply: (H x).
  rewrite /ball_/=.
  rewrite sub0r normrN.
  near: x.
  exact: dnbhs0_lt.
  near: x.
  exact: nbhs_dnbhs_neq.
rewrite [leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last exact: le_bigmax.
by rewrite /= !mxE.
Unshelve. all: by end_near. Qed.

Variables m n : nat.
Implicit Types M N : R -> 'M[R]_(m.+1, n.+1).

Lemma derivable_mxD M N t : derivable M t 1 -> derivable N t 1 ->
  derivable (fun x => M x + N x) t 1.
Proof.
move=> Hf Hg.
by apply: derivableD.
Qed.

Lemma derivable_mxN M t : derivable M t 1 ->
  derivable (fun x => - M x) t 1.
Proof.
move=> HM.
exact: derivableN.
Qed.

Lemma derivable_mxB M N t : derivable M t 1 -> derivable N t 1 ->
  derivable (fun x => M x - N x) t 1.
Proof.
move=> Hf Hg.
by apply: derivableB.
Qed.

Lemma trmx_derivable M t v :
  derivable M t v = derivable (fun x => (M x)^T) t v.
Proof.
rewrite propeqE; split; rewrite /derivable/=.
- move=> /cvg_ex[/= l Hl].
  apply/cvg_ex => /=; exists l^T.
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0 re].
  near=> x.
  rewrite [leLHS](_ : _ = `|l - x^-1 *: ((M (x *: v + t)) - (M t))|); last first.
    rewrite -[RHS]norm_trmx.
    rewrite [in RHS]linearD/=.
    rewrite [in RHS]linearN/=.
    congr (`| _ - _ |).
    rewrite [RHS]linearZ/=.
    by rewrite [in RHS]linearB.
  apply: re => /=.
  rewrite sub0r normrN.
  near: x.
  by apply: dnbhs0_lt.
  near: x.
  by apply: nbhs_dnbhs_neq.
- move=> /cvg_ex[/= l Hl].
  apply/cvg_ex => /=; exists l^T.
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0 re].
  near=> x.
  rewrite [leLHS](_ : _ = `|l - x^-1 *: ((M (x *: v + t))^T - (M t)^T)|); last first.
    rewrite -[RHS]norm_trmx.
    rewrite [in RHS]linearD/=.
    rewrite [in RHS]linearN/=.
    congr (`| _ - _ |).
    rewrite [RHS]linearZ/=.
    rewrite [in RHS]linearB.
    by rewrite /= !trmxK.
  apply: re => /=.
  rewrite sub0r normrN.
  near: x.
  by apply: dnbhs0_lt.
  near: x.
  by apply: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

Lemma derivable_mx_row M t i :
  derivable M t 1 -> derivable (row i \o M) t 1.
Proof.
rewrite /derivable => /cvg_ex[/= l Hl].
apply/cvg_ex => /=.
exists (row i l).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0)[r /= r0 re].
near=> x.
apply: le_trans; last first.
  apply: (re x).
  rewrite /ball_ /= sub0r normrN.
  near: x.
  by apply: dnbhs0_lt.
  near: x.
  by apply: nbhs_dnbhs_neq.
rewrite /Num.Def.normr/= !mx_normrE.
apply/bigmax_leP => /=.
split.
    apply: le_trans; last first.
      apply: le_bigmax => /=.
      exact: (ord0, ord0).
    by [].
move=> j _.
rewrite !mxE.
under eq_bigr do rewrite !mxE.
apply: le_trans; last first.
  apply: le_bigmax.
  exact: (i, j.2).
by rewrite /=.
Unshelve. all: by end_near. Qed.

Lemma derivable_mx_col M t i :
  derivable M t 1 -> derivable (col i \o M) t 1.
Proof.
rewrite /derivable => /cvg_ex[/= l Hl].
apply/cvg_ex => /=.
exists (col i l).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0)[r /= r0 re].
near=> x.
apply: le_trans; last first.
  apply: (re x).
  rewrite /ball_ /= sub0r normrN.
  near: x.
  by apply: dnbhs0_lt.
  near: x.
  by apply: nbhs_dnbhs_neq.
rewrite /Num.Def.normr/= !mx_normrE.
apply/bigmax_leP => /=.
split.
    apply: le_trans; last first.
      apply: le_bigmax => /=.
      exact: (ord0, ord0).
    by [].
move=> j _.
rewrite !mxE.
under eq_bigr do rewrite !mxE.
apply: le_trans; last first.
  apply: le_bigmax.
  exact: (j.1, i).
by rewrite /=.
Unshelve. all: by end_near. Qed.

Lemma derive1mx_cst (P : 'M[R]_(m.+1, n.+1)) : (cst P)^`()%classic = cst 0.
Proof.
apply/funext => ?.
by rewrite derive1_cst.
Qed.

Lemma derive1mx_tr M t : derivable M t 1 -> 'D_1 (trmx \o M) t = ('D_1 M t)^T.
Proof.
move=> Mt1.
rewrite !derive_funmxE//=.
  apply/matrixP => i j; rewrite !mxE.
  by rewrite (_ : (fun _ => _) = (fun t => M t j i)) // funeqE => ?; rewrite mxE.
by rewrite -trmx_derivable.
Qed.

Lemma derive1mxD M N t : derivable M t 1 -> derivable N t 1 ->
  'D_1 (M + N) t = 'D_1 M t + 'D_1 N t.
Proof.
move=> Hf Hg.
by rewrite deriveD//.
Qed.

Lemma derive1mxN M t : derivable M t 1 -> 'D_1 (- M) t = - 'D_1 M t.
Proof.
move=> Mt1.
by rewrite deriveN.
Qed.

Lemma derive1mxB M N t : derivable M t 1 -> derivable N t 1 ->
  'D_1 (M - N) t = 'D_1 M t - 'D_1 N t.
Proof.
move=> Mt1 Nt1.
by rewrite deriveB.
Qed.

End derive_mx.

Section derive_mx_R.

Variables (R : realFieldType) (m n k : nat).

Lemma derivable_mxM (f : R -> 'M[R^o]_(m.+1, k.+1)) (g : R -> 'M[R^o]_(k.+1, n.+1)) t :
  derivable f t 1 -> derivable g t 1 -> derivable (fun x => f x *m g x) t 1.
Proof.
move=> /derivable_mxP Hf /derivable_mxP Hg.
apply/derivable_mxP => a b. evar (f1 : 'I_k.+1 -> R^o -> R^o).
rewrite (_ : (fun x => _) = (\sum_i f1 i)); last first.
  rewrite funeqE => t'; rewrite mxE fct_sumE; apply: eq_bigr => k0 _.
  rewrite /f1; reflexivity.
rewrite {}/f1; apply: derivable_sum => k0.
evar (f1 : R^o -> R). evar (f2 : R -> R).
rewrite (_ : (fun t' => _) = f1 * f2); last first.
  rewrite funeqE => t'; rewrite -[RHS]/(f1 t' * f2 t') /f1 /f2; reflexivity.
rewrite {}/f1 {}/f2; exact: derivableM.
Qed.

End derive_mx_R.

Section derive_mx_SE.

Variables (R : rcfType) (M : R -> 'M[R^o]_4).


Lemma SE_derivable : (forall t, M t \is 'SE3[R]) ->
  forall t, derivable M t 1.
Proof.
move=> ME/= t.
apply/derivable_mxP.
move=> [[|[|[|[|//]]]]] Hi [[|[|[|[|//]]]]] Hj.
- have : (fun t => M t (Ordinal Hi) (Ordinal Hj)) = 0.
    apply/funext => x.
    have := ME x.
Admitted.

Lemma derivable_rot_of_hom : (forall t, derivable M t 1) ->
  forall x, derivable (@rot_of_hom _ \o M) x 1.
Proof.
move=> H x.
apply/derivable_mxP => i j.
rewrite /rot_of_hom.
rewrite (_ : (fun _ => _) = (fun y => (M y) (lshift 1 i) (lshift 1 j))); last first.
  by rewrite funeqE => y; rewrite !mxE.
rewrite /= in H.
have /derivable_mxP := H x.
exact.
Qed.

Local Open Scope classical_set_scope.

Lemma derive1mx_SE : (forall t, M t \in 'SE3[R]) ->
  forall t, 'D_1 M t = block_mx
    ('D_1 (@rot_of_hom R^o \o M) t) 0
    ('D_1 (@trans_of_hom R^o \o M) t) 0.
Proof.
move=> MSE t.
rewrite !derive_funmxE//; last 3 first.
  admit.
  apply: derivable_rot_of_hom => /= x.
  exact: SE_derivable.
  exact: SE_derivable.
rewrite block_mxEh.
rewrite {1}(_ : M = (fun x => hom (rot_of_hom (M x)) (trans_of_hom (M x)))); last first.
  rewrite funeqE => x; by rewrite -(SE3E (MSE x)).
apply/matrixP => i j.
rewrite 2!mxE; case: splitP => [j0 jj0|j0 jj0].
  rewrite (_ : j = lshift 1 j0); last exact/val_inj.
  rewrite mxE; case: splitP => [i1 ii1|i1 ii1].
    rewrite (_ : i = lshift 1 i1); last exact/val_inj.
    rewrite mxE; congr ('D_1 _ t); rewrite funeqE => x.
    by rewrite /hom (block_mxEul _ _ _ _ i1 j0).
  rewrite (_ : i = rshift 3 i1); last exact/val_inj.
  rewrite mxE; congr ('D_1 _ t); rewrite funeqE => x.
  by rewrite /hom (block_mxEdl (rot_of_hom (M x))).
rewrite (_ : j = rshift 3 j0) ?mxE; last exact/val_inj.
rewrite (ord1 j0).
case: (@splitP 3 1 i) => [i0 ii0|i0 ii0].
  rewrite (_ : i = lshift 1 i0); last exact/val_inj.
  rewrite (_ : (fun _ => _) = (fun=> 0)).
    by rewrite derive_cst mxE.
  by rewrite funeqE => x;  rewrite /hom (block_mxEur (rot_of_hom (M x))) mxE.
rewrite (_ : i = rshift 3 i0); last exact/val_inj.
rewrite (_ : (fun _ => _) = (fun=> 1)) ?derive_cst // (ord1 i0) ?mxE //.
by rewrite funeqE => x; rewrite /hom (block_mxEdr (rot_of_hom (M x))) mxE.
Admitted.

End derive_mx_SE.

Section row_belast.

(* TODO: move? *)
Definition row_belast {R : ringType} n (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \row_(i < n) (v ``_ (widen_ord (leqnSn n) i)).

(* TODO: move? *)
Lemma row_belast_last (R : ringType) n (r : 'rV[R]_n.+1) H :
  r = castmx (erefl, H) (row_mx (row_belast r) (r ``_ ord_max)%:M).
Proof.
apply/rowP => i; rewrite castmxE mxE.
case: fintype.splitP => /= [j Hj|[] [] //= ? ni]; rewrite mxE /=.
  congr (_ ``_ _); exact: val_inj.
rewrite mulr1n; congr (_ ``_ _); apply val_inj; by rewrite /= ni addn0.
Qed.

Lemma derivable_row_belast (R : realFieldType) n (u : R -> 'rV[R^o]_n.+2) (t : R) (v : R):
  derivable_mx u t v -> derivable_mx (fun x => row_belast (u x)) t v.
Proof.
move=> H i j; move: (H ord0 (widen_ord (leqnSn n.+1) j)) => {H}.
set f := fun _ => _. set g := fun _ => _.
by rewrite (_ : f = g) // funeqE => x; rewrite /f /g mxE.
Qed.

Lemma dotmul_belast {R : realFieldType} n (u : 'rV[R]_n.+2) (v1 : 'rV[R]_n.+1) v2 H :
  u *d castmx (erefl 1%nat, H) (row_mx v1 v2) =
    u *d castmx (erefl 1%nat, H) (row_mx v1 0%:M) +
    u *d castmx (erefl 1%nat, H) (row_mx 0 v2).
Proof.
rewrite -dotmulDr; congr dotmul; apply/matrixP => i j; rewrite !(castmxE,mxE) /=.
case: fintype.splitP => [k /= jk|[] [] // ? /= jn]; by rewrite !(mxE,addr0,add0r,mul0rn).
Qed.

Lemma derive1mx_dotmul_belast (R : realFieldType) n (u v : R^o -> 'rV[R^o]_n.+2) t :
  let u' x := row_belast (u x) in let v' x := row_belast (v x) in
  u' t *d 'D_1 v' t + (u t)``_ord_max *: derive (fun x => (v x)``_ord_max) t 1 =
  u t *d 'D_1 v t.
Proof.
move=> u' v'.
rewrite (row_belast_last ('D_1 v t)) ?addn1 // => /= ?.
rewrite dotmul_belast; congr (_ + _).
  rewrite 2!dotmulE [in RHS]big_ord_recr /=.
  rewrite castmxE mxE /=; case: fintype.splitP => [j /= /eqP/negPn|j _].
    by rewrite (gtn_eqF (ltn_ord j)).
  rewrite !mxE (_ : _ == _); last by apply/eqP/val_inj => /=; move: j => [[] ?].
  rewrite mulr0 addr0; apply/eq_bigr => i _; rewrite castmxE !mxE; congr (_ * _).
  case: fintype.splitP => [k /= ik|[] [] //= ?]; rewrite !mxE.
    rewrite derive_funmxE//; last first.
      admit.
    rewrite /= !mxE/=.
    rewrite derive_funmxE//; last first.
      admit.
    rewrite /= !mxE/=.
    f_equal.
    by rewrite funeqE => x; rewrite /v' !mxE; congr ((v _) _ _); by apply/val_inj.
  by rewrite addn0 => /eqP/negPn; rewrite (ltn_eqF (ltn_ord i)).
apply/esym.
rewrite dotmulE big_ord_recr /= (eq_bigr (fun=> 0)); last first.
  move=> i _.
  rewrite !castmxE !mxE; case: fintype.splitP => [j /= ij| [] [] //= ?].
    by rewrite mxE mulr0.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
rewrite sumr_const mul0rn add0r castmxE /=; congr (_ * _); rewrite !mxE.
case: fintype.splitP => [j /= /eqP/negPn | [] [] //= ? Hn].
  by rewrite (gtn_eqF (ltn_ord j)).
rewrite mxE/= mulr1n.
rewrite derive_funmxE//; last first.
  admit.
by rewrite mxE//.
Admitted.

End row_belast.

(* TODO: could be derived from more generic lemmas about bilinearity in derive.v? *)
Section product_rules.

Lemma derive1mx_dotmul (R : realFieldType) n (u v : R^o -> 'rV[R^o]_n.+1) (t : R^o) :
  derivable u t 1 -> derivable v t 1 ->
  'D_1 (fun x => u x *d v x : R^o) t =
  'D_1 u t *d v t + u t *d 'D_1 v t.
Proof.
move=> /derivable_mxP U /derivable_mxP V.
evar (f : R -> R); rewrite (_ : (fun x : R => u x *d v x : R^o) = f); last first.
  rewrite funeqE => x /=; exact: dotmulE.
rewrite {}/f.
set f := fun i : 'I__ => fun x => ((u x) ``_ i * (v x) ``_ i).
rewrite (_ : (fun _ : R => _) = \sum_(k < _) f k); last first.
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite derive_sum; last by move=> ?; exact: derivableM (U _ _) (V _ _).
rewrite {}/f.
elim: n u v => [|n IH] u v in U V *.
  rewrite big_ord_recl/= big_ord0 addr0.
  rewrite /dotmul !mxE !sum1E !mxE.
  rewrite deriveM//=.
  rewrite addrC.
  rewrite mulrC//.
  rewrite derive_funmxE//; last first.
    exact/derivable_mxP.
  rewrite !mxE.
  rewrite derive_funmxE//; last first.
    exact/derivable_mxP.
  rewrite !mxE.
  done.
rewrite [LHS]big_ord_recr /=.
set u' := fun x => row_belast (u x). set v' := fun x => row_belast (v x).
transitivity ('D_1 u' t *d v' t + u' t *d 'D_1 v' t +
    derive (fun x => (u x)``_ord_max * (v x)``_ord_max) t 1).
  rewrite -(IH _ _ (derivable_row_belast U) (derivable_row_belast V)).
  apply: f_equal2; last by [].
  apply eq_bigr => i _; congr (derive _ t 1).
  by rewrite funeqE => x; rewrite !mxE.
rewrite (deriveM (U _ _) (V _ _)) /= -!addrA addrC addrA.
rewrite -(addrA (_ + _)) [in RHS]addrC derive1mx_dotmul_belast; congr (_ + _).
by rewrite [in RHS]dotmulC -derive1mx_dotmul_belast addrC dotmulC.
Qed.

Lemma derive1mxM (R : realFieldType) n m p (M : R -> 'M[R^o]_(n.+1, m.+1))
  (N : R^o -> 'M[R^o]_(m.+1, p.+1)) (t : R^o) :
  derivable M t 1 -> derivable N t 1 ->
  'D_1 (fun t => M t *m N t) t =
    'D_1 M t *m N t + M t *m ('D_1 N t).
Proof.
move=> HM HN; apply/matrixP => i j.
rewrite derive_funmxE; last admit.
rewrite ![in LHS]mxE.
rewrite (_ : (fun x => _) = fun x => \sum_k (M x) i k * (N x) k j); last first.
  by rewrite funeqE => x; rewrite !mxE.
rewrite (_ : (fun x => _) =
    fun x => (row i (M x)) *d (col j (N x))^T); last first.
  rewrite funeqE => z; rewrite dotmulE; apply eq_bigr => k _.
  by rewrite 3!mxE.
rewrite (derive1mx_dotmul (derivable_mx_row HM)); last first.
  rewrite /=.
  (* derivable_mx_col HN*) admit.
(*by rewrite [in RHS]mxE; congr (_  + _); rewrite [in RHS]mxE dotmulE;
   apply/eq_bigr => /= k _; rewrite !mxE; apply: f_equal2;
   try by congr (@derive1 _ R^o _ t);
          rewrite funeqE => z; rewrite !mxE.
Qed.*) Admitted.

Lemma derive1mx_crossmul (R : realFieldType) (u v : R -> 'rV[R^o]_3) t :
  derivable u t 1 -> derivable v t 1 ->
  'D_1 (fun x => (u x *v v x) : 'rV[R^o]_3) t =
  'D_1 u t *v v t + u t *v 'D_1 v t.
Proof.
move=> U V.
evar (f : R -> 'rV[R]_3); rewrite (_ : (fun x : R => _) = f); last first.
  rewrite funeqE => x; exact: crossmulE.
rewrite {}/f; apply/rowP => i; rewrite mxE.
(*rewrite (mxE_funeqE (fun x : R^o => _)) /= mxE 2!crossmulE !{1}[in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=];
  rewrite ?derive1E (deriveD (derivableM (U _ _) (V _ _))
    (derivableN (derivableM (U _ _) (V _ _))));
  rewrite (deriveN (derivableM (U _ _) (V _ _))) 2!(deriveM (U _ _) (V _ _));
  rewrite addrCA -!addrA; congr (_ + (_ + _)); by [ rewrite mulrC |
  rewrite opprD addrC; congr (_ + _); rewrite mulrC ].
Qed.*) Admitted.

End product_rules.

Section cross_product_matrix.

Lemma differential_cross_product (R : realFieldType) (v : 'rV[R^o]_3) y :
  'd (crossmul v) y = mx_lin1 \S( v ) :> (_ -> _).
Proof.
rewrite (_ : crossmul v = (fun x => x *m \S( v ))); last first.
  by rewrite funeqE => ?; rewrite -spinE.
rewrite (_ : mulmx^~ \S(v) = @mulmxr _ 1 _ _ \S(v)); last by rewrite funeqE.
rewrite diff_lin //= => x.
suff : differentiable (mulmxr \S(v)) (x : 'rV[R^o]_3).
  by move/differentiable_continuous.
rewrite (_ : mulmxr \S(v) = (fun z => \sum_i z``_i *: row i \S(v))); last first.
  rewrite funeqE => z; by rewrite -mulmx_sum_row.
set f := fun (i : 'I_3) (z : 'rV_3) => z``_i *: row i \S(v) : 'rV_3.
rewrite (_ : (fun _ => _) = \sum_i f i); last by rewrite funeqE => ?; by rewrite fct_sumE.
apply: differentiable_sum => i.
exact/differentiableZl/differentiable_coord.
Qed.

Lemma differential_cross_product2 (R : realFieldType) (v y : 'rV[R^o]_3) :
  'd (fun x : 'rV[R^o]_3 => x *v v) y = -1 \*: mx_lin1 \S( v ) :> (_ -> _).
Proof.
transitivity ('d (crossmul (- v)) y); last first.
  by rewrite differential_cross_product spinN mx_lin1N.
congr diff.
by rewrite funeqE => /= u; rewrite (@lieC _ (vec3 R)) linearNl.
Qed.

End cross_product_matrix.

(* [sciavicco] p.80-81 *)
Section derivative_of_a_rotation_matrix.

Variables (R : realFieldType) (M : R -> 'M[R^o]_3).

Definition ang_vel_mx t : 'M_3 := (M t)^T * 'D_1 M t.

Definition body_ang_vel_mx t : 'M_3 := 'D_1 M t *m (M t)^T.

(* angular velocity (a free vector) *)
Definition ang_vel t := unspin (ang_vel_mx t).

Hypothesis MO : forall t, M t \is 'O[ R ]_3.
Hypothesis derivable_M : forall t, derivable M t 1.

Lemma ang_vel_mx_is_so t : ang_vel_mx t \is 'so[ R ]_3.
Proof.
have : (fun t => (M t)^T * M t) = cst 1.
  rewrite funeqE => x; by rewrite -orthogonal_inv // mulVr // orthogonal_unit.
move/(congr1 (fun f => 'D_1 f t)).
rewrite derive_cst.
rewrite derive1mxM // -?trmx_derivable // derive1mx_tr//.
move=> /eqP; rewrite addr_eq0 => /eqP H.
by rewrite antiE /ang_vel_mx trmx_mul trmxK H opprK.
Qed.

Lemma ang_vel_mxE t : ang_vel_mx t = \S( ang_vel t).
Proof. by rewrite /ang_vel unspinK // ang_vel_mx_is_so. Qed.

(* [sciavicco] eqn 3.7 *)
Lemma derive1mx_ang_vel t : 'D_1 M t = M t * ang_vel_mx t.
Proof.
move: (ang_vel_mx_is_so t); rewrite antiE -subr_eq0 opprK => /eqP.
rewrite {1 2}/ang_vel_mx trmx_mul trmxK => /(congr1 (fun x => (M t) * x)).
rewrite mulr0 mulrDr !mulrA -{1}(orthogonal_inv (MO t)).
rewrite divrr ?orthogonal_unit // mul1r.
move=> /eqP; rewrite addr_eq0 => /eqP {1}->.
rewrite -mulrA -mulrN -mulrA; congr (_ * _).
move: (ang_vel_mx_is_so t); rewrite antiE -/(ang_vel_mx t) => /eqP ->.
by rewrite /ang_vel_mx trmx_mul trmxK mulmxE.
Qed.

Lemma derive1mx_rot (p' : 'rV[R^o]_3 (* constant vector *)) :
  let p := fun t => p' *m M t in
  forall t, 'D_1 p t = ang_vel t *v p t.
Proof.
move=> p t; rewrite /p derive1mxM; last first.
  exact: derivable_M.
  rewrite /derivable_mx => i j; exact: ex_derive.
rewrite derive_cst mul0mx add0r derive1mx_ang_vel mulmxA.
by rewrite -{1}(unspinK (ang_vel_mx_is_so t)) spinE.
Qed.

End derivative_of_a_rotation_matrix.
