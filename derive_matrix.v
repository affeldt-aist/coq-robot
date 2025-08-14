(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum rat.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import interval_inference.
From mathcomp Require Import realalg complex fingroup perm.
From mathcomp Require Import sesquilinear ring.
From mathcomp Require Import boolp reals classical_sets.
From mathcomp Require Import topology normedtype landau derive trigo.
From mathcomp Require Import functions.
Require Import ssr_ext euclidean rigid skew.

(******************************************************************************)
(*                  Derivatives of time-varying matrices                      *)
(*                                                                            *)
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

Lemma norm_trmx (R : realFieldType) m n
  (M : 'M[R]_(m.+1, n.+1)) : `|M^T| = `|M|.
Proof.
rewrite /Num.Def.normr/= !mx_normrE.
under eq_bigr do rewrite mxE.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: bigmax_le => //=.
    exact: le_trans (le_bigmax _ _ (ord0, ord0)).
  by move=> i _; apply/bigmax_geP; right => /=; exists (i.2, i.1).
- apply: bigmax_le => //=.
    exact: le_trans (le_bigmax _ _ (ord0, ord0)).
  by move=> i _; apply/bigmax_geP; right => /=; exists (i.2, i.1).
Qed.

Section pointwise_derivable.
Context {R : realFieldType} {V W : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m.+1, n.+1).

Definition derivable_mx M t v :=
  forall i j, derivable (fun x => M x i j) t v.

Lemma derivable_mxP M t v : derivable_mx M t v <-> derivable M t v.
Proof.
split; rewrite /derivable_mx /derivable.
- move=> H.
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
  exact: ((@cvgrPdist_le _ _ _ _ (dnbhs_filter 0) _ _).1
    (svalP (cid ((cvg_ex _).1 (H i.1 i.2)))) _ e0).
- move=> /cvg_ex[/= l Hl] i j.
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

Lemma derivable_trmx M t v :
  derivable (fun x => (M x)^T) t v = derivable M t v.
Proof.
rewrite propeqE; split; rewrite /derivable/=.
- move=> /cvg_ex[/= l Hl].
  apply/cvg_ex => /=; exists l^T.
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : Hl => /(_ _ e0)[/= r r0 re].
  near=> x.
  rewrite [leLHS](_ : _ =
      `|l - x^-1 *: ((M (x *: v + t))^T - (M t)^T)|); last first.
    rewrite -[RHS]norm_trmx.
    rewrite [in RHS]linearD/=.
    rewrite [in RHS]linearN/=.
    congr (`| _ - _ |).
    rewrite [RHS]linearZ/=.
    rewrite [in RHS]linearB.
    by rewrite /= !trmxK.
  apply: re => /=.
    rewrite sub0r normrN.
    by near: x; exact: dnbhs0_lt.
  by near: x; exact: nbhs_dnbhs_neq.
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
    by near: x; exact: dnbhs0_lt.
  by near: x; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

Lemma derivable_row M t v i : derivable M t v -> derivable (row i \o M) t v.
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
    by near: x; exact: dnbhs0_lt.
  by near: x; exact: nbhs_dnbhs_neq.
rewrite /Num.Def.normr/= !mx_normrE.
apply/bigmax_leP => /=.
split.
    exact: le_trans (le_bigmax _ _ (ord0, ord0)).
move=> j _.
rewrite !mxE.
under eq_bigr do rewrite !mxE.
exact: le_trans (le_bigmax _ _ (i, j.2)).
Unshelve. all: by end_near. Qed.

Lemma derivable_col M t v i : derivable M t v -> derivable (col i \o M) t v.
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
    by near: x; exact: dnbhs0_lt.
  by near: x; exact: nbhs_dnbhs_neq.
rewrite /Num.Def.normr/= !mx_normrE.
apply/bigmax_leP => /=.
split.
  exact: le_trans (le_bigmax _ _ (ord0, ord0)).
move=> j _.
rewrite !mxE.
under eq_bigr do rewrite !mxE.
exact: le_trans (le_bigmax _ _ (j.1, i)).
Unshelve. all: by end_near. Qed.

Lemma derivable_row3 (a b c : V -> R) t v :
  derivable a t v -> derivable b t v -> derivable c t v ->
  derivable (fun x => row3 (a x) (b x) (c x)) t v.
Proof.
move=> /cvg_ex[/= l Hl] /cvg_ex[/= o Ho] /cvg_ex[/= p Hp].
apply/cvg_ex; exists (row3 l o p) => /=.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0)[r/= r0 re].
move/cvgrPdist_le : Ho => /(_ _ e0)[s/= s0 se].
move/cvgrPdist_le : Hp => /(_ _ e0)[u/= u0 ue].
near=> x.
rewrite /Num.Def.normr/= mx_normrE.
apply: bigmax_le.
  exact: ltW.
move=> /= [i j] _.
rewrite (ord1 i){i}/=.
rewrite row3N.
rewrite row3D.
rewrite row3Z.
rewrite row3N.
rewrite row3D.
rewrite row3E.
rewrite ![in leLHS]mxE/=.
case: fintype.splitP => [j0|].
  rewrite (ord1 j0) => _.
  rewrite !mxE eqxx/= mulr1n.
  apply: re.
    rewrite /= sub0r normrN.
    by near: x; exact: dnbhs0_lt.
  by near: x; exact: nbhs_dnbhs_neq.
move=> k j1k.
rewrite !mxE.
case: fintype.splitP => [k0|k0].
  rewrite (ord1 k0) => _.
  rewrite !mxE eqxx/= mulr1n.
  apply: se.
    rewrite /= sub0r normrN.
    by near: x; exact: dnbhs0_lt.
  by near: x; exact: nbhs_dnbhs_neq.
rewrite (ord1 k0) => _.
rewrite !mxE eqxx/= mulr1n.
apply: ue.
  rewrite /= sub0r normrN.
  by near: x; exact: dnbhs0_lt.
by near: x; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

Lemma derivable_coord (a : V -> 'rV[R]_n.+1) t v (i : 'I_n.+1) :
  derivable a t v ->
  derivable (fun x : V => (a x)``_i) t v.
Proof.
move=> /cvg_ex[/= l Hl].
apply/cvg_ex; exists (l``_i) => /=.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0) Hl.
apply: filterS Hl => x.
rewrite {1}/Num.Def.normr/= mx_normrE.
move/bigmax_leP => -[_/=] /(_ (ord0, i)).
by rewrite !mxE/=; exact.
Qed.

End pointwise_derivable.

Section pointwise_derive.
Local Open Scope classical_set_scope.
Context {R : realFieldType} {V W : normedModType R} .

Lemma derive_mx {m n : nat} (M : V -> 'M[R]_(m.+1, n.+1)) t v :
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

Lemma derive_trmx {m n : nat} (M : V -> 'M[R]_(m.+1, n.+1)) t v :
  derivable M t v -> 'D_v (trmx \o M) t = ('D_v M t)^T.
Proof.
move=> Mt1.
rewrite !derive_mx//=; last by rewrite derivable_trmx.
apply/matrixP => i j; rewrite !mxE.
by under eq_fun do rewrite mxE.
Qed.

End pointwise_derive.

Section derivable_mulmx.
Context {R : realFieldType} {V : normedModType R} {m n k : nat}.

Lemma derivable_mulmx
    (f : V -> 'M[R]_(m.+1, k.+1)) (g : V -> 'M[R]_(k.+1, n.+1)) t v :
  derivable f t v -> derivable g t v -> derivable (fun x => f x *m g x) t v.
Proof.
move=> /derivable_mxP Hf /derivable_mxP Hg; apply/derivable_mxP => a b.
evar (f1 : 'I_k.+1 -> V -> R).
rewrite (_ : (fun x => _) = \sum_i f1 i); last first.
  rewrite funeqE => t'; rewrite mxE fct_sumE; apply: eq_bigr => k0 _.
  by rewrite /f1; reflexivity.
rewrite {}/f1; apply: derivable_sum => k0.
evar (f1 : V -> R). evar (f2 : V -> R).
rewrite (_ : (fun t' => _) = f1 * f2); last first.
  by rewrite funeqE => t'; rewrite -[RHS]/(f1 t' * f2 t') /f1 /f2; reflexivity.
by rewrite {}/f1 {}/f2; exact: derivableM.
Qed.

End derivable_mulmx.

Section derive_SE.
Context {R : rcfType} {V : normedModType R} (M : V -> 'M[R^o]_4).

Lemma derivable_rot_of_hom x v : derivable M x v ->
  derivable (@rot_of_hom _ \o M) x v.
Proof.
move=> Mt1.
apply/derivable_mxP => i j; rewrite /rot_of_hom/=.
rewrite (_ : (fun _ => _) =
    fun y => (M y) (lshift 1 i) (lshift 1 j)); last first.
  by rewrite funeqE => y; rewrite !mxE.
by have /derivable_mxP := Mt1; exact.
Qed.

Lemma derivable_trans_of_hom x v : derivable M x v ->
  derivable (@trans_of_hom _ \o M) x v.
Proof.
move=> Mxv; apply/derivable_mxP => i j; rewrite /trans_of_hom/=.
rewrite (_ : (fun _ => _) =
    fun y => (M y) (rshift 3 i) (lshift 1 j)); last first.
  by rewrite funeqE => y; rewrite !mxE.
by have /derivable_mxP := Mxv; exact.
Qed.

Lemma derive1mx_SE t v : derivable M t v -> (forall t, M t \in 'SE3[R]) ->
  'D_v  M t = block_mx
    ('D_v (@rot_of_hom R^o \o M) t) 0
    ('D_v (@trans_of_hom R^o \o M) t) 0.
Proof.
move=> Mtv MSE.
rewrite !derive_mx//; [|exact: derivable_trans_of_hom
                       |exact: derivable_rot_of_hom].
rewrite block_mxEh.
rewrite {1}(_ : M =
    fun x => hom (rot_of_hom (M x)) (trans_of_hom (M x))); last first.
  by rewrite funeqE => x; rewrite -(SE3E (MSE x)).
apply/matrixP => i j.
rewrite 2!mxE; case: splitP => [j0 jj0|j0 jj0].
  rewrite (_ : j = lshift 1 j0); last exact/val_inj.
  rewrite mxE; case: splitP => [i1 ii1|i1 ii1].
    rewrite (_ : i = lshift 1 i1); last exact/val_inj.
    rewrite mxE; congr ('D_v _ t); rewrite funeqE => x.
    by rewrite /hom (block_mxEul _ _ _ _ i1 j0).
  rewrite (_ : i = rshift 3 i1); last exact/val_inj.
  rewrite mxE; congr ('D_v _ t); rewrite funeqE => x.
  by rewrite /hom (block_mxEdl (rot_of_hom (M x))).
rewrite (_ : j = rshift 3 j0) ?mxE; last exact/val_inj.
rewrite (ord1 j0).
case: (@splitP 3 1 i) => [i0 ii0|i0 ii0].
  rewrite (_ : i = lshift 1 i0); last exact/val_inj.
  rewrite (_ : (fun _ => _) = fun=> 0).
    by rewrite derive_cst mxE.
  by rewrite funeqE => x;  rewrite /hom (block_mxEur (rot_of_hom (M x))) mxE.
rewrite (_ : i = rshift 3 i0); last exact/val_inj.
rewrite (_ : (fun _ => _) = (fun=> 1)) ?derive_cst // (ord1 i0) ?mxE //.
by rewrite funeqE => x; rewrite /hom (block_mxEdr (rot_of_hom (M x))) mxE.
Qed.

End derive_SE.

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

Lemma derivable_row_belast (R : realFieldType) {V : normedModType R}
    n (u : V -> 'rV[R]_n.+2) (t : V) (v : V):
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

Lemma derive1mx_dotmul_belast {R : realFieldType} {V : normedModType R} n
    (u v : V -> 'rV[R]_n.+2) t w :
  derivable v t w ->
  let u' x := row_belast (u x) in let v' x := row_belast (v x) in
  u' t *d 'D_w v' t + (u t)``_ord_max *: derive (fun x => (v x)``_ord_max) t w =
  u t *d 'D_w v t.
Proof.
move=> vt1 u' v'.
rewrite (row_belast_last ('D_w v t)) ?addn1 // => /= ?.
rewrite dotmul_belast; congr (_ + _).
  rewrite 2!dotmulE [in RHS]big_ord_recr /=.
  rewrite castmxE mxE /=; case: fintype.splitP => [j /= /eqP/negPn|j _].
    by rewrite (gtn_eqF (ltn_ord j)).
  rewrite !mxE (_ : _ == _); last by apply/eqP/val_inj => /=; move: j => [[] ?].
  rewrite mulr0 addr0; apply/eq_bigr => i _; rewrite castmxE !mxE; congr (_ * _).
  case: fintype.splitP => [k /= ik|[] [] //= ?]; rewrite !mxE.
    rewrite derive_mx//; last first.
      rewrite /v'.
      apply/derivable_mxP/derivable_row_belast.
      exact/derivable_mxP.
    rewrite /= !mxE/=.
    rewrite derive_mx//.
    rewrite mxE/=.
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
by rewrite derive_mx// mxE.
Qed.

End row_belast.

(* TODO: could be derived from more generic lemmas about bilinearity in derive.v? *)
Section product_rules.

Global Instance is_diff_sum {R : numFieldType} {V W : normedModType R}
  n (h : 'I_n -> V -> W) (x : V)
  (dh : 'I_n -> V -> W) : (forall i, is_diff x (h i) (dh i)) ->
  is_diff x (\sum_(i < n) h i) (\sum_(i < n) dh i).
Proof.
by elim/big_ind2 : _ => // [|] *; [exact: is_diff_cst|exact: is_diffD].
Qed.

Lemma derive_dotmul {R : realFieldType} {V : normedModType R} n
    (u v : V -> 'rV[R]_n.+1) (t : V) (w : V) :
    derivable u t w -> derivable v t w ->
  'D_w (fun x => u x *d v x) t = 'D_w u t *d v t + u t *d 'D_w v t.
Proof.
move=> /derivable_mxP utw /derivable_mxP vtw.
under eq_fun do rewrite dotmulE.
set f := fun i : 'I__ => fun x => (u x) ``_ i * (v x) ``_ i.
rewrite (_ : (fun _ : V => _) = \sum_(k < _) f k); last first.
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite derive_sum; last by move=> i; exact: derivableM.
rewrite !dotmulE -big_split/=; apply: eq_bigr => i _.
by rewrite {}/f deriveM// mulrC addrC; congr (_ * _ + _ * _);
  rewrite derive_mx ?mxE//=; exact/derivable_mxP.
Qed.

(* NB: from Damien's LaSalle *)
Notation "p ..[ i ]" := (p 0 i) (at level 10).

Global Instance is_diff_component {R : realFieldType} n i (p : 'rV[R]_n.+1) :
  is_diff p (fun q => q..[i] : R^o) (fun q => q..[i]).
Proof.
have comp_lin : linear (fun q : 'rV[R]_n.+1 => q..[i] : R^o).
  by move=> ???; rewrite !mxE.
have comp_cont : continuous (fun q : 'rV[R]_n.+1 => q..[i] : R^o).
  move=> q A [_/posnumP[e] Ae] /=; apply/nbhs_ballP; exists e%:num => //=.
  by move=> r /(_ ord0) /(_ i) /Ae.
pose glM := GRing.isLinear.Build _ _ _ _ _ comp_lin.
pose gL : {linear 'rV_n.+1 -> R^o} := HB.pack (fun q : 'rV_n.+1 => q ..[ i]) glM.
apply: DiffDef; first exact: (@linear_differentiable _ _ _ gL).
by rewrite (@diff_lin _ _ _ gL).
Qed.

Global Instance is_diff_component_comp {R : realFieldType} (V : normedModType R) n
  (f : V -> 'rV[R]_n.+1) i p df : is_diff p f df ->
  is_diff p (fun q => (f q)..[i] : R^o) (fun q => (df q)..[i]).
Proof.
move=> dfp.
have -> : (fun q => (f q)..[i]) = (fun v => v..[i]) \o f by rewrite funeqE.
(* This should work *)
(* apply: is_diff_eq. *)
exact: is_diff_comp.
Qed.
(* /NB: from Damien's LaSalle *)

Global Instance is_diff_dotmul {R : realFieldType} m n (V := 'rV[R]_m.+1)
    (u v du dv : V -> 'rV[R]_n.+1) (t : V) :
  is_diff t u du -> is_diff t v dv ->
  is_diff t (fun x => u x *d v x)
            (fun x => u t *d dv x + v t *d du x).
Proof.
move=> udu vdv/=.
under eq_fun do rewrite dotmulE.
set f := fun i : 'I__ => (fun x => (u x) ``_ i) * (fun x => (v x) ``_ i).
rewrite [X in is_diff _ X _](_ : _ = \sum_(k < _) f k); last first.
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite [X in is_diff _ _ X](_ : _ = \sum_(i < n.+1)
    ((u t)``_i *: (fun x => (dv x)``_i) + (v t)``_i *: (fun x => (du x)``_i))); last first.
  by apply/funext => x; rewrite 2!dotmulE -big_split/= fct_sumE.
apply: is_diff_sum => i.
rewrite {}/f /=.
exact: is_diffM.
Qed.

Lemma differentiable_dotmul {R : realFieldType} m n (V := 'rV[R]_m.+1)
    (u v : V -> 'rV[R]_n.+1) (t : V) :
  differentiable u t ->
  differentiable v t ->
  differentiable (fun x => u x *d v x) t.
Proof.
move=> /differentiableP udu /differentiableP vdv/=.
by have [/=] := is_diff_dotmul udu vdv.
Qed.

Lemma derive_mulmx {R : realFieldType} {V : normedModType R} n m p
    (M : V -> 'M[R]_(n.+1, m.+1))
    (N : V -> 'M[R]_(m.+1, p.+1)) (t : V) w :
  derivable M t w -> derivable N t w ->
  'D_w (fun t => M t *m N t) t = 'D_w M t *m N t + M t *m 'D_w N t.
Proof.
move=> HM HN; apply/matrixP => i j.
rewrite derive_mx/=; last exact/derivable_mulmx.
rewrite ![in LHS]mxE.
rewrite (_ : (fun x => _) = fun x => \sum_k (M x) i k * (N x) k j); last first.
  by rewrite funeqE => x; rewrite !mxE.
rewrite (_ : (fun x => _) =
    fun x => (row i (M x)) *d (col j (N x))^T); last first.
  rewrite funeqE => z; rewrite dotmulE; apply eq_bigr => k _.
  by rewrite 3!mxE.
rewrite (derive_dotmul (derivable_row HM)); last first.
  by rewrite derivable_trmx/=; exact: derivable_col.
rewrite [in RHS]mxE; congr +%R.
  rewrite dotmulE.
  rewrite [in RHS]mxE.
  apply: eq_bigr => /= k _.
  rewrite !mxE/=.
  congr *%R.
  rewrite derive_mx//=; last first.
    exact: derivable_row.
  rewrite mxE.
  rewrite derive_mx//=.
  rewrite mxE/=.
  congr ('D_w _ t).
  by apply/funext => y; rewrite !mxE.
rewrite dotmulE.
rewrite [in RHS]mxE.
apply: eq_bigr => /= k _.
rewrite !mxE/=.
congr *%R.
rewrite derive_mx//=; last first.
  by rewrite derivable_trmx//=; exact/derivable_col.
rewrite !mxE//=.
rewrite derive_mx//= !mxE.
congr ('D_w _ t).
by apply/funext => y; rewrite !mxE.
Qed.

Lemma derive_crossmul {R : realFieldType} {V : normedModType R}
    (u v : V -> 'rV[R]_3) t w :
  derivable u t w -> derivable v t w ->
  'D_w (fun x => u x *v v x) t = 'D_w u t *v v t + u t *v 'D_w v t.
Proof.
move=> utw vtw.
evar (f : V -> 'rV[R]_3); rewrite (_ : (fun x : V => _) = f); last first.
  by rewrite funeqE => x; exact: crossmulE.
rewrite {}/f; apply/rowP => i; rewrite mxE.
rewrite derive_mx/=; last first.
  by apply: derivable_row3;
   apply: derivableB => //=;
      by apply: derivableM => //=; exact: derivable_coord.
rewrite !mxE/=.
rewrite (mxE_funeqE (fun x : V => _))/=.
rewrite 2!crossmulE !{1}[in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=].
- rewrite deriveB//=; [ |
    by apply: derivableM => //=; exact: derivable_coord..].
  rewrite deriveM//=; [|exact: derivable_coord..].
  rewrite deriveM//=; [|exact: derivable_coord..].
  rewrite addrCA -!addrA; congr (_ + (_ + _)).
    by rewrite derive_mx//= mxE.
    by rewrite mulrC derive_mx//= mxE.
    rewrite addrC opprD mulrC.
    rewrite derive_mx//= mxE.
    congr (_ - _)%R.
    by rewrite derive_mx//= mxE.
- (*TOOD: copipe *)
  rewrite deriveB//=; [ |
    by apply: derivableM => //=; exact: derivable_coord..].
  rewrite deriveM//=; [|exact: derivable_coord..].
  rewrite deriveM//=; [|exact: derivable_coord..].
  rewrite addrCA -!addrA; congr (_ + (_ + _)).
    by rewrite derive_mx//= mxE.
    by rewrite mulrC derive_mx//= mxE.
    rewrite addrC opprD mulrC.
    rewrite derive_mx//= mxE.
    congr (_ - _)%R.
    by rewrite derive_mx//= mxE.
- (*TOOD: copipe *)
  rewrite deriveB//=; [ |
    by apply: derivableM => //=; exact: derivable_coord..].
  rewrite deriveM//=; [|exact: derivable_coord..].
  rewrite deriveM//=; [|exact: derivable_coord..].
  rewrite addrCA -!addrA; congr (_ + (_ + _)).
    by rewrite derive_mx//= mxE.
    by rewrite mulrC derive_mx//= mxE.
    rewrite addrC opprD mulrC.
    rewrite derive_mx//= mxE.
    congr (_ - _)%R.
    by rewrite derive_mx//= mxE.
Qed.

End product_rules.

Section cross_product_matrix.

Lemma differential_crossmul {R : realFieldType} (v : 'rV[R]_3) y :
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

Lemma differential_crossmul2 (R : realFieldType) (v y : 'rV[R]_3) :
  'd (fun x : 'rV[R]_3 => x *v v) y = -1 \*: mx_lin1 \S( v ) :> (_ -> _).
Proof.
transitivity ('d (crossmul (- v)) y); last first.
  by rewrite differential_crossmul spinN mx_lin1N.
congr diff.
by rewrite funeqE => /= u; rewrite (@lieC _ (vec3 R)) linearNl.
Qed.

End cross_product_matrix.

(* [sciavicco] p.80-81 *)
Section derivative_of_a_rotation_matrix.
Context {R : realFieldType}.
Variable M : R -> 'M[R^o]_3.

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
rewrite derive_mulmx // ?derivable_trmx // derive_trmx//.
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
move=> p t; rewrite /p derive_mulmx; last first.
  exact: derivable_M.
  rewrite /derivable_mx => i j; exact: ex_derive.
rewrite derive_cst mul0mx add0r derive1mx_ang_vel mulmxA.
by rewrite -{1}(unspinK (ang_vel_mx_is_so t)) spinE.
Qed.

End derivative_of_a_rotation_matrix.
