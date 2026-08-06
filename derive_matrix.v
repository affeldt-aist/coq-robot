(* robot-rocq (c) 2026 AIST and INRIA. License: LGPL-2.1-or-later. *)
From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrint ssrnum rat.
From mathcomp Require Import closed_field polyrcf matrix mxalgebra mxpoly zmodp.
From mathcomp Require Import interval_inference.
From mathcomp Require Import realalg complex fingroup perm.
From mathcomp Require Import sesquilinear ring_tactic .
From mathcomp Require Import boolp reals classical_sets.
From mathcomp Require Import topology normedtype landau derive trigo.
From mathcomp Require Import functions.
Require Import ssr_ext euclidean rigid skew.

(**md**************************************************************************)
(* # Derivatives of time-varying matrices                                     *)
(*                                                                            *)
(* ```                                                                        *)
(*        ang_vel_mx M == angular velocity matrix of M(t)                     *)
(*         ang_vel M t == angular velocity                                    *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* This is to avoid a bug in MathComp-Analysis 1.17.0 *)
Remove Hints is_derive_mx : typeclass_instances.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.

Lemma mx_lin1N (R : pzRingType) n (M : 'M[R]_n) :
  mx_lin1 (- M) = -1 \*: mx_lin1 M :> ( _ -> _).
Proof. by rewrite funeqE => v /=; rewrite scaleN1r mulmxN. Qed.

Import Order.Def.

(* NB: added to be able to produce the following instance to be able to use bigop lemmas *)
Lemma nng_max0r {K : realFieldType} : left_id ((0:K)%:nng) (@maxr {nonneg K}).
Proof.
move=> x.
rewrite /max; case: ifPn => //.
rewrite -leNgt => x0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact: x0.
by have : 0 <= x%:nngnum by []. (* NB: this should be automatic *)
Qed.

(* TODO: backport to MCA *)
HB.instance Definition _ {K : realFieldType} :=
  Monoid.isComLaw.Build {nonneg K} 0%:nng max maxA maxC nng_max0r.

Lemma norm_trmx (R : realFieldType) m n (M : 'M[R]_(m, n)) : `|M^T| = `|M|.
Proof.
rewrite [LHS]mx_normE/=.
under eq_bigr do rewrite mxE.
rewrite -(pair_big xpredT xpredT (fun i j => `|M j i|%:nng))/=.
by rewrite exchange_big//= pair_big.
Qed.

Section pointwise_derivable.
Context {R : realFieldType} {V W : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

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
      `|l - x^-1 *: ((M (x *: v + t))^T - (M t)^T)|).
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
  rewrite [leLHS](_ : _ = `|l - x^-1 *: ((M (x *: v + t)) - (M t))|).
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

Lemma derivable_coord (a : V -> 'rV[R]_n) t v (i : 'I_n) :
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

Section pointwise_derivable_TODO.
Context {R : realFieldType} {V W : normedModType R} {m n : nat}.
Implicit Types M : V -> 'M[R]_(m, n).

(* PR to MCA *)
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
  (* TODO: there should be a lemma for that in MC, let's propose one *)
  destruct m.
    by rewrite bigmax_eq_id// => -[[[]]].
  destruct n.
    by rewrite bigmax_eq_id// => -[? [[]]].
  exact: le_trans (le_bigmax _ _ (ord0, ord0)).
move=> j _.
rewrite !mxE.
under eq_bigr do rewrite !mxE.
exact: le_trans (le_bigmax _ _ (i, j.2)).
Unshelve. all: by end_near. Qed.

(* PR to MCA *)
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
  (* TODO: there should be a lemma for that in MC, let's propose one *)
  destruct m.
    by rewrite bigmax_eq_id// => -[[[]]].
  destruct n.
    by rewrite bigmax_eq_id// => -[? [[]]].
  exact: le_trans (le_bigmax _ _ (ord0, ord0)).
move=> j _.
rewrite !mxE.
under eq_bigr do rewrite !mxE.
exact: le_trans (le_bigmax _ _ (j.1, i)).
Unshelve. all: by end_near. Qed.

(* TODO: PR to MCA *)
Lemma derivable_mx_is_scalar (a : V -> R) t v :
  derivable a t v -> derivable (fun x : V => (a x)%:M : 'M_1) t v.
Proof.
move=> /cvg_ex[/= l Hl]; apply/cvg_ex; exists l%:M => //.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0)[r/= r0 re].
near=> x.
rewrite /Num.Def.normr/= mx_normrE.
apply: (bigmax_le _ (ltW e0)) => /= -[i j] _.
rewrite {i}(ord1 i) {j}(ord1 j)/= ![in leLHS]mxE/= !mulr1n.
apply: re.
  rewrite /= sub0r normrN.
  by near: x; exact: dnbhs0_lt.
by near: x; exact: nbhs_dnbhs_neq.
Unshelve. all: by end_near. Qed.

(* NB: to stay in robot-rocq? *)
Lemma derivable_row3 (a b c : V -> R) t v :
  derivable a t v -> derivable b t v -> derivable c t v ->
  derivable (fun x => row3 (a x) (b x) (c x)) t v.
Proof.
move=> da db dc.
under eq_fun do rewrite row3E/=.
apply: (@derivable_row_mx _ _ 1 2); first exact: derivable_mx_is_scalar.
by apply: (@derivable_row_mx _ _ 1 1); exact: derivable_mx_is_scalar.
Qed.

End pointwise_derivable_TODO.

Section pointwise_derive.
Local Open Scope classical_set_scope.
Context {R : realFieldType} {V W : normedModType R} .

(* TODO: PR to MCA in progress *)
Lemma derive_trmx {m n : nat} (M : V -> 'M[R]_(m, n)) t v :
  derivable M t v -> 'D_v (trmx \o M) t = ('D_v M t)^T.
Proof.
move=> Mt1.
rewrite !derive_mx//=; first by rewrite derivable_trmx.
apply/matrixP => i j; rewrite !mxE.
by under eq_fun do rewrite mxE.
Qed.

End pointwise_derive.

(* TODO: PR to MCA *)
Lemma derivable_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v -> derivable (lsubmx \o f) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= l Hl]:= df1.
apply/cvg_ex => /=; exists (l``_(lshift n2 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hl => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, lshift n2 j)).
by rewrite !mxE.
Qed.

(* TODO: PR to MCA *)
Lemma derive_lsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v ->
  'D_v (lsubmx \o f) t = @lsubmx _ _ n1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE/=; first exact: derivable_lsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.

(* TODO: PR to MCA *)
Lemma derivable_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v -> derivable (rsubmx \o f) t v.
Proof.
move=> /= => df1.
apply/derivable_mxP => i j/=.
rewrite (ord1 i).
have /cvg_ex[/= r Hr]:= df1.
apply/cvg_ex => /=; exists (r``_(rshift n1 j)).
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : Hr => /(_ _ e0).
apply: filterS => x.
apply: le_trans.
rewrite [in leRHS]/Num.Def.normr/= mx_normrE.
apply: le_trans; last first.
  exact: (le_bigmax _ _ (ord0, rshift n1 j)).
by rewrite !mxE.
Qed.

(* TODO: PR to MCA *)
Lemma derive_rsubmx {R : realFieldType} {V : normedModType R} {n1 n2}
    (f : V -> 'rV[R]_(n1 + n2)) t v :
  derivable f t v ->
  'D_v (rsubmx \o f) t = @rsubmx _ _ n1 _ ('D_v f t).
Proof.
move=> df1; apply/matrixP => i j; rewrite !mxE /=.
rewrite derive_mx ?mxE/=; first exact: derivable_rsubmx.
rewrite derive_mx ?mxE//=; congr ('D_v _ t).
by apply/funext => x; rewrite !mxE.
Qed.

Section derivable_mulmx.
Context {R : realFieldType} {V : normedModType R} {m n k : nat}.

(* TODO: PR to MCA *)
Lemma derivable_mulmx
    (f : V -> 'M[R]_(m, k)) (g : V -> 'M[R]_(k, n)) t v :
  derivable f t v -> derivable g t v -> derivable (fun x => f x *m g x) t v.
Proof.
move=> /derivable_mxP Hf /derivable_mxP Hg; apply/derivable_mxP => a b.
evar (f1 : 'I_k -> V -> R).
rewrite (_ : (fun x => _) = \sum_i f1 i).
  rewrite funeqE => t'; rewrite mxE fct_sumE; apply: eq_bigr => k0 _.
  by rewrite /f1; reflexivity.
rewrite {}/f1; apply: derivable_sum => k0.
evar (f1 : V -> R). evar (f2 : V -> R).
rewrite (_ : (fun t' => _) = f1 * f2).
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
    fun y => (M y) (lshift 1 i) (lshift 1 j)).
  by rewrite funeqE => y; rewrite !mxE.
by have /derivable_mxP := Mt1; exact.
Qed.

Lemma derivable_trans_of_hom x v : derivable M x v ->
  derivable (@trans_of_hom _ \o M) x v.
Proof.
move=> Mxv; apply/derivable_mxP => i j; rewrite /trans_of_hom/=.
rewrite (_ : (fun _ => _) =
    fun y => (M y) (rshift 3 i) (lshift 1 j)).
  by rewrite funeqE => y; rewrite !mxE.
by have /derivable_mxP := Mxv; exact.
Qed.

Lemma derive1mx_SE t v : derivable M t v -> (forall t, M t \in 'SE3[R]) ->
  'D_v  M t = block_mx
    ('D_v (@rot_of_hom R^o \o M) t) 0
    ('D_v (@trans_of_hom R^o \o M) t) 0.
Proof.
move=> Mtv MSE.
rewrite !derive_mx/=; [|exact: derivable_rot_of_hom
                       |exact: derivable_trans_of_hom|].
  by [].
rewrite block_mxEh.
rewrite {1}(_ : M =
    fun x => hom (rot_of_hom (M x)) (trans_of_hom (M x))).
  by rewrite funeqE => x; rewrite -(SE3E (MSE x)).
apply/matrixP => i j.
rewrite 2!mxE; case: splitP => [j0 jj0|j0 jj0].
  rewrite (_ : j = lshift 1 j0); first exact/val_inj.
  rewrite mxE; case: splitP => [i1 ii1|i1 ii1].
    rewrite (_ : i = lshift 1 i1); first exact/val_inj.
    rewrite mxE; congr ('D_v _ t); rewrite funeqE => x.
    by rewrite /hom (block_mxEul _ _ _ _ i1 j0).
  rewrite (_ : i = rshift 3 i1); first exact/val_inj.
  rewrite mxE; congr ('D_v _ t); rewrite funeqE => x.
  by rewrite /hom (block_mxEdl (rot_of_hom (M x))).
rewrite (_ : j = rshift 3 j0) ?mxE; first exact/val_inj.
rewrite (ord1 j0).
case: (@splitP 3 1 i) => [i0 ii0|i0 ii0].
  rewrite (_ : i = lshift 1 i0); first exact/val_inj.
  rewrite (_ : (fun _ => _) = fun=> 0).
    by rewrite funeqE => x;  rewrite /hom (block_mxEur (rot_of_hom (M x))) mxE.
  by rewrite derive_cst mxE.
rewrite (_ : i = rshift 3 i0); first exact/val_inj.
rewrite (_ : (fun _ => _) = (fun=> 1)) ?derive_cst // (ord1 i0) ?mxE //.
by rewrite funeqE => x; rewrite /hom (block_mxEdr (rot_of_hom (M x))) mxE.
Qed.

End derive_SE.

Section row_belast.

Lemma derivable_row_belast (R : realFieldType) {V : normedModType R}
    n (u : V -> 'rV[R]_n.+1) (t : V) (v : V):
  derivable u t v -> derivable (fun x => row_belast (u x)) t v.
Proof.
move=> /derivable_mxP H.
apply/derivable_mxP => i j.
move: (H ord0 (widen_ord (leqnSn n) j)) => {H}.
set f := fun _ => _. set g := fun _ => _.
by rewrite (_ : f = g) // funeqE => x; rewrite /f /g mxE.
Qed.

Lemma dotmul_belast {R : realFieldType} n (u : 'rV[R]_n.+1) (v1 : 'rV[R]_n) v2 H :
  u *d castmx (erefl 1%nat, H) (row_mx v1 v2) =
    u *d castmx (erefl 1%nat, H) (row_mx v1 0%:M) +
    u *d castmx (erefl 1%nat, H) (row_mx 0 v2).
Proof.
rewrite -dotmulDr; congr dotmul; apply/matrixP => i j; rewrite !(castmxE,mxE) /=.
case: fintype.splitP => [k /= jk|[] [] // ? /= jn]; by rewrite !(mxE,addr0,add0r,mul0rn).
Qed.

Lemma derive1mx_dotmul_belast {R : realFieldType} {V : normedModType R} n
    (u v : V -> 'rV[R]_n.+1) t w :
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
  rewrite !mxE (_ : _ == _); first by apply/eqP/val_inj => /=; move: j => [[] ?].
  rewrite mulr0 addr0; apply/eq_bigr => i _; rewrite castmxE !mxE; congr (_ * _).
  case: fintype.splitP => [k /= ik|[] [] //= ?]; rewrite !mxE.
    rewrite derive_mx/=.
      rewrite /v'.
      exact/derivable_row_belast.
    rewrite /= !mxE/=.
    rewrite derive_mx//.
    rewrite mxE/=.
    f_equal.
    by rewrite funeqE => x; rewrite /v' !mxE; congr ((v _) _ _); by apply/val_inj.
  by rewrite addn0 => /eqP/negPn; rewrite (ltn_eqF (ltn_ord i)).
apply/esym.
rewrite dotmulE big_ord_recr /= (eq_bigr (fun=> 0)).
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

(* TODO: PR to MCA *)
Global Instance is_diff_sum {R : numFieldType} {V W : normedModType R}
  n (h : 'I_n -> V -> W) (x : V)
  (dh : 'I_n -> V -> W) : (forall i, is_diff x (h i) (dh i)) ->
  is_diff x (\sum_(i < n) h i) (\sum_(i < n) dh i).
Proof.
by elim/big_ind2 : _ => // [|] *; [exact: is_diff_cst|exact: is_diffD].
Qed.

Lemma derive_dotmul {R : realFieldType} {V : normedModType R} n
    (u v : V -> 'rV[R]_n) (t : V) (w : V) :
    derivable u t w -> derivable v t w ->
  'D_w (fun x => u x *d v x) t = 'D_w u t *d v t + u t *d 'D_w v t.
Proof.
move=> /derivable_mxP utw /derivable_mxP vtw.
under eq_fun do rewrite dotmulE.
set f := fun i : 'I__ => fun x => (u x) ``_ i * (v x) ``_ i.
rewrite (_ : (fun _ : V => _) = \sum_(k < _) f k).
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite derive_sum; first by move=> i; exact: derivableM.
rewrite !dotmulE -big_split/=; apply: eq_bigr => i _.
rewrite {}/f deriveM/=.
  by [].
  by [].
rewrite mulrC addrC; congr (_ * _ + _ * _);
  rewrite derive_mx ?mxE/=.
exact/derivable_mxP.
by [].
exact/derivable_mxP.
by [].
Qed.

(* NB: from Damien's LaSalle *)
Global Instance is_diff_component {R : realFieldType} n i (p : 'rV[R]_n) :
  is_diff p (fun q => q..[i] : R^o) (fun q => q..[i]).
Proof.
have comp_lin : linear (fun q : 'rV[R]_n => q..[i] : R^o).
  by move=> ???; rewrite !mxE.
have comp_cont : continuous (fun q : 'rV[R]_n => q..[i] : R^o).
  move=> q A [_/posnumP[e] Ae] /=; apply/nbhs_ballP; exists e%:num => //=.
  by move=> r [e0] /(_ ord0) /(_ i) /Ae.
pose glM := GRing.isLinear.Build _ _ _ _ _ comp_lin.
pose gL : {linear 'rV_n -> R^o} := HB.pack (fun q : 'rV_n => q ..[ i]) glM.
apply: DiffDef; first exact: (@linear_differentiable _ _ _ gL).
by rewrite (@diff_lin _ _ _ gL).
Qed.

Global Instance is_diff_component_comp {R : realFieldType} (V : normedModType R) n
  (f : V -> 'rV[R]_n) i p df : is_diff p f df ->
  is_diff p (fun q => (f q)..[i] : R^o) (fun q => (df q)..[i]).
Proof.
move=> dfp.
have -> : (fun q => (f q)..[i]) = (fun v => v..[i]) \o f by rewrite funeqE.
(* This should work *)
(* apply: is_diff_eq. *)
exact: is_diff_comp.
Qed.
(* /NB: from Damien's LaSalle *)

Global Instance is_diff_dotmul {R : realFieldType} m n (V := 'rV[R]_m)
    (u v du dv : V -> 'rV[R]_n) (t : V) :
  is_diff t u du -> is_diff t v dv ->
  is_diff t (fun x => u x *d v x)
            (fun x => u t *d dv x + v t *d du x).
Proof.
move=> udu vdv/=.
under eq_fun do rewrite dotmulE.
set f := fun i : 'I__ => (fun x => (u x) ``_ i) * (fun x => (v x) ``_ i).
rewrite [X in is_diff _ X _](_ : _ = \sum_(k < _) f k).
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite [X in is_diff _ _ X](_ : _ = \sum_(i < n)
    ((u t)``_i *: (fun x => (dv x)``_i) + (v t)``_i *: (fun x => (du x)``_i))).
  by apply/funext => x; rewrite 2!dotmulE -big_split/= fct_sumE.
apply: is_diff_sum => i.
rewrite {}/f /=.
exact: is_diffM.
Qed.

Lemma differentiable_dotmul {R : realFieldType} m n (V := 'rV[R]_m)
    (u v : V -> 'rV[R]_n) (t : V) :
  differentiable u t ->
  differentiable v t ->
  differentiable (fun x => u x *d v x) t.
Proof.
move=> /differentiableP udu /differentiableP vdv/=.
by have [/=] := is_diff_dotmul udu vdv.
Qed.

Lemma derivable_dotmul {R : realFieldType} {n}
    (u v : R -> 'rV[R]_n) t :
  derivable u t 1 -> derivable v t 1 ->
  derivable (fun x => u x *d v x) t 1.
Proof.
move=> ut1 vt1/=.
rewrite /dotmul.
rewrite (_ : (fun x : R => _) =
    \sum_k (fun x : R => (u x)``_k * (v x) 0 k)).
  apply/funext => x.
   rewrite !mxE.
   under eq_bigr do rewrite !mxE.
   elim/big_ind2 : _ => //= f a g b -> ->.
   by rewrite fctE.
apply: derivable_sum => i.
by apply: derivableM => /=; exact: derivable_coord.
Qed.

(* NB: depends on dotmul, so cannot be PRed to MCA right away *)
Lemma derive_mulmx {R : realFieldType} {V : normedModType R} n m p
    (M : V -> 'M[R]_(n, m))
    (N : V -> 'M[R]_(m, p)) (t : V) w :
  derivable M t w -> derivable N t w ->
  'D_w (fun t => M t *m N t) t = 'D_w M t *m N t + M t *m 'D_w N t.
Proof.
move=> HM HN; apply/matrixP => i j.
rewrite derive_mx/=; first exact/derivable_mulmx.
rewrite ![in LHS]mxE.
rewrite (_ : (fun x => _) = fun x => \sum_k (M x) i k * (N x) k j).
  by rewrite funeqE => x; rewrite !mxE.
rewrite (_ : (fun x => _) =
    fun x => (row i (M x)) *d (col j (N x))^T).
  rewrite funeqE => z; rewrite dotmulE; apply eq_bigr => k _.
  by rewrite 3!mxE.
rewrite (derive_dotmul (derivable_row HM)).
  by rewrite derivable_trmx/=; exact: derivable_col.
rewrite [in RHS]mxE; congr +%R.
  rewrite dotmulE.
  rewrite [in RHS]mxE.
  apply: eq_bigr => /= k _.
  rewrite !mxE/=.
  congr *%R.
  rewrite derive_mx/=.
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
rewrite derive_mx/=.
  by rewrite derivable_trmx/=; exact/derivable_col.
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
evar (f : V -> 'rV[R]_3); rewrite (_ : (fun x : V => _) = f).
  by rewrite funeqE => x; exact: crossmulE.
rewrite {}/f; apply/rowP => i; rewrite mxE.
rewrite derive_mx/=.
  by apply: derivable_row3;
   apply: derivableB => /=;
      by apply: derivableM => /=; exact: derivable_coord.
rewrite !mxE/=.
under eq_fun do rewrite !mxE/=.
rewrite 2!crossmulE !{1}[in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=].
- rewrite deriveB/=; [
    by apply: derivableM => /=; exact: derivable_coord..|].
  rewrite deriveM/=; [exact: derivable_coord..|].
  rewrite deriveM/=; [exact: derivable_coord..|].
  rewrite addrCA -!addrA; congr (_ + (_ + _)).
    by rewrite derive_mx//= mxE.
    by rewrite mulrC derive_mx//= mxE.
    rewrite [in LHS]addrC opprD mulrC.
    rewrite derive_mx//= mxE.
    congr (_ - _)%R.
    by rewrite derive_mx//= mxE.
- (*TOOD: copipe *)
  rewrite deriveB/=; [
    by apply: derivableM => /=; exact: derivable_coord..|].
  rewrite deriveM/=; [exact: derivable_coord..|].
  rewrite deriveM/=; [exact: derivable_coord..|].
  rewrite addrCA -!addrA; congr (_ + (_ + _)).
    by rewrite derive_mx//= mxE.
    by rewrite mulrC derive_mx//= mxE.
    rewrite [in LHS]addrC opprD mulrC.
    rewrite derive_mx//= mxE.
    congr (_ - _)%R.
    by rewrite derive_mx//= mxE.
- (*TOOD: copipe *)
  rewrite deriveB/=; [
    by apply: derivableM => /=; exact: derivable_coord..|].
  rewrite deriveM/=; [exact: derivable_coord..|].
  rewrite deriveM/=; [exact: derivable_coord..|].
  rewrite addrCA -!addrA; congr (_ + (_ + _)).
    by rewrite derive_mx/= ?mxE.
    by rewrite mulrC derive_mx/= ?mxE.
    rewrite [in LHS]addrC opprD mulrC.
    rewrite derive_mx/= ?mxE.
      by [].
    congr (_ - _)%R.
    by rewrite derive_mx//= mxE.
Qed.

End product_rules.

Section cross_product_matrix.

Lemma differential_crossmul {R : realFieldType} (v : 'rV[R]_3) y :
  'd (crossmul v) y = mx_lin1 \S( v ) :> (_ -> _).
Proof.
rewrite (_ : crossmul v = (fun x => x *m \S( v ))).
  by rewrite funeqE => ?; rewrite -spinE.
rewrite (_ : mulmx^~ \S(v) = @mulmxr _ 1 _ _ \S(v)); first by rewrite funeqE.
rewrite diff_lin //= => x.
suff : differentiable (mulmxr \S(v)) (x : 'rV[R^o]_3).
  by move/differentiable_continuous.
rewrite (_ : mulmxr \S(v) = (fun z => \sum_i z``_i *: row i \S(v))).
  rewrite funeqE => z; by rewrite -mulmx_sum_row.
set f := fun (i : 'I_3) (z : 'rV_3) => z``_i *: row i \S(v) : 'rV_3.
rewrite (_ : (fun _ => _) = \sum_i f i); first by rewrite funeqE => ?; by rewrite fct_sumE.
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
Variable M : R -> 'M[R]_3.

Definition ang_vel_mx t : 'M_3 := (M t)^T * 'D_1 M t.

Definition body_ang_vel_mx t : 'M_3 := 'D_1 M t *m (M t)^T.

Hypothesis MO : forall t, M t \is 'O[ R ]_3.

(* [sciavicco] eqn 3.7 *)
Lemma derive1mx_ang_vel t : 'D_1 M t = M t * ang_vel_mx t.
Proof.
by rewrite /ang_vel_mx mulrA -mulmxE orthogonal_mul_tr// mul1mx.
Qed.

Hypothesis derivable_M : forall t, derivable M t 1.

Lemma ang_vel_mx_is_so t : ang_vel_mx t \is 'so[ R ]_3.
Proof.
have : (fun t => (M t)^T * M t) = cst 1.
  rewrite funeqE => x; by rewrite -orthogonal_inv // mulVr // orthogonal_unit.
move/(congr1 (fun f => 'D_1 f t)).
rewrite derive_cst.
rewrite derive_mulmx/= ?derivable_trmx ?derive_trmx//.
move=> /eqP; rewrite addr_eq0 => /eqP H.
by rewrite antiE /ang_vel_mx trmx_mul trmxK H opprK.
Qed.

(* angular velocity (a free vector) *)
Definition ang_vel t := unspin (ang_vel_mx t).

Lemma ang_vel_mxE t : ang_vel_mx t = \S( ang_vel t).
Proof. by rewrite /ang_vel unspinK // ang_vel_mx_is_so. Qed.

Lemma derive1mx_rot (p' : 'rV[R]_3 (* constant vector *)) :
  let p := fun t => p' *m M t in
  forall t, 'D_1 p t = ang_vel t *v p t.
Proof.
move=> p t; rewrite /p derive_mulmx.
  apply/derivable_mxP => i j; exact: ex_derive.
  exact: derivable_M.
rewrite derive_cst mul0mx add0r derive1mx_ang_vel mulmxA.
by rewrite -{1}(unspinK (ang_vel_mx_is_so t)) spinE.
Qed.

End derivative_of_a_rotation_matrix.
