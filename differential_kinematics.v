From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop finset ssralg matrix.
From mathcomp Require Import ssrnum.

Require Import Reals.
From mathcomp.analysis Require Import Rstruct Rbar boolp reals topology.
From mathcomp.analysis Require Import hierarchy landau forms derive.

Require Import euclidean3 rot skew.

(* WIP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section tmp.

Variable (V W : normedModType R).

Lemma derivable_sum n (f : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (f i) x v) -> derivable (\sum_(i < n) f i) x v.
Proof.
elim: n f => [f _|n IH f H].
  rewrite big_ord0 (_ : 0 = cst 0) //; exact: derivable_cst.
rewrite big_ord_recr /=; exact: derivableD (IH _ _) (H _).
Qed.

Lemma derive_sum n (f : 'I_n -> V -> W) (x v : V) :
  (forall i, derivable (f i) x v) ->
  derive (\sum_(i < n) f i) x v = \sum_(i < n) derive (f i) x v.
Proof.
elim: n f => [f _|n IH f H].
  by rewrite 2!big_ord0 (_ : 0 = cst 0) // derive_cst.
rewrite big_ord_recr deriveD // ?IH // ?big_ord_recr //; exact: derivable_sum.
Qed.

Lemma fct_sum n (x : V) (f : 'I_n -> V -> W):
  \sum_(k < n) f k x = (\sum_(k < n) f k) x.
Proof.
elim: n f => [f|n IH f]; first by rewrite 2!big_ord0.
by rewrite [in RHS]big_ord_recr /= -[RHS]/(_ x + _ x) -IH big_ord_recr.
Qed.

Definition derive1mx n m (M : R -> 'M[W]_(n, m)) := fun t =>
  \matrix_(i < n, j < m) (derive1 (fun t' : R => M t' i j) t : W).

Lemma derive1mx_cst n m (k : 'M[W]_(n, m)) : derive1mx (cst k) = cst 0.
Proof.
rewrite /derive1mx funeqE => t; apply/matrixP => i j; rewrite !mxE.
by rewrite derive1E (_ : (fun t' : R => _) = cst (k i j)) // derive_cst.
Qed.

Lemma derive1mxT n (K : R -> 'M[W]_(n, n)) t :
  derive1mx (fun x => (K x)^T) t = (derive1mx K t)^T.
Proof.
apply/matrixP => i j; rewrite !mxE.
by rewrite (_ : (fun _ => _) = (fun t => K t j i)) // funeqE => ?; rewrite mxE.
Qed.

End tmp.

Section tmp2.

Lemma row_mx_betail {R : ringType} n (r : 'rV[R]_n.+1) :
  r = castmx (erefl, addnC n 1%N)
    (row_mx (\row_(i < n) (r ``_ (widen_ord (leqnSn n) i)))
            ((r ``_ ord_max)%:M)).
Proof.
apply/rowP => i; rewrite castmxE mxE.
case: fintype.splitP => /= [j Hj|[] [] //= ? ni].
  by rewrite mxE; congr (_ ``_ _); apply val_inj.
rewrite mxE /= mulr1n; congr (_ ``_ _); apply val_inj; by rewrite /= ni addn0.
Qed.

Definition row_betail {R : ringType} n (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \row_(i < n) (v ``_ (widen_ord (leqnSn n) i)).

Lemma dotmul_betail {R : realType} n (u : 'rV[R]_n.+1) (v1 : 'rV[R]_n) v2 H :
  u *d castmx (erefl 1%nat, H) (row_mx v1 v2) =
    u *d castmx (erefl 1%nat, H) (row_mx v1 0%:M) +
    u *d castmx (erefl 1%nat, H) (row_mx 0 v2).
Proof.
rewrite -dotmulDr; congr dotmul; apply/matrixP => i j; rewrite !(castmxE,mxE) /=.
case: fintype.splitP => [k /= jk|[] [] // ? /= jn]; by rewrite !(mxE,addr0,add0r,mul0rn).
Qed.

End tmp2.

Section derivative_of_matrices.

Lemma derive1mx_dotmul_betail n (u v : R^o -> 'rV[R^o]_n.+1) t :
  let u' x := row_betail (u x) in
  let v' x := row_betail (v x) in
  u' t *d derive1mx v' t + (u t)``_ord_max *: derive (fun x => (v x)``_ord_max) t 1 =
  u t *d derive1mx v t.
Proof.
move=> u' v'.
rewrite (row_mx_betail (derive1mx v t)) dotmul_betail; congr (_ + _).
  rewrite 2!dotmulE [in RHS]big_ord_recr /=.
  rewrite castmxE mxE /=; case: fintype.splitP => [j /= /eqP/negPn|j _].
    by rewrite (gtn_eqF (ltn_ord j)).
  rewrite !mxE (_ : _ == _); last by apply/eqP/val_inj => /=; move: j => [[] ?].
  rewrite mulr0 addr0; apply/eq_bigr => i _.
  rewrite castmxE !mxE /=; congr (_ * _).
  case: fintype.splitP => [k /= ik|[] [] //= ?].
    rewrite !mxE; f_equal.
    rewrite funeqE => x; rewrite /v' !mxE; congr ((v _) _ _); by apply/val_inj.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
apply/esym.
rewrite dotmulE big_ord_recr /= (eq_bigr (fun=> 0)); last first.
  move=> i _.
  rewrite !castmxE mxE; case: fintype.splitP => [j /= ij| [] [] //= ?].
    by rewrite mxE mulr0.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
rewrite sumr_const mul0rn add0r castmxE /=; congr (_ * _).
rewrite mxE; case: fintype.splitP => [j /= /eqP/negPn | [] [] //= ? Hn].
  by rewrite (gtn_eqF (ltn_ord j)).
by rewrite !mxE derive1E (_ : _ == _).
Qed.

Definition derivable_rV n (u : R^o -> 'rV[R^o]_n) (t : R^o) v :=
  forall i, derivable (fun x : R^o => (u x)``_ i) t v.

Lemma derivable_rV_betail n (u : R^o -> 'rV[R^o]_n.+1) (t : R^o) (v : R^o):
  derivable_rV u t v -> derivable_rV (fun x => row_betail (u x)) t v.
Proof.
move=> H i; move: (H (widen_ord (leqnSn n) i)) => {H}.
set f := fun _ => _. set g := fun _ => _.
by rewrite (_ : f = g) // funeqE => x; rewrite /f /g mxE.
Qed.

Lemma derive1mx_dotmul n (u v : R^o -> 'rV[R^o]_n) (t : R^o) :
  derivable_rV u t 1 -> derivable_rV v t 1 ->
  derive1 (fun x => (u x *d v x : R^o)) t =
  derive1mx u t *d v t + u t *d derive1mx v t.
Proof.
move=> Hu Hv.
rewrite (_ : (fun x : R => _) = (fun x => \sum_k (u x)``_k * (v x)``_k)); last first.
  rewrite funeqE => x; by rewrite dotmulE.
rewrite derive1E.
set f := fun i : 'I__ => (fun x : R^o => ((u x) ``_ i * (v x) ``_ i) : R^o).
rewrite (_ : (fun x : R => _) = \sum_(k < _) f k); last first.
  by rewrite funeqE => x; rewrite /f /= -fct_sum.
rewrite derive_sum; last first.
  move=> i; rewrite {}/f.
  set f1 := fun x : R^o=> ((u x)``_ i) : R^o.
  set f2 := fun x : R^o=> ((v x)``_ i) : R^o.
  rewrite (_ : (fun _ : R^o => _) = f1 * f2); last by rewrite funeqE.
  apply derivableM; rewrite /f1 /f2.
  apply Hu.
  apply Hv.
rewrite {}/f.
elim: n u v => [u v|n IH u v] in Hu Hv *.
  rewrite big_ord0 (_ : v t = 0) ?dotmulv0 ?add0r; last by apply/rowP => -[] [].
  rewrite (_ : u t = 0) ?dotmul0v //; by apply/rowP => -[] [].
rewrite [LHS]big_ord_recr /=.
set u' := fun x => row_betail (u x). set v' := fun x => row_betail (v x).
transitivity (derive1mx u' t *d v' t + u' t *d derive1mx v' t +
  derive (fun x : R^o => (u x)``_ord_max * (v x)``_ord_max) t 1).
  rewrite -IH; last 2 first.
    by apply derivable_rV_betail.
    by apply derivable_rV_betail.
  congr (_ + _); apply eq_bigr => i _; congr (derive _ t 1).
  by rewrite funeqE => x; rewrite !mxE.
rewrite deriveM /=; last 2 first.
  apply Hu.
  apply Hv.
rewrite -!addrA addrC addrA -(addrA (_ + _)) [in RHS]addrC.
rewrite derive1mx_dotmul_betail; congr (_ + _).
by rewrite [in RHS]dotmulC -derive1mx_dotmul_betail addrC dotmulC.
Qed.

Lemma derive1mx_crossmul (r1 r2 : R^o -> 'rV[R^o]_3) t :
  derive1mx (fun x => (r1 x *v r2 x) : 'rV[R^o]_3) t =
  derive1mx r1 t *v r2 t + r1 t *v derive1mx r2 t.
Proof.
Abort.

Lemma derive1mxM n m p (M : R^o -> 'M[R^o]_(n.+1, m.+1))
  (N : R^o -> 'M[R^o]_(m.+1, p.+1)) (t : R^o) :
  derive1mx (fun t => M t *m N t) t =
    derive1mx M t *m (N t) + (M t) *m (derive1mx N t).
Proof.
apply/matrixP => i j.
rewrite ![in LHS]mxE (_ : (fun x => (M x *m N x) i j) =
  (fun x => \sum_k (M x) i k * (N x) k j)); last first.
  by rewrite funeqE => x; rewrite !mxE.
Admitted.

End derivative_of_matrices.

Section derivative_of_a_rotation_matrix.

Variable M : R -> 'M[R^o]_3. (* time-varying matrix *)
Hypothesis MSO : forall t, M t \is 'SO[real_realType]_3.

Definition s t := derive1mx M t * (M t)^T.

Lemma s_skew_symmetric t : s t \is 'so[real_realType]_3.
Proof.
rewrite antiE -subr_eq0 opprK; apply/eqP; rewrite /s trmx_mul trmxK mulmxE.
have : (fun t => M t * (M t)^T) = cst 1.
  rewrite funeqE => t'.
  by move: (MSO t'); rewrite rotationE orthogonalE => /andP[/eqP].
move/(congr1 (fun x => derive1mx x t)); rewrite derive1mx_cst -[cst 0 _]/(0).
by rewrite derive1mxM derive1mxT.
Qed.

(* [sciavicco] eqn 3.7 *)
Lemma derive_rot_skew (t : R) : derive1mx M t = s t * M t.
Proof.
move: (s_skew_symmetric t); rewrite antiE -subr_eq0 opprK => /eqP.
rewrite {1 2}/s trmx_mul trmxK => /(congr1 (fun x => x * M t)).
rewrite mul0r mulrDl -{1}mulrA -{1}(rotation_inv (MSO t)).
rewrite mulVr ?mulr1 ?unitmxE ?rotation_det // ?unitr1 //.
move/eqP; rewrite addr_eq0 => /eqP ->.
move: (s_skew_symmetric t); rewrite antiE => /eqP ->.
by rewrite /s trmx_mul trmxK mulNr.
Qed.

End derivative_of_a_rotation_matrix.
