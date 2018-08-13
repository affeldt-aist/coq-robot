From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop finset ssralg matrix.
From mathcomp Require Import interval ssrnum.

Require Import Reals.
From mathcomp.analysis Require Import boolp reals Rstruct Rbar classical_sets posnum.
From mathcomp.analysis Require Import topology hierarchy landau forms derive.

Require Import ssr_ext euclidean3 rot skew.

(* WIP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

(* TODO: move *)
Lemma mx_lin1N (R : ringType) n (M : 'M[R]_n) :
  mx_lin1 (- M) = -1 \*: mx_lin1 M :> ( _ -> _).
Proof. rewrite funeqE => v /=; by rewrite scaleN1r mulmxN. Qed.

Section mx.

Variable (V W : normedModType R).

Lemma mxE_funeqE n m (f : V -> 'I_n -> 'I_m -> W) i j :
  (fun x => (\matrix_(i < n, j < m) (f x i j)) i j) =
  (fun x => f x i j).
Proof. by rewrite funeqE => ?; rewrite mxE. Qed.

End mx.

Section derive_mx.

Variable (V W : normedModType R).

Definition derivable_mx m n (M : R -> 'M[W]_(m, n)) t v :=
  forall i j, derivable (fun x : R^o => (M x) i j) t v.

Definition derive1mx m n (M : R -> 'M[W]_(m, n)) := fun t =>
  \matrix_(i < m, j < n) (derive1 (fun x => M x i j) t : W).

Variables m n : nat.
Implicit Types M N : R -> 'M[W]_(m, n).

Lemma derivable_mxD M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derivable_mx (fun x => M x + N x) t 1.
Proof.
move=> Hf Hg a b. evar (f1 : R -> W). evar (f2 : R -> W).
rewrite (_ : (fun x => _) = f1 + f2); last first.
  rewrite funeqE => x; rewrite -[RHS]/(f1 x + f2 x) mxE /f1 /f2; reflexivity.
rewrite {}/f1 {}/f2; exact: derivableD.
Qed.

Lemma trmx_derivable M t v :
  derivable_mx M t v = derivable_mx (fun x => (M x)^T) t v.
Proof.
rewrite propeqE; split => [H j i|H i j].
by rewrite (_ : (fun _ => _) = (fun x => M x i j)) // funeqE => z; rewrite mxE.
by rewrite (_ : (fun _ => _) = (fun x => (M x)^T j i)) // funeqE => z; rewrite mxE.
Qed.

Lemma derivable_mx_row M t i :
  derivable_mx M t 1 -> derivable_mx (row i \o M) t 1.
Proof.
move=> H a b.
by rewrite (_ : (fun _ => _) = (fun x => (M x) i b)) // funeqE => z; rewrite mxE.
Qed.

Lemma derivable_mx_col M t i :
  derivable_mx M t 1 -> derivable_mx (trmx \o col i \o M) t 1.
Proof.
move=> H a b.
by rewrite (_ : (fun _ => _) = (fun x => (M x) b i)) // funeqE => z; rewrite 2!mxE.
Qed.

Lemma derive1mx_cst (P : 'M[W]_(m, n)) : derive1mx (cst P) = cst 0.
Proof.
rewrite /derive1mx funeqE => t; apply/matrixP => i j; rewrite !mxE.
by rewrite derive1E (_ : (fun _ => _) = cst (P i j)) // derive_val.
Qed.

Lemma derive1mx_tr M t : derive1mx (trmx \o M) t = (derive1mx M t)^T.
Proof.
apply/matrixP => i j; rewrite !mxE.
by rewrite (_ : (fun _ => _) = (fun t => M t j i)) // funeqE => ?; rewrite mxE.
Qed.

Lemma derive1mxD M N t : derivable_mx M t 1 -> derivable_mx N t 1 ->
  derive1mx (M + N) t = derive1mx M t + derive1mx N t.
Proof.
move=> Hf Hg; apply/matrixP => a b; rewrite /derive1mx !mxE.
rewrite (_ : (fun _ => _) = (fun x => M x a b) \+ fun x => N x a b); last first.
  by rewrite funeqE => ?; rewrite mxE.
by rewrite derive1E deriveD // 2!derive1E.
Qed.

End derive_mx.

Section derive_mx_R.

Variables m n k : nat.

Lemma derivable_mxM (f : R -> 'M[R^o]_(m, k)) (g : R -> 'M[R^o]_(k, n)) t :
  derivable_mx f t 1 -> derivable_mx g t 1 -> derivable_mx (fun x => f x *m g x) t 1.
Proof.
move=> Hf Hg a b. evar (f1 : 'I_k -> R^o -> R^o).
rewrite (_ : (fun x => _) = (\sum_i f1 i)); last first.
  rewrite funeqE => t'; rewrite mxE fct_sumE; apply: eq_bigr => k0 _.
  rewrite /f1; reflexivity.
rewrite {}/f1; apply derivable_sum => k0.
evar (f1 : R^o -> R^o). evar (f2 : R^o -> R^o).
rewrite (_ : (fun t' => _) = f1 * f2); last first.
  rewrite funeqE => t'; rewrite -[RHS]/(f1 t' * f2 t') /f1 /f2; reflexivity.
rewrite {}/f1 {}/f2; exact: derivableM.
Qed.

End derive_mx_R.

Section row_belast.

Definition row_belast {R : ringType} n (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \row_(i < n) (v ``_ (widen_ord (leqnSn n) i)).

Lemma row_belast_last (R : ringType) n (r : 'rV[R]_n.+1) H :
  r = castmx (erefl, H) (row_mx (row_belast r) (r ``_ ord_max)%:M).
Proof.
apply/rowP => i; rewrite castmxE mxE.
case: fintype.splitP => /= [j Hj|[] [] //= ? ni]; rewrite mxE /=.
  congr (_ ``_ _); exact: val_inj.
rewrite mulr1n; congr (_ ``_ _); apply val_inj; by rewrite /= ni addn0.
Qed.

Lemma derivable_row_belast n (u : R^o -> 'rV[R^o]_n.+1) (t : R^o) (v : R^o):
  derivable_mx u t v -> derivable_mx (fun x => row_belast (u x)) t v.
Proof.
move=> H i j; move: (H ord0 (widen_ord (leqnSn n) j)) => {H}.
set f := fun _ => _. set g := fun _ => _.
by rewrite (_ : f = g) // funeqE => x; rewrite /f /g mxE.
Qed.

Lemma dotmul_belast {R : rcfType} n (u : 'rV[R]_n.+1) (v1 : 'rV[R]_n) v2 H :
  u *d castmx (erefl 1%nat, H) (row_mx v1 v2) =
    u *d castmx (erefl 1%nat, H) (row_mx v1 0%:M) +
    u *d castmx (erefl 1%nat, H) (row_mx 0 v2).
Proof.
rewrite -dotmulDr; congr dotmul; apply/matrixP => i j; rewrite !(castmxE,mxE) /=.
case: fintype.splitP => [k /= jk|[] [] // ? /= jn]; by rewrite !(mxE,addr0,add0r,mul0rn).
Qed.

Lemma derive1mx_dotmul_belast n (u v : R^o -> 'rV[R^o]_n.+1) t :
  let u' x := row_belast (u x) in let v' x := row_belast (v x) in
  u' t *d derive1mx v' t + (u t)``_ord_max *: derive (fun x => (v x)``_ord_max) t 1 =
  u t *d derive1mx v t.
Proof.
move=> u' v'.
rewrite (row_belast_last (derive1mx v t)) ?addn1 // => ?.
rewrite dotmul_belast; congr (_ + _).
  rewrite 2!dotmulE [in RHS]big_ord_recr /=.
  rewrite castmxE mxE /=; case: fintype.splitP => [j /= /eqP/negPn|j _].
    by rewrite (gtn_eqF (ltn_ord j)).
  rewrite !mxE (_ : _ == _); last by apply/eqP/val_inj => /=; move: j => [[] ?].
  rewrite mulr0 addr0; apply/eq_bigr => i _; rewrite castmxE !mxE; congr (_ * _).
  case: fintype.splitP => [k /= ik|[] [] //= ?]; rewrite !mxE.
    f_equal.
    rewrite funeqE => x; rewrite /v' !mxE; congr ((v _) _ _); by apply/val_inj.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
apply/esym.
rewrite dotmulE big_ord_recr /= (eq_bigr (fun=> 0)); last first.
  move=> i _.
  rewrite !castmxE !mxE; case: fintype.splitP => [j /= ij| [] [] //= ?].
    by rewrite mxE mulr0.
  rewrite addn0 => /eqP/negPn; by rewrite (ltn_eqF (ltn_ord i)).
rewrite sumr_const mul0rn add0r castmxE /=; congr (_ * _); rewrite !mxE.
case: fintype.splitP => [j /= /eqP/negPn | [] [] //= ? Hn].
  by rewrite (gtn_eqF (ltn_ord j)).
by rewrite mxE derive1E (_ : _ == _).
Qed.

End row_belast.

(* TODO: could be derived from more generic lemmas about bilinearity in derive.v? *)
Section product_rules.

Lemma derive1mx_dotmul n (u v : R^o -> 'rV[R^o]_n) (t : R^o) :
  derivable_mx u t 1 -> derivable_mx v t 1 ->
  derive1 (fun x => u x *d v x : R^o) t =
  derive1mx u t *d v t + u t *d derive1mx v t.
Proof.
move=> U V.
evar (f : R -> R); rewrite (_ : (fun x : R => _) = f); last first.
  rewrite funeqE => x /=; exact: dotmulE.
rewrite derive1E {}/f.
set f := fun i : 'I__ => fun x => ((u x) ``_ i * (v x) ``_ i).
rewrite (_ : (fun _ : R => _) = \sum_(k < _) f k); last first.
  by rewrite funeqE => x; rewrite /f /= fct_sumE.
rewrite derive_sum; last by move=> ?; exact: derivableM (U _ _) (V _ _).
rewrite {}/f.
elim: n u v => [|n IH] u v in U V *.
  rewrite big_ord0 (_ : v t = 0) ?dotmulv0 ?add0r; last by apply/rowP => [[]].
  rewrite (_ : u t = 0) ?dotmul0v //; by apply/rowP => [[]].
rewrite [LHS]big_ord_recr /=.
set u' := fun x => row_belast (u x). set v' := fun x => row_belast (v x).
transitivity (derive1mx u' t *d v' t + u' t *d derive1mx v' t +
    derive (fun x => (u x)``_ord_max * (v x)``_ord_max) t 1).
  rewrite -(IH _ _ (derivable_row_belast U) (derivable_row_belast V)).
  congr (_ + _); apply eq_bigr => i _; congr (derive _ t 1).
  by rewrite funeqE => x; rewrite !mxE.
rewrite (deriveM (U _ _) (V _ _)) /= -!addrA addrC addrA.
rewrite -(addrA (_ + _)) [in RHS]addrC derive1mx_dotmul_belast; congr (_ + _).
by rewrite [in RHS]dotmulC -derive1mx_dotmul_belast addrC dotmulC.
Qed.

Lemma derive1mxM n m p (M : R^o -> 'M[R^o]_(n, m))
  (N : R^o -> 'M[R^o]_(m, p)) (t : R^o) :
  derivable_mx M t 1 -> derivable_mx N t 1 ->
  derive1mx (fun t => M t *m N t) t =
    derive1mx M t *m N t + M t *m (derive1mx N t).
Proof.
move=> HM HN; apply/matrixP => i j; rewrite ![in LHS]mxE.
rewrite (_ : (fun x => _) = fun x => \sum_k (M x) i k * (N x) k j); last first.
  by rewrite funeqE => x; rewrite !mxE.
rewrite (_ : (fun x => _) =
    fun x => (row i (M x)) *d (col j (N x))^T); last first.
  rewrite funeqE => z; rewrite dotmulE; apply eq_bigr => k _.
  by rewrite 3!mxE.
rewrite (derive1mx_dotmul (derivable_mx_row HM) (derivable_mx_col HN)).
rewrite [in RHS]mxE; congr (_  + _); rewrite [in RHS]mxE dotmulE;
  apply/eq_bigr => /= k _; rewrite !mxE; congr (_ * _); congr (derive1 _ t);
  by rewrite funeqE => z; rewrite !mxE.
Qed.

Lemma derive1mx_crossmul (u v : R -> 'rV[R^o]_3) t :
  derivable_mx u t 1 -> derivable_mx v t 1 ->
  derive1mx (fun x => (u x *v v x) : 'rV[R^o]_3) t =
  derive1mx u t *v v t + u t *v derive1mx v t.
Proof.
move=> U V.
evar (f : R -> 'rV[R]_3); rewrite (_ : (fun x : R => _) = f); last first.
  rewrite funeqE => x; exact: crossmulE.
rewrite {}/f {1}/derive1mx; apply/rowP => i; rewrite mxE derive1E.
rewrite (mxE_funeqE (fun x : R^o => _)) /= mxE 2!crossmulE ![in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=];
  rewrite ?derive1E (deriveD (derivableM (U _ _) (V _ _))
    (derivableN (derivableM (U _ _) (V _ _))));
  rewrite (deriveN (derivableM (U _ _) (V _ _))) 2!(deriveM (U _ _) (V _ _));
  rewrite addrCA -!addrA; congr (_ + (_ + _)); by [ rewrite mulrC |
  rewrite opprD addrC; congr (_ + _); rewrite mulrC ].
Qed.

End product_rules.

Section cross_product_matrix.

Lemma coord_continuous {K : absRingType} m n i j :
  continuous (fun M : 'M[K]_(m.+1, n.+1) => M i j).
Proof.
move=> /= M s /= /locallyP; rewrite locally_E => -[e e0 es].
apply/locallyP; rewrite locally_E; exists e => //= N MN; exact/es/MN.
Qed.

Lemma differentiable_coord m n (M : 'M[R]_(m.+1, n.+1)) i j :
  (differentiable M) (fun N : 'M[R]_(m.+1, n.+1) => N i j : R^o).
Proof.
have @f : {linear 'M[R]_(m.+1, n.+1) -> R^o}.
  by exists (fun N : 'M[R]_(_, _) => N i j); eexists; move=> ? ?; rewrite !mxE.
rewrite (_ : (fun _ => _) = f) //; exact/linear_differentiable/coord_continuous.
Qed.

Lemma differential_cross_product (v : 'rV[R]_3) y :
  'd_y (crossmul v) = mx_lin1 \S( v ) :> (_ -> _).
Proof.
rewrite (_ : crossmul v = (fun x => x *m \S( v ))); last first.
  by rewrite funeqE => ?; rewrite -spinE.
rewrite (_ : mulmx^~ \S(v) = mulmxr_linear 1 \S(v)); last by rewrite funeqE.
rewrite diff_lin //= => x.
suff : differentiable x (mulmxr \S(v)) by move/differentiable_continuous.
rewrite (_ : mulmxr \S(v) = (fun z => \sum_i z``_i *: row i \S(v))); last first.
  rewrite funeqE => z; by rewrite -mulmx_sum_row.
set f := fun (i : 'I_3) (z : 'rV_3) => z``_i *: row i \S(v) : 'rV_3.
rewrite (_ : (fun _ => _) = \sum_i f i); last by rewrite funeqE => ?; by rewrite fct_sumE.
apply: differentiable_sum => i.
exact/differentiableZl/differentiable_coord.
Qed.

Lemma differential_cross_product2 (v y : 'rV[R]_3) :
  'd_y (fun x : 'rV[R^o]_3 => x *v v) = -1 \*: mx_lin1 \S( v ) :> (_ -> _).
Proof.
transitivity ('d_y (crossmul (- v))); last first.
  by rewrite differential_cross_product spinN mx_lin1N.
congr diff.
by rewrite funeqE => /= u; rewrite crossmulC crossmulNv.
Qed.

End cross_product_matrix.

Section derivative_of_a_rotation_matrix.

Variable M : R -> 'M[R^o]_3. (* time-varying matrix *)
Hypothesis MO : forall t, M t \is 'O[ [ringType of R] ]_3.
Hypothesis derivable_M : forall t, derivable_mx M t 1.

(* angular velocity matrix *)
Definition ang_vel_mx t := (M t)^T * derive1mx M t.

Lemma ang_vel_mx_is_so t : ang_vel_mx t \is 'so[ [ringType of R] ]_3.
Proof.
have : (fun t => (M t)^T * M t) = cst 1.
  rewrite funeqE => x; by rewrite -orthogonal_inv // mulVr // orthogonal_unit.
move/(congr1 (fun f => derive1mx f t)); rewrite derive1mx_cst -[cst 0 _]/(0).
rewrite derive1mxM // -?trmx_derivable // derive1mx_tr.
move=> /eqP; rewrite addr_eq0 => /eqP H.
by rewrite antiE /ang_vel_mx trmx_mul trmxK H opprK.
Qed.

(* [sciavicco] eqn 3.7 *)
Lemma derive_rot_skew (t : R) : derive1mx M t = M t * ang_vel_mx t.
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

Lemma derive1mx_angular_velocity (p' : 'rV[R^o]_3 (* constant vector *)) :
  let p := fun t => p' *m (M t) in
  forall t, derive1mx p t = unspin (ang_vel_mx t) *v (p' *m M t).
Proof.
move=> p t; rewrite /p derive1mxM; last first.
  exact: derivable_M.
  rewrite /derivable_mx => i j; exact: ex_derive.
rewrite derive1mx_cst mul0mx add0r derive_rot_skew mulmxA.
by rewrite -{1}(unspinK (ang_vel_mx_is_so t)) spinE.
Qed.

Require Import angle.

Lemma derivative_Rx (a : R -> angle.angle [rcfType of R^o]) t :
  derive1mx (fun x => Rx (a x)) t = \S( row3 1 0 0 ) *m Rx (a t).
Admitted.

End derivative_of_a_rotation_matrix.

Require Import frame.

Section about_free_vectors.

Variable T : ringType.

Definition FreeVect_add (F : TFrame.t T) (a b : FreeVect.t F) : FreeVect.t F :=
  <| FreeVect.v a + FreeVect.v b $ F |>.

Local Notation "a +fv b" := (FreeVect_add a b) (at level 39).

Lemma fv_eq a b : a = b -> forall F : Frame.t T, <| a $ F |> = <| b $ F |>.
Proof. by move=> ->. Qed.

End about_free_vectors.

Notation "a +fv b" := (FreeVect_add a b) (at level 39).

Module BoundVect. (* i.e., point of application prescribed *)
Section bound_vector.
Variable T : ringType.
Record t (F : TFrame.t T) := mk { endp : 'rV[T]_3 }.
Definition startp F (v : t F) : 'rV[T]_3 := TFrame.o F.
End bound_vector.
End BoundVect.
Coercion boundvectendp (T : ringType) (F : TFrame.t T) (v : BoundVect.t F) :=
  BoundVect.endp v.

Reserved Notation "a +bf b" (at level 39).
Reserved Notation "a -b b" (at level 39).

Section about_bound_vectors.

Variables (T : ringType) (F : TFrame.t T).

Definition FreeVect_of_Bound (p : BoundVect.t F) : FreeVect.t F :=
  <| BoundVect.endp p $ F |>.

Definition BoundVect_add (a b : BoundVect.t F) : BoundVect.t F :=
  BoundVect.mk F (BoundVect.endp a + BoundVect.endp b).

Definition BoundFree_add (a : BoundVect.t F) (b : FreeVect.t F) : BoundVect.t F :=
  BoundVect.mk F (BoundVect.endp a + FreeVect.v b).

Local Notation "a +bf b" := (BoundFree_add a b).

Lemma BoundFree_addA (a : BoundVect.t F) (b c : FreeVect.t F) :
  a +bf b +bf c = a +bf (b +fv c).
Proof. by rewrite /BoundFree_add /= addrA. Qed.

Definition BoundVect_sub (F : TFrame.t T) (a b : BoundVect.t F) : FreeVect.t F :=
  <| BoundVect.endp a - BoundVect.endp b $ F |>.

Local Notation "a -b b" := (BoundVect_sub a b).

End about_bound_vectors.

Notation "a +bf b" := (BoundFree_add a b).
Notation "a -b b" := (BoundVect_sub a b).

Module RFrame.
Section rframe.
Variable T : ringType.
Record t (F : TFrame.t T) := mk {
  o : BoundVect.t F ;
  i : FreeVect.t F ;
  j : FreeVect.t F ;
  k : FreeVect.t F ;
  f : TFrame.t T ;
  _ : BoundVect.endp o = TFrame.o f ;
  _ : FreeVect.v i = (f|,@Ordinal 3 0 isT) ;
  _ : FreeVect.v j = (f|,@Ordinal 3 1 isT) ;
  _ : FreeVect.v k = (f|,@Ordinal 3 2 isT) ;
}.
End rframe.
End RFrame.

Coercion tframe_of_rframe (R : ringType) (F : TFrame.t R) (f : RFrame.t F) : TFrame.t R :=
  RFrame.f f.

(* TODO *)
Axiom derivable_mx_trame_o :
  forall (F : TFrame.t [ringType of R^o]) (G : R -> RFrame.t F) t,
  derivable_mx G t 1 ->
  derivable_mx (@TFrame.o [ringType of R^o] \o G) t 1.

Section motion_lemmas.

Variables (F : TFrame.t [ringType of R^o]).

Lemma derive1mx_BoundFree_add (Q : R -> BoundVect.t F) (Z : R -> FreeVect.t F) t :
  derivable_mx (fun x => BoundVect.endp (Q x)) t 1 ->
  derivable_mx (fun x => FreeVect.v (Z x)) t 1 ->
  derive1mx (fun x => BoundVect.endp (Q x +bf Z x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
    derive1mx (fun x => FreeVect.v (Z x)) t.
Proof.
move=> H H'.
rewrite (_ : (fun x : R => _) = (fun x : R => BoundVect.endp (Q x) +
  (FreeVect.v (Z x)))); last by rewrite funeqE.
rewrite derive1mxD.
- by [].
- exact: H.
- exact H'.
Qed.

Lemma derivable_mx_FromTo (G : R -> RFrame.t F) t :
  derivable_mx G t 1 -> derivable_mx (fun x => (G x) _R^ F) t 1.
Proof.
move=> H a b.
rewrite (_ : (fun x => _) = (fun x => row a (G x) *d row b F)); last first.
  rewrite funeqE => t'; by rewrite !mxE.
evar (f : 'I_3 -> R^o -> R^o).
rewrite (_ : (fun x => _) = \sum_i f i); last first.
  rewrite funeqE => t'; rewrite dotmulE fct_sumE; apply: eq_bigr => /= i _.
  rewrite !mxE /f; reflexivity.
rewrite {}/f.
apply: derivable_sum => i.
apply derivableM; [ exact: H| exact: ex_derive].
Qed.

Lemma derivable_mx_FromTo' (G : R -> RFrame.t F) t :
  derivable_mx G t 1 -> derivable_mx (fun x => F _R^ (G x)) t 1.
Proof.
move=> H.
rewrite trmx_derivable (_ : (fun x => _) = (fun x => (G x) _R^ F)).
  exact: derivable_mx_FromTo.
rewrite funeqE => x; by rewrite trmx_FromTo.
Qed.

End motion_lemmas.

(* appendix B.1 *)
Section kinematics.

Variable F : TFrame.t [ringType of R^o]. (* fixed frame *)
Variable G : R -> RFrame.t F. (* time-varying frame (origin and basis in F) *)
Hypothesis derivable_G : forall t, derivable_mx G t 1.
Variable P' : forall t, BoundVect.t (G t). (* point with coordinates in G *)
Hypothesis P'_fixed_in_G : forall t, BoundVect.endp (P' t) = BoundVect.endp (P' 0).

(* motion of P w.r.t. the fixed frame F *)
Definition P (t : R) : BoundVect.t F :=
  RFrame.o (G t) +bf to_coord F (FreeVect_of_Bound (P' t)).

Variable Q' : forall t, BoundVect.t (G t).
Hypothesis Q'_fixed_in_G : forall t, BoundVect.endp (Q' t) = BoundVect.endp (Q' 0).

Definition Q (t : R) : BoundVect.t F :=
  RFrame.o (G t) +bf to_coord F (FreeVect_of_Bound (Q' t)).

Lemma p_p_Q (t : R) : P t = Q t +bf to_coord F (P' t -b Q' t).
Proof.
rewrite /Q.
rewrite BoundFree_addA.
rewrite /P.
congr (_ +bf _).
apply fv_eq => /=.
rewrite -mulmxDl.
congr (_ *m _).
rewrite addrC.
apply/eqP.
rewrite -subr_eq.
by [].
Qed.

Lemma derivable_mx_Q t : derivable_mx (fun x => BoundVect.endp (Q x)) t 1.
Proof.
rewrite /Q /=; apply derivable_mxD.
  suff H : derivable_mx (fun x : R => TFrame.o (G x)) t 1.
    move=> a b; move: (H a b).
    rewrite (_ : (fun x : R^o => (TFrame.o (G x)) a b) =
      (fun x : R^o => (BoundVect.endp (RFrame.o (G x))) a b)) // funeqE => x.
    destruct (G x) => /=; by rewrite e.
  exact: derivable_mx_trame_o.
apply derivable_mxM.
  rewrite (_ : (fun x => _) = (fun _ => BoundVect.endp (Q' 0))); last first.
    rewrite funeqE => x; by rewrite Q'_fixed_in_G.
  move=> a b; exact: ex_derive.
exact: derivable_mx_FromTo.
Qed.

Let Rot := fun t => (G t) _R^ F.

(* angular velocity *)
Definition ang_vel M := fun t => unspin (ang_vel_mx M t).

Lemma velocity_composition_rule (t : R) :
  derive1mx (fun x => BoundVect.endp (P x)) t =
  derive1mx (fun x => BoundVect.endp (Q x)) t +
  ang_vel Rot t *v (FreeVect.v (P t -b Q t)).
Proof.
rewrite {1}(_ : P = fun t => Q t +bf to_coord F (P' t -b Q' t)); last first.
  by rewrite funeqE => t'; rewrite p_p_Q.
rewrite (derive1mx_BoundFree_add (@derivable_mx_Q t)); last first.
  apply: derivable_mxM.
  rewrite (_ : (fun x : R^o => _) = (fun x : R^o => (FreeVect.v (P' 0 -b Q' 0)))); last first.
  rewrite funeqE => x.
  by rewrite /= P'_fixed_in_G Q'_fixed_in_G.
  move=> a b; exact: ex_derive.
  exact: derivable_mx_FromTo.
congr (_ + _).
rewrite [in LHS]/to_coord [in LHS]/= derive1mxM; last 2 first.
  rewrite {1}(_ : (fun x  => _) = (fun x  => BoundVect.endp (P' 0) - BoundVect.endp (Q' 0))); last first.
    by rewrite funeqE => ?; rewrite P'_fixed_in_G Q'_fixed_in_G.
  move=> a b.
  exact: ex_derive.
  exact: derivable_mx_FromTo.
rewrite (_ : (fun t0 => _) = (cst (BoundVect.endp (P' 0) - BoundVect.endp (Q' 0)))); last first.
  by rewrite funeqE => x; rewrite P'_fixed_in_G Q'_fixed_in_G.
rewrite derive1mx_cst mul0mx add0r.
rewrite -spinE.
rewrite unspinK; last first.
  rewrite /ang_vel_mx.
  rewrite derive_rot_skew; last 2 first.
  - move=> t'; by rewrite FromTo_is_O.
  - move=> t'; exact: derivable_mx_FromTo.
  - rewrite mulrA -mulmxE orthogonal_tr_mul ?FromTo_is_O // mul1mx ang_vel_mx_is_so.
    + by [].
    + move=> t'; by rewrite FromTo_is_O.
    + move=> t'; exact: derivable_mx_FromTo.
rewrite /ang_vel_mx mulmxA; congr (_ *m _).
rewrite /P /Q /= opprD addrACA subrr add0r mulmxBl -!mulmxA.
by rewrite orthogonal_mul_tr ?FromTo_is_O // !mulmx1.
Qed.

Lemma B5 (t : R) : derive1mx Rot t = Rot t * \S( unspin (ang_vel_mx Rot t)).
Proof.
rewrite derive_rot_skew; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'. exact: derivable_mx_FromTo.
rewrite unspinK // ang_vel_mx_is_so; last 2 first.
  move=> t'; by rewrite FromTo_is_O.
  move=> t'. exact: derivable_mx_FromTo.
by [].
Qed.

End kinematics.

(* NB: see also Section tangent_frames in rigid.v *)
Section tangent_vectors.
(* or "bound vectors":  *)

Variable R : realType.
Let vector := 'rV[R]_3.
Let point := 'rV[R]_3.
Implicit Types p : point.

(* tangent vector *)
Record tvec p := TVec {tvec_field :> vector}.
Definition vtvec p (v : tvec p) := let: TVec v := v in v.

Local Notation "p .-vec" := (tvec p) (at level 5).
Local Notation "u :@ p" := (TVec p u) (at level 11).

Definition addt (p : point) (u : p.-vec) (v : vector) : p.-vec :=
  TVec p (tvec_field u + v).

Local Notation "p +@ u" := (addt p u) (at level 41).

End tangent_vectors.

Coercion vtvec_field_coercion := vtvec.
Notation "p .-vec" := (tvec p) (at level 5).
Notation "u :@ p" := (TVec p u) (at level 11).
Notation "p +@ u" := (addt p u) (at level 41).

(* [sciavicco] eqn 3.9 *)
Lemma rot_skew {T : rcfType} (M : 'M[T]_3) (w : 'rV[T]_3) :
  M \is 'O[T]_3 ->
  M * \S( w ) * M^T = \S( w *m M).
Proof.
move=> MO.
apply/matrix3P/and9P; split.
Abort.
