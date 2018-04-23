From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype tuple finfun bigop finset ssralg matrix.
From mathcomp Require Import interval ssrnum.

Require Import Reals.
From mathcomp.analysis Require Import boolp reals Rstruct Rbar set posnum.
From mathcomp.analysis Require Import topology hierarchy landau forms derive.

Require Import ssr_ext euclidean3 rot skew.

(* WIP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section dotmul_bilinear.

Variables (R : rcfType) (n : nat).

Definition dotmul_rev (v u : 'rV[R]_n) := u *d v.
Canonical rev_dotmul := @RevOp _ _ _ dotmul_rev (@dotmul R n)
  (fun _ _ => erefl).

Lemma dotmul_is_linear u : GRing.linear (dotmul u : 'rV[R]_n -> R^o).
Proof. move=> /= k v w; by rewrite dotmulDr dotmulvZ. Qed.
Canonical dotmul_linear x := Linear (dotmul_is_linear x).

Lemma dotmul_rev_is_linear v : GRing.linear (dotmul_rev v : 'rV[R]_n -> R^o).
Proof. move=> /= k u w; by rewrite /dotmul_rev dotmulDl dotmulZv. Qed.
Canonical dotmul_rev_linear v := Linear (dotmul_rev_is_linear v).

Canonical dotmul_bilinear := [bilinear of (@dotmul R n)].

End dotmul_bilinear.

Section crossmul_bilinear.

Variables (R : rcfType).

Definition crossmul_rev (v u : 'rV[R]_3) := u *v v.
Canonical rev_crossmul := @RevOp _ _ _ crossmul_rev (@crossmul R)
  (fun _ _ => erefl).

Lemma crossmul_is_linear u : GRing.linear (crossmul u : 'rV[R]_3 -> 'rV[R]_3).
Proof. move=> /= k v w; by rewrite crossmulDr crossmulvZ. Qed.
Canonical crossmul_linear x := Linear (crossmul_is_linear x).

Lemma crossmul_rev_is_linear v : GRing.linear (crossmul_rev v : 'rV[R]_3 -> 'rV[R]_3).
Proof. move=> /= k u w; by rewrite /crossmul_rev crossmulDl crossmulZv. Qed.
Canonical crossmul_rev_linear v := Linear (crossmul_rev_is_linear v).

Canonical crossmul_bilinear := [bilinear of (@crossmul R)].

End crossmul_bilinear.

Section tmp.

Variable (V W : normedModType R).

Definition derive1mx n m (M : R -> 'M[W]_(n, m)) := fun t =>
  \matrix_(i < n, j < m) ((fun x => M x i j)^`() t : W).

Lemma derive1mx_cst n m (M : 'M[W]_(n, m)) : derive1mx (cst M) = cst 0.
Proof.
rewrite /derive1mx funeqE => t; apply/matrixP => i j; rewrite !mxE.
by rewrite derive1E (_ : (fun _ => _) = cst (M i j)) // derive_val.
Qed.

Lemma derive1mx_tr n (M : R -> 'M[W]_(n, n)) t :
  derive1mx (fun x => (M x)^T) t = (derive1mx M t)^T.
Proof.
apply/matrixP => i j; rewrite !mxE.
by rewrite (_ : (fun _ => _) = (fun t => M t j i)) // funeqE => ?; rewrite mxE.
Qed.

Lemma derive_mx n m (f : V -> 'I_n -> 'I_m -> W) i j (t : V) v :
  'D_v[fun x => (\matrix_(i < n, j < m) (f x i j)) i j] t =
    (\matrix_(i < n, j < m) ('D_v[fun x => f x i j] t : W)) i j.
Proof.
by rewrite (_ : (fun x => _) = (fun x => f x i j)) ?mxE // funeqE => ?; rewrite mxE.
Qed.

Definition derivable_mx m n (M : R -> 'M[W]_(m, n)) (t : R^o) v :=
  forall i j, derivable (fun x : R^o => (M x) i j) t v.

Lemma trmx_derivable m n (M : R^o -> 'M[W]_(m, n)) (t : R^o) v :
  derivable_mx M t v -> derivable_mx (fun t0 : R => (M t0)^T) t v.
Proof.
move=> H i j.
by rewrite (_ : (fun _ => _) = (fun x => M x j i)) // funeqE => z; rewrite mxE.
Qed.

Lemma derivable_mx_row n m (M : R^o -> 'M[W]_(n, m)) (t : R^o) i :
  derivable_mx M t 1 -> derivable_mx (fun x : R => \row_z (M x) i z) t 1.
Proof.
move=> H a b.
by rewrite (_ : (fun _ => _) = (fun x => (M x) i b)) // funeqE => z; rewrite mxE.
Qed.

Lemma derivable_mx_row' n m (M : R -> 'M[W]_(n, m)) (t : R^o) i :
  derivable_mx M t 1 -> derivable_mx (fun x : R => \row_z (M x) z i) t 1.
Proof.
move=> H a b.
by rewrite (_ : (fun _ => _) = (fun x : R^o => (M x) b i)) // funeqE => z; rewrite mxE.
Qed.

End tmp.

Section row_belast.

Definition row_belast {R : ringType} n (v : 'rV[R]_n.+1) : 'rV[R]_n :=
  \row_(i < n) (v ``_ (widen_ord (leqnSn n) i)).

Lemma row_belast_last {R : ringType} n (r : 'rV[R]_n.+1) H :
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
  u' t *d derive1mx v' t + (u t)``_ord_max *: 'D_1[fun x => (v x)``_ord_max] t =
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
  (fun x => u x *d v x : R^o)^`() t =
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
    'D_1[fun x => (u x)``_ord_max * (v x)``_ord_max] t).
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
    fun x => (\row_(z < _) (M x i) z) *d (\row_(z < _) (N x z j))); last first.
  rewrite funeqE => z; rewrite dotmulE; apply eq_bigr => k _; by rewrite 2!mxE.
rewrite (derive1mx_dotmul (derivable_mx_row HM) (derivable_mx_row' HN)).
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
rewrite derive_mx /= mxE 2!crossmulE ![in RHS]mxE /=.
case: ifPn => [/eqP _|/ifnot0P/orP[]/eqP -> /=];
  rewrite ?derive1E (deriveD (derivableM (U _ _) (V _ _))
    (derivableN (derivableM (U _ _) (V _ _))));
  rewrite (deriveN (derivableM (U _ _) (V _ _))) 2!(deriveM (U _ _) (V _ _));
  rewrite addrCA -!addrA; congr (_ + (_ + _)); by [ rewrite mulrC |
  rewrite opprD addrC; congr (_ + _); rewrite mulrC ].
Qed.

End product_rules.

Section derivative_of_a_rotation_matrix.

Variable M : R -> 'M[R^o]_3. (* time-varying matrix *)
Hypothesis MSO : forall t, M t \is 'SO[real_realType]_3.
Hypothesis derivable_M : forall t, derivable_mx M t 1.

Definition s t := derive1mx M t * (M t)^T.

Lemma sso t : s t \is 'so[real_realType]_3.
Proof.
rewrite antiE -subr_eq0 opprK; apply/eqP; rewrite /s trmx_mul trmxK mulmxE.
have : (fun t => M t * (M t)^T) = cst 1.
  rewrite funeqE => x.
  by move: (MSO x); rewrite rotationE orthogonalE => /andP[/eqP].
move/(congr1 (fun x => derive1mx x t)); rewrite derive1mx_cst -[cst 0 _]/(0).
rewrite derive1mxM // ?derive1mx_tr //; exact/trmx_derivable/derivable_M.
Qed.

(* [sciavicco] eqn 3.7 *)
Lemma derive_rot_skew (t : R) : derive1mx M t = s t * M t.
Proof.
move: (sso t); rewrite antiE -subr_eq0 opprK => /eqP.
rewrite {1 2}/s trmx_mul trmxK => /(congr1 (fun x => x * M t)).
rewrite mul0r mulrDl -{1}mulrA -{1}(rotation_inv (MSO t)).
rewrite mulVr ?mulr1 ?unitmxE ?rotation_det // ?unitr1 //.
move/eqP; rewrite addr_eq0 => /eqP ->.
move: (sso t); rewrite antiE => /eqP ->.
by rewrite /s trmx_mul trmxK mulNr.
Qed.

End derivative_of_a_rotation_matrix.

Require Import frame.

Section about_free_vectors.

Variable T : rcfType.

Definition FreeVect_add (F : TFrame.t T) (a b : FreeVect.t F) : FreeVect.t F :=
  <| FreeVect.v a + FreeVect.v b $ F |>.

Local Notation "a +fv b" := (FreeVect_add a b) (at level 39).

Lemma fv_eq a b : a = b -> forall F : Frame.t T, <| a $ F |> = <| b $ F |>.
Proof. by move=> ->. Qed.

End about_free_vectors.

Notation "a +fv b" := (FreeVect_add a b) (at level 39).

Module BoundVect.
Section bound_vector.
Variable T : rcfType.
Record t (F : TFrame.t T) := mk { endp : 'rV[T]_3 }.
End bound_vector.
End BoundVect.

Section about_bound_vectors.

Variable T : rcfType.
Variable F : TFrame.t T.

Definition startp (_ : BoundVect.t F) : 'rV[T]_3 :=
  TFrame.o F.

Definition FreeVect_of_Bound (p : BoundVect.t F) : FreeVect.t F :=
  <| BoundVect.endp p $ F |>.

Definition BoundVect_add (a b : BoundVect.t F) : BoundVect.t F :=
  BoundVect.mk F (BoundVect.endp a + BoundVect.endp b).

Definition BoundFree_add (a : BoundVect.t F) (b : FreeVect.t F) : BoundVect.t F :=
  BoundVect.mk F (BoundVect.endp a + FreeVect.v b).

Local Notation "a # b" := (BoundFree_add a b) (at level 39).

Lemma BoundFree_addA (a : BoundVect.t F) (b c : FreeVect.t F) :
  a # b # c = a # (b +fv c).
Proof. by rewrite /BoundFree_add /= addrA. Qed.

Definition Rsub (F : TFrame.t T) (a b : BoundVect.t F) : FreeVect.t F :=
  <| BoundVect.endp a - BoundVect.endp b $ F |>.

Local Notation "a (-) b" := (Rsub a b) (at level 39).

(*Definition derive1bv (p : R -> BoundVect.t F) : R -> BoundVect.t F :=
  fun t => BoundVect.mk F (derive1mx (fun t => BoundVect.endp (p t)) t).*)

End about_bound_vectors.

Notation "a # b" := (BoundFree_add a b) (at level 39).
Notation "a (-) b" := (Rsub a b) (at level 39).

Module RFrame.
Section rframe.
Variable T : rcfType.
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

Coercion tframe_of_rframe (R : rcfType) (F : TFrame.t R) (f : RFrame.t F) : TFrame.t R :=
  RFrame.f f.

Section motion.

Variable T : rcfType.

Variable F : TFrame.t T. (* fixed frame *)
Variable G : R -> RFrame.t F. (* time-varying frame (origin and basis in F) *)
Variable P' : forall t, BoundVect.t (G t). (* point with coordinates in G *)
Hypothesis P'_fixed_in_G : forall t, BoundVect.endp (P' t) = BoundVect.endp (P' 0).

Definition P (t : R) : BoundVect.t F :=
  RFrame.o (G t) # to_coord F (FreeVect_of_Bound (P' t)).

Variable Q' : forall t, BoundVect.t (RFrame.f (G t)).
Hypothesis Q'_fixed_in_G : forall t, BoundVect.endp (Q' t) = BoundVect.endp (Q' 0).

Definition Q (t : R) : BoundVect.t F :=
  RFrame.o (G t) # to_coord F (FreeVect_of_Bound (Q' t)).

Lemma p_p_Q (t : R) : P t = Q t # to_coord F (P' t (-) Q' t).
Proof.
rewrite /Q.
rewrite BoundFree_addA.
rewrite /P.
congr (_ # _).
apply fv_eq => /=.
rewrite -mulmxDl.
congr (_ *m _).
rewrite addrC.
apply/eqP.
rewrite -subr_eq.
done.
Qed.

(*Variable angular_velocity : R -> 'rV[T]_3.

Lemma velocity_composition_rule (t : R) :
  derive1mx P t = derive1mx Q t + angular_velocity t *v (P t - Q t).*)

End motion.

Section cross_product_matrix.

Variable v : 'rV[R^o]_3.
Let vector := [normedModType R of 'rV[R]_3].
Let f : {linear vector -> vector} := crossmul_linear v.
Let g : {bilinear vector -> vector -> vector } := @crossmul_bilinear _.

Lemma continuous_crossmul : continuous (fun p => g p.1 p.2).
Proof.
move=> x.
Admitted.

Lemma diff_crossmul a (h : vector * vector) :
  'd_a (fun x => g x.1 x.2) h = a.1 *v h.2 + h.1 *v a.2.
Proof. rewrite diff_bilin //; exact: continuous_crossmul. Qed.

Lemma test x : lin1_mx ('d_x (fun x => v *v x)) = \S( v ).
Proof.
Abort.

End cross_product_matrix.

(* NB: see also Section tangent_frames in rigid.v *)
Section tangent_vectors.
(* or "bound vectors": point of application prescribed *)

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
Lemma rot_skew (M : 'M[R]_3) (w : 'rV[R]_3) :
  M * \S( w ) * M^T = \S( w *m M).
Proof.
Abort.
