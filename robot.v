Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp
Require Import complex.
From mathcomp.fingroup
Require Import fingroup perm.

(*
 OUTLINE:
 1. section extra
 2. section dot_product
 3. section triple_prod_mat
    section crossmul 
    (definition of "normal" also) 
    (sample lemma: double_crossmul)
 4. section O_3[R]_3 and SO_3[R]
    (sample lemma: Euler's theorem)
 5. section norm 
    (sample lemma: multiplication by O_3[R] preserves norm)
    (NB: some specialized lemmas for dimension 3 (Section norm3))
 6. section angle
    (addition, scalar multiplication, half-angle)
    (definitions of cos, sin, tan, acos, asin, and atan, and various properties) 
    definition of vec_angle (restricted to [0,pi])
    (sample lemma: multiplication by a O_3[R] matrix preserves vec_angle)
 7. section colinear
    (simple definition using crossmul, but seemed clearer to me to have a dedicated definition)
 8. section normalize
    section axial_normal_decomposition.
    (easy definitions to construct frames out of already available points/vectors)
 9. module orthonormal_frame 
    definition of orthonormal frames (including orientation)
 10. module about the canonical frame (1,0,0),(0,1,0),(0,0,1)
 11. definition of the mapping from one frame to another 
     FromTo.mkT
 12. section triad 
    (construction of a frame out of three non-colinear points)
 13. section transformation_given_three_points 
    (construction d'une transformation (rotation + translation) etant donnes 
    trois points de depart et leurs positions d'arrivee)
    sample lemma: the rotation obtained behaves like a change of coordinates from left to right
 14. definition of rotations w.r.t. axis
     definition of the Rx,Ry,Rz rotations.
     sample lemma: all rotations around an axis of angle a have trace "1 + 2 * cos a"
 15. section homogeneous_transformation
 16. section isometry_def 
     (contains the definition of central isometries)
 17. section sign_of_isometry (n = 3)
     (contains the definition of direct isometries)
 18. section tangent vectors 
 19. section derivative maps of isometries
     definition of what it means to preserve the cross-product by a transformation
     (sample lemma: preservation of the cross-product by derivative maps)
 20. section rigid_transformation_is_homogenous_transformation
     (a direct isometry (i.e., cross-product preserving) can be expressed in homogeneous coordinates)
     (NB: converse in progress (?))
 21. section kinematics chains
 22. section symmetric/antisymmetry/skew (properties of skew matrices)
     (sample lemma: eigenvalues of skew matrices)
     Cayley transformation
     definition of antip_vec and proof that this vector is stable by rotation (like the axis)     
 23. section exponential_map_rot
     specialized exponential map
     (sample lemmas: inverse of the exponential map,
       exponential map of a skew matrix is a rotation)
     (Rodrigues formula: 
       u * e^(phi,w) can be expressed using a linear combination of vectors
         u, (u *d w)w, u *v w)      
 24. section exponential_coordinates_rotation
     sample lemmas:
       e^(phi,w) is a rotation of phi around w
       any rotation matrix M around an axis has angle acos (tr M - 1)/2
       any rotation matrix M around an axis has axis antip_vec
     (sample lemmas: specialized exponential map <-> Rodrigues' formula)
     (NB: in progress)
 25. section exponential_map 
     tentative definition of e^M (as a series up to k)
 26. section exponential_coordinates_rigid
     tentative definition of a twist
     (NB: in progress)
 27. section quaternion 
     definition of quaternions
     definition of addition, negation -> quaternions form a zmodtype
     definition of multiplication -> quaternions form a ring
     definition of scaling -> quaternions form a lmodtype
     definition of inverse -> quaternions form a unitringtype
     definition of conjugate, norm
     definition of unit quaternions
     definition of rotation using unit quaternions
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Ltac simp_ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=].
Ltac simpr := rewrite ?(mulr0,mul0r,mul1r,mulr1,addr0,add0r).

Ltac simp := rewrite ?(Monoid.simpm,mulNr,mulrN,opprK,oppr0).

Section extra.

Lemma opp_self {R : rcfType} n (u : 'rV[R]_n) : u = - u -> u = 0.
Proof.
move/eqP.
by rewrite -subr_eq0 opprK -mulr2n -scaler_nat scaler_eq0 pnatr_eq0 /= => /eqP.
Qed.

Lemma row_mx_eq0 (M : ringType) (m n1 n2 : nat)
 (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (M : ringType) (m1 m2 n : nat)
 (A1 : 'M[M]_(m1, n)) (A2 : 'M_(m2, n)):
 (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
by rewrite -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx0 tr_col_mx row_mx_eq0.
Qed.

Lemma row_mx_col {R : ringType} (A : 'M[R]_3) : A = row_mx (col 0 A) (row_mx (col 1 A) (col 2%:R A)).
Proof.
rewrite -[in LHS](@hsubmxK _ 3 1 2 A) (_ : lsubmx _ = col 0 A); last first.
  apply/colP => i; rewrite !mxE /= (_ : lshift 2 0 = 0) //.
  by apply val_inj.
rewrite (_ : rsubmx _ = row_mx (col 1 A) (col 2%:R A)) //.
set a := rsubmx _; rewrite -[in LHS](@hsubmxK _ 3 1 1 a); congr row_mx.
  apply/colP => i; rewrite !mxE /= (_ : rshift 1 (lshift 1 0) = 1) //.
  by apply val_inj.
apply/colP => i; rewrite !mxE /= (_ : rshift 1 (rshift 1 0) = 2%:R) //.
by apply val_inj.
Qed.

Lemma rew_condAr (a b c : bool) : a = b && c -> (b -> c = a).
Proof. by case: b. Qed.

Lemma ifnot01 (i : 'I_2) : (i != 0) = (i == 1).
Proof. by case: i => -[] // []. Qed.

Lemma thirdI3 (i j : 'I_3) : i != j -> exists k, (k != i) && (k != j).
Proof.
case: i j => -[i0|[i1|[i2|//]]].
- case=> -[//|[j1 _|[j2 _|//]]]; by [exists 2%:R | exists 1].
- case=> -[j0 _|[//|[j2 _|//]]]; by [exists 2%:R | exists 0].
- case=> -[j0 _|[j1 _|[//|//]]]; by [exists 1 | exists 0].
Qed.

Lemma ifnot0 (i : 'I_3) : (i != 0) = (i == 1) || (i == 2%:R).
Proof. by case: i => -[i0 //| [i1 //| [i2 // | //]]]. Qed.

Lemma ifnot1 (i : 'I_3) : (i != 1) = (i == 0) || (i == 2%:R).
Proof. by case: i => -[i0 //| [i1 //| [i2 // | //]]]. Qed.

Lemma ifnot2 (i : 'I_3) : (i != 2%:R) = (i == 0) || (i == 1).
Proof. by case: i => -[i0 //| [i1 //| [i2 // | //]]]. Qed.

Lemma liftE0 m (i : 'I_m.+2) : fintype.lift i ord0 = (i == 0)%:R.
Proof.
apply/val_inj => /=; rewrite /bump leqn0 addn0; by case: i => // -[].
Qed.

Lemma liftE1 {m} (i : 'I_m.+3) : fintype.lift i 1 = (i <= 1).+1%:R.
Proof.
apply val_inj => /=; case: i => -[/= _| [] //]; by rewrite /bump modn_small.
Qed.

Definition row2 {R : ringType} (a b : R) : 'rV[R]_2 :=
  \row_p [eta \0 with 0 |-> a, 1 |-> b] p.

Definition row3 {R : ringType} (a b c : R) : 'rV[R]_3 :=
  \row_p [eta \0 with 0 |-> a, 1 |-> b, 2%:R |-> c] p.

Lemma row30 {R : ringType} : row3 0 0 0 = 0 :> 'rV[R]_3.
Proof. by apply/rowP => a; rewrite !mxE /=; do 3 case: ifPn => //. Qed.

Lemma row3E {R : ringType} (u : 'rV[R]_3) : 
  u = row3 (u 0 0) 0 0 + row3 0 (u 0 1) 0 + row3 0 0 (u 0 2%:R).
Proof.
apply/rowP => i; rewrite !mxE /=; case: ifPn => [/eqP ->|]; first by simp.
rewrite ifnot0 => /orP [] /eqP -> /=; by simp.
Qed.

Lemma row3_row_mx {R : ringType} (a b c : R) : row3 a b c = row_mx a%:M (row_mx b%:M c%:M).
Proof.
apply/rowP => i.
case/boolP : (i == 0) => [/eqP ->|].
  rewrite !mxE /=.
  case: splitP => // j.
  by rewrite (ord1 j) mxE.
rewrite ifnot0 => /orP [] /eqP ->; rewrite !mxE /=.
  case: splitP => k; first by rewrite (ord1 k).
  case=> k0; rewrite !mxE.
  case: splitP => // j; first by rewrite (ord1 j) mxE.
  by rewrite -k0 (ord1 j).
case: splitP => k; first by rewrite (ord1 k).
case=> k0; rewrite !mxE.
case: splitP => // j; first by rewrite -k0 (ord1 j).
by rewrite (ord1 j) mxE.
Qed.

Lemma sum1E {T : ringType} (f : 'I_1 -> T) : \sum_(i < 1) f i = f 0.
Proof. rewrite (bigD1 ord0) //= big_pred0 ?addr0 //; by case => -[]. Qed.

Lemma sum2E {T : ringType} (f : 'I_2 -> T) : \sum_(i < 2) f i = f 0 + f 1.
Proof. rewrite big_ord_recr /= sum1E; congr (f _ + f _); by apply val_inj. Qed.

Lemma sum3E {T : ringType} (f : 'I_3 -> T) : \sum_(i < 3) f i = f 0 + f 1 + f 2%:R.
Proof. rewrite big_ord_recr //= sum2E; congr (f _ + f _ + f _); by apply val_inj. Qed.

Lemma sum4E {T : ringType} (f : 'I_4 -> T) : \sum_(i < 4) f i = f 0 + f 1 + f 2%:R + f 3%:R.
Proof. rewrite big_ord_recr //= sum3E; congr (f _ + f _ + f _ + f _); by apply val_inj. Qed.

Lemma det_mx11 {T : comRingType }(A : 'M[T]_1) : \det A = A 0 0.
Proof. by rewrite {1}[A]mx11_scalar det_scalar. Qed.

Lemma cofactor_mx22 {T : comRingType} (A : 'M[T]_2) i j :
  cofactor A i j = (-1) ^+ (i + j) * A (i + 1) (j + 1).
Proof.
rewrite /cofactor det_mx11 !mxE; congr (_ * A _ _);
by apply/val_inj; move: i j => [[|[|?]]?] [[|[|?]]?].
Qed.

Lemma det_mx22 {T : comRingType} (A : 'M[T]_2) : \det A = A 0 0 * A 1 1 -  A 0 1 * A 1 0.
Proof.
rewrite (expand_det_row _ ord0) !(mxE, big_ord_recl, big_ord0).
rewrite !(mul0r, mul1r, addr0) !cofactor_mx22 !(mul1r, mulNr, mulrN).
by rewrite !(lift0E, add0r) /= addrr_char2.
Qed.

Lemma cofactor_mx33 {T : comRingType} (A : 'M[T]_3) i j :
  cofactor A i j = (-1) ^+ (i + j) * 
                   (A (i == 0)%:R (j == 0)%:R * A ((i <= 1).+1%:R) ((j <= 1).+1%:R) -
                    A (i == 0)%:R ((j <= 1).+1%:R) * A ((i <= 1).+1%:R) (j == 0)%:R).
Proof.
rewrite /cofactor det_mx22 !mxE; congr (_ * (A _ _ * A _ _ - A _ _ * A _ _));
  by rewrite (liftE0, liftE1).
Qed.

Lemma det_mx33 {T : comRingType } (M : 'M[T]_3) :
  \det M = M 0 0 * (M 1 1 * M 2%:R 2%:R - M 2%:R 1 * M 1 2%:R) +
           M 0 1 * (M 2%:R 0 * M 1 2%:R - M 1 0 * M 2%:R 2%:R) +
           M 0 2%:R * (M 1 0 * M 2%:R 1 - M 2%:R 0 * M 1 1).
Proof.
rewrite (expand_det_row M 0) sum3E -2!addrA; congr (_ * _ + (_ * _ + _ * _)).
  by rewrite cofactor_mx33 /= expr0 mul1r [in X in _ - X]mulrC.
by rewrite cofactor_mx33 /= expr1 mulN1r opprB mulrC.
by rewrite cofactor_mx33 expr2 mulN1r opprK mul1r /= [in X in _ - X]mulrC.
Qed.

Section extra_complex.

Variable R : rcfType.

Lemma opp_conjc (a b : R) : - (a -i* b) = - a +i* b.
Proof. by apply/eqP; rewrite eq_complex /= opprK !eqxx. Qed.

Lemma Re_scale (x : R[i]) (k : R) : k != 0 -> Re (x / k%:C) = (Re x) / k.
Proof. 
move=> k0; case: x => a b /=.
rewrite expr0n /= addr0 mul0r -mulrN opprK mulr0 addr0.
by rewrite expr2 invrM // ?unitfE // (mulrA k) divff // mul1r.
Qed.

Lemma complexZ1 (a b k : R) : (k * a) +i* (k * b) = k%:C * (a +i* b).
Proof. by simpc. Qed.

Lemma complexZ2 (a b k : R) : (k * a) -i* (k * b) = k%:C * (a -i* b).
Proof. by simpc. Qed.

Definition complexZ := (complexZ1, @complexZ2).

End extra_complex.

End extra.

Section dot_product.

Variables (R : rcfType) (n : nat).

Definition dotmul (u v : 'rV[R]_n) : R := (u *m v^T) 0 0.
Local Notation "*d%R" := (@dotmul _).
Local Notation "u *d w" := (dotmul u w) (at level 40).

Lemma dotmulE u v : u *d v = \sum_k u 0 k * v 0 k.
Proof. by rewrite [LHS]mxE; apply: eq_bigr=> i; rewrite mxE. Qed.

Lemma dotmulC u v : u *d v = v *d u.
Proof. by rewrite /dotmul -[_ *m _]trmxK trmx_mul !trmxK mxE. Qed.

Lemma dotmul0v v : 0 *d v = 0.
Proof. by rewrite [LHS]mxE big1 // => i; rewrite mxE mul0r. Qed.

Lemma dotmulv0 v : v *d 0 = 0.
Proof. by rewrite dotmulC dotmul0v. Qed.

Lemma dotmulDr a b c : a *d (b + c) = a *d b + a *d c.
Proof. by rewrite {1}/dotmul linearD /= linearD /= mxE. Qed.

Lemma dotmulDl a b c : (b + c) *d a = b *d a + c *d a.
Proof. by rewrite dotmulC dotmulDr dotmulC (dotmulC c). Qed.

Lemma dotmulD u v : (u + v) *d (u + v) = u *d u + (u *d v) *+ 2 + v *d v.
Proof. rewrite dotmulDr 2!dotmulDl -!addrA; congr (_ + _); by rewrite dotmulC. Qed.

Lemma dotmulvN u v : u *d -v = - (u *d v).
Proof. by rewrite /dotmul linearN /= mulmxN mxE. Qed.

Lemma dotmulNv u v : - u *d v = - (u *d v).
Proof. by rewrite dotmulC dotmulvN dotmulC. Qed.

Lemma dotmulvZ u k v : u *d (k *: v) = k * (u *d v).
Proof. by rewrite /dotmul linearZ /= -scalemxAr mxE. Qed.

Lemma dotmulZv u k v : (k *: u) *d v = k * (u *d v).
Proof. by rewrite dotmulC dotmulvZ dotmulC. Qed.

Lemma le0dotmul u : 0 <= u *d u.
Proof. rewrite dotmulE sumr_ge0 // => i _; by rewrite -expr2 sqr_ge0. Qed.

Lemma dotmulvv0 u : (u *d u == 0) = (u == 0).
Proof.
apply/idP/idP; last by move/eqP ->; rewrite dotmul0v.
rewrite dotmulE psumr_eq0; last by move=> i _; rewrite -expr2 sqr_ge0.
move/allP => H; apply/eqP/rowP => i.
apply/eqP; by rewrite mxE -sqrf_eq0 expr2 -(implyTb ( _ == _)) H.
Qed.

Lemma dotmul_delta_mx u i : u *d delta_mx 0 i = u 0 i.
Proof.
rewrite dotmulE (bigD1 i) //= mxE !eqxx /= mulr1 (eq_bigr (fun=> 0)).
rewrite big_const; elim: #| _ | => /= [|*]; by rewrite ?(addr0,add0r).
by move=> j ji; rewrite !mxE eqxx (negbTE ji) /= mulr0.
Qed.

Lemma dotmul_eq u v : (forall x, u *d x = v *d x) -> u = v.
Proof.
move=> uv.
rewrite (row_sum_delta u) (row_sum_delta v); apply eq_bigr => i _.
move: (uv (delta_mx 0 i)); by rewrite 2!dotmul_delta_mx => ->.
Qed.

Lemma dotmul_trmx u M v : u *d (v *m M) = (u *m M^T) *d v.
Proof. by rewrite /dotmul trmx_mul mulmxA. Qed.

End dot_product.

Notation "*d%R" := (@dotmul _ _) : ring_scope.
Notation "u *d w" := (dotmul u w) (at level 40) : ring_scope.

Section triple_prod_mat.

Variable (T : ringType).

Definition double_prod_mat (u v : 'rV[T]_2) :=
  \matrix_(i < 2) [eta \0 with 0 |-> u, 1 |-> v] i.

(* find a better name *)
Definition triple_prod_mat (u v w : 'rV[T]_3) :=
  \matrix_(i < 3) [eta \0 with 0 |-> u, 1 |-> v, 2%:R |-> w] i.
(*Definition triple_product_mat (u v w : vector) :=
  \matrix_(i < 3) [eta \0 with 0 |-> u, 1 |-> v, 2%:R |-> w] i.*)

Lemma triple_prod_matE a b c : 
  triple_prod_mat a b c = col_mx a (col_mx b c).
Proof.
apply/matrixP => i j; rewrite !mxE /SimplFunDelta /=.
case: ifPn => [i0|].
  case: splitP => [j0|k ik]; first by rewrite (ord1 j0).
  exfalso. move/negP: i0; apply; apply/negP; by rewrite -val_eqE /= ik.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case: splitP => [j0|]; first by rewrite (ord1 j0).
  case => -[|k Hk] //= zerotwo _; rewrite mxE.
  case: splitP => k; by rewrite (ord1 k).
case: splitP => [j0|]; first by rewrite (ord1 j0).
case => -[|[|k Hk]] //= onetwo _; rewrite mxE.
case: splitP => k; by rewrite (ord1 k).
Qed.

Lemma triple_prod_mat_rowE (M : 'M[T]_3) :
  M = triple_prod_mat (row 0 M) (row 1 M) (row 2%:R M).
Proof.
rewrite /triple_prod_mat.
apply/matrixP => i j.
rewrite mxE /=.
case/boolP : (i == 0) => [/eqP -> |]; first by rewrite mxE.
rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE.
Qed.

Lemma row'_triple_prod_mat (i : 'I_3) (u v w : 'rV[T]_3) :
  row' i (triple_prod_mat u v w) = [eta \0 with
  0 |-> \matrix_(k < 2) [eta \0 with 0 |-> v, 1 |-> w] k,
  1 |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> w] k,
  2%:R |-> \matrix_(k < 2) [eta \0 with 0 |-> u, 1 |-> v] k] i.
Proof.
case: i => [[|[|[|?]]]] ?; apply/matrixP=> [] [[|[|[|?]]]] ? j;
by rewrite !mxE.
Qed.

Lemma triple_prod_mat_perm_12 (a b c : 'rV[T]_3) :
  xrow 1 2%:R (triple_prod_mat a b c) = triple_prod_mat a c b.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma triple_prod_mat_perm_01 a b c :
  xrow 0 1 (triple_prod_mat a b c) = triple_prod_mat b a c.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma triple_prod_mat_perm_02 a b c :
 xrow 0 2%:R (triple_prod_mat a b c) = triple_prod_mat c b a.
Proof.
apply/matrixP => -[[|[|[] //]] ?] [[|[|[] //]] ?]; by rewrite !mxE permE. 
Qed.

Lemma mulmx_triple_prod_mat M a b c : 
  triple_prod_mat a b c *m M = triple_prod_mat (a *m M) (b *m M) (c *m M).
Proof.
apply/matrixP => i j.
move: i => -[[|[|[] // ]] ?]; rewrite !mxE; apply eq_bigr => /= ? _; by rewrite mxE.
Qed.

End triple_prod_mat.

Section crossmul.

Variable R : rcfType.
Let vector := 'rV[R]_3.

(* by definition, zi = axis of joint i *)

Local Notation "A _|_ B" := (A%MS <= kermx B%MS^T)%MS (at level 69).

Lemma normal_sym k m (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) :
  A _|_ B = B _|_ A.
Proof.
rewrite !(sameP sub_kermxP eqP) -{1}[A]trmxK -trmx_mul.
by rewrite -{1}trmx0 (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma normalNm k m (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) : (- A) _|_ B = A _|_ B.
Proof. by rewrite eqmx_opp. Qed.

Lemma normalmN k m (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) : A _|_ (- B) = A _|_ B.
Proof. by rewrite ![A _|_ _]normal_sym normalNm. Qed.

Lemma normalDm k m p (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) (C : 'M[R]_(p,3)) :
  (A + B _|_ C) = (A _|_ C) && (B _|_ C).
Proof. by rewrite addsmxE !(sameP sub_kermxP eqP) mul_col_mx col_mx_eq0. Qed.

Lemma normalmD  k m p (A : 'M[R]_(k,3)) (B : 'M[R]_(m,3)) (C : 'M[R]_(p,3)) :
  (A _|_ B + C) = (A _|_ B) && (A _|_ C).
Proof. by rewrite ![A _|_ _]normal_sym normalDm. Qed.

Lemma normalvv (u v : 'rV[R]_3) : (u _|_ v) = (u *d v == 0).
Proof. by rewrite (sameP sub_kermxP eqP) [_ *m _^T]mx11_scalar fmorph_eq0. Qed.

Lemma triple_prod_mat_mulmx (v : vector) a b c : 
  v *m (triple_prod_mat a b c)^T = row3 (v *d a) (v *d b) (v *d c).
Proof.
rewrite triple_prod_matE (tr_col_mx a) (tr_col_mx b) (mul_mx_row v a^T).
by rewrite row3_row_mx (mul_mx_row v b^T) /dotmul -!mx11_scalar.
Qed.

(* Definition mixed_product_mat n (u : 'I_n -> 'rV[R]_n) :=  *)
(*   \matrix_(i < n, j < n) u i ord0 j. *)

(* Definition crossmul (u : 'rV[R]_n.+1) (v : 'I_n -> 'rV[R]_n.+1) : 'rV[R]_n.+1 := *)
(*   \row_(k < n) \det (mixed_product_mat (delta_mx 0 k)). *)

Definition crossmul (u v : vector) : vector :=
  \row_(k < 3) \det (triple_prod_mat (delta_mx 0 k) u v).

Local Notation "*v%R" := (@crossmul _).
Local Notation "u *v w" := (crossmul u w) (at level 40).

(*Definition crossmul (u v : vector) : vector :=
  \row_(i < 3) \det (col_mx (delta_mx (ord0 : 'I_1) i) (col_mx u v)).*)

Lemma crossmulC u v : u *v v = - (v *v u).
Proof.
rewrite /crossmul; apply/rowP => k; rewrite !mxE.
set M := (X in - \det X).
transitivity (\det (row_perm (tperm (1 : 'I__) 2%:R) M)); last first.
  by rewrite row_permE detM det_perm odd_tperm /= expr1 mulN1r.
congr (\det _); apply/matrixP => i j; rewrite !mxE permE /=.
by case: i => [[|[|[]]]] ?.
Qed.

Lemma crossmul0v u : 0 *v u = 0.
Proof.
apply/rowP=> k; rewrite !mxE; apply/eqP/det0P.
exists (delta_mx 0 1).
  apply/negP=> /eqP /(congr1 (fun f : 'M__ => f 0 1)) /eqP.
  by rewrite !mxE /= oner_eq0.
by rewrite -rowE; apply/rowP=> j; rewrite !mxE.
Qed.

Lemma crossmulv0 u : u *v 0 = 0.
Proof. by rewrite crossmulC crossmul0v oppr0. Qed.

Lemma crossmul_triple (u v w : 'rV[R]_3) :
  u *d (v *v w) = \det (triple_prod_mat u v w).
Proof.
pose M (k : 'I_3) : 'M_3 := triple_prod_mat (delta_mx 0 k) v w.
pose Mu12 := triple_prod_mat (u 0 1 *: delta_mx 0 1 + u 0 2%:R *: delta_mx 0 2%:R) v w.
rewrite (@determinant_multilinear _ _ _ (M 0) Mu12 0 (u 0 0) 1) ?mul1r
        ?row'_triple_prod_mat //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx /tnth /=.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
rewrite [\det Mu12](@determinant_multilinear _ _ _
  (M 1) (M 2%:R) 0 (u 0 1) (u 0 2%:R)) ?row'_triple_prod_mat //; last first.
  apply/matrixP => i j; rewrite !mxE !eqxx.
  by case: j => [[|[|[]]]] ? //=; simp_ord; simpr.
by rewrite dotmulE !big_ord_recl big_ord0 addr0 /= !mxE; simp_ord.
Qed.

Lemma crossmul_normal (u v : 'rV[R]_3) : u _|_ (u *v v).
Proof.
rewrite normalvv crossmul_triple.
rewrite (determinant_alternate (oner_neq0 _)) => [|i] //.
by rewrite !mxE.
Qed.

Lemma common_normal_crossmul u v : (u *v v) _|_ u + v.
Proof.
rewrite normalmD ![(_ *v _) _|_ _]normal_sym crossmul_normal.
by rewrite crossmulC normalmN crossmul_normal.
Qed.

(* u /\ (v + w) = u /\ v + u /\ w *)
Lemma crossmul_linear u : linear (crossmul u).
Proof.
move=> a v w; apply/rowP => k; rewrite !mxE.
pose M w := triple_prod_mat (delta_mx 0 k) u w.
rewrite (@determinant_multilinear _ _ (M _) (M v) (M w) 2%:R a 1);
  rewrite ?row'_triple_prod_mat ?mul1r ?scale1r ?mxE //=.
by apply/rowP => j; rewrite !mxE.
Qed.

Canonical crossmul_is_additive u := Additive (crossmul_linear u).
Canonical crossmul_is_linear u := AddLinear (crossmul_linear u).

Definition crossmulr u := crossmul^~ u.

Lemma crossmulr_linear u : linear (crossmulr u).
Proof.
move=> a v w; rewrite /crossmulr crossmulC linearD linearZ /=.
by rewrite opprD -scalerN -!crossmulC.
Qed.

Canonical crossmulr_is_additive u := Additive (crossmulr_linear u).
Canonical crossmulr_is_linear u := AddLinear (crossmulr_linear u).

Lemma crossmulE u v : (u *v v) = row3
  (u 0 1 * v 0 2%:R - u 0 2%:R * v 0 1)
  (u 0 2%:R * v 0 0 - u 0 0 * v 0 2%:R)
  (u 0 0 * v 0 1 - u 0 1 * v 0 0).
Proof.
apply/rowP => i; rewrite !mxE (expand_det_row _ ord0).
rewrite !(mxE, big_ord_recl, big_ord0) !(mul0r, mul1r, addr0).
rewrite /cofactor !det_mx22 !mxE /= mul1r mulN1r opprB -signr_odd mul1r.
by simp_ord; case: i => [[|[|[]]]] //= ?; rewrite ?(mul1r,mul0r,add0r,addr0).
Qed.

Lemma crossmulNv (u v : vector) : - u *v v = - (u *v v).
Proof. by rewrite crossmulC linearN /= opprK crossmulC. Qed.

Lemma crossmulvN (a b : vector) : a *v (- b) = - (a *v b).
Proof. by rewrite crossmulC crossmulNv opprK crossmulC. Qed.

Lemma crossmulZ (a b : vector) k : ((k *: a) *v b) = k *: (a *v b).
Proof. by rewrite crossmulC linearZ /= crossmulC scalerN opprK. Qed.

Lemma crossmul0E (u v : vector) : 
  (u *v v == 0) = [forall i, [forall j, (i != j) ==> (v 0 i * u 0 j == u 0 i * v 0 j)]].
Proof.
apply/idP/idP => [/eqP|].
  rewrite crossmulE => uv0.
  apply/forallP => /= i. apply/forallP => /= j. apply/implyP => ij.
  case: (thirdI3 ij) => k Hk.
  move/rowP : uv0 => /(_ k).
  rewrite !mxE /= => /eqP.
  case: ifPn => [/eqP k0|k0].
    rewrite subr_eq0; move: Hk ij; rewrite k0 eq_sym ifnot0 (eq_sym _ j) ifnot0.
    case/andP => /orP[] /eqP -> /orP [] /eqP -> // _ /eqP;
      [move=> ->; by rewrite mulrC | move=> <-; by rewrite mulrC].
  case: ifPn => [/eqP k1|k1].
    rewrite subr_eq0; move: Hk ij; rewrite k1 eq_sym ifnot1 (eq_sym _ j) ifnot1.
    case/andP => /orP[] /eqP -> /orP [] /eqP -> // _ /eqP;
      [move=> <-; by rewrite mulrC | move=> ->; by rewrite mulrC].
  case: ifPn => [/eqP k2|k2 _].
    rewrite subr_eq0; move: Hk ij; rewrite k2 eq_sym ifnot2 (eq_sym _ j) ifnot2.
    case/andP => /orP[] /eqP -> /orP [] /eqP -> // _ /eqP;
      [move=> ->; by rewrite mulrC | move=> <-; by rewrite mulrC].
  move: (ifnot0 k); by rewrite k0 (negbTE k1) (negbTE k2).  
move/forallP => /= H; apply/eqP/rowP => i.
rewrite crossmulE !mxE /=; apply/eqP.
case: ifPn => [_|].
  move: (H 1) => /forallP/(_ 2%:R) /= /eqP <-; by rewrite subr_eq0 mulrC.
rewrite ifnot0 => /orP [] /eqP -> /=.
- move: (H 0) => /forallP/(_ 2%:R) /= /eqP <-; by rewrite subr_eq0 mulrC.
- move: (H 0) => /forallP/(_ 1) /= /eqP <-; by rewrite subr_eq0 mulrC.
Qed.

(* rewrite linear_sum. *)

Lemma crossmulvv (u : vector) : u *v u = 0.
Proof.
rewrite crossmulE; apply/rowP => i; rewrite !mxE; do 3 rewrite mulrC subrr.
rewrite /SimplFunDelta /=; case: ifP => [//|_]; case: ifP => [//|_]; by case: ifP.
Qed.

Lemma mulmxl_crossmulr M u v : M *m (u *v v) = u *v (M *m v).
Proof. by rewrite -(mul_rV_lin1 [linear of crossmul u]) mulmxA mul_rV_lin1. Qed.

Lemma mulmxl_crossmull M u v : M *m (u *v v) = ((M *m u) *v v).
Proof. by rewrite crossmulC mulmxN mulmxl_crossmulr -crossmulC. Qed.

(* Lemma mulmxr_crossmulr o u v : o \in so -> *)
(*   (u *v v) *m o = ((u *m o) *v (v *m o)). *)
(* Proof. *)
(* rewrite -[M]trmxK [M^T]matrix_sum_delta. *)
(* rewrite !linear_sum /=; apply: eq_bigr=> i _. *)
(* rewrite !linear_sum /=; apply: eq_bigr=> j _. *)
(* rewrite !mxE !linearZ /= trmx_delta. *)
(* rewr *)
(* rewrite -[in RHS]/(crossmulr _ _). *)
(* rewrite linear_sum /= /crossmu. *)
(* rewrite *)

(* apply/rowP => k; rewrite !mxE. *)
(* rewrite -![_ *v _](mul_rV_lin1 [linear of crossmulr _]). *)
(* rewrite -!mulmxA. *)
(* rewrite mul_rV_lin. *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr (v * M)]). *)

(* rewrite -/(mulmxr _ _) -!(mul_rV_lin1 [linear of mulmxr M]). *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr v]). *)

(* rewrite -!/(crossmulr _ _). *)
(* rewrite -!(mul_rV_lin1 [linear of crossmulr v]). *)
(* Abort. *)

(*
/mulmxr. mul_rV_lin1.
Qed.
*)

Lemma dotmul_crossmul_shift a b c : a *d (b *v c) = c *d (a *v b).
Proof. 
rewrite crossmul_triple.
rewrite -triple_prod_mat_perm_12 xrowE det_mulmx det_perm /= odd_tperm /=.
rewrite -triple_prod_mat_perm_01 xrowE det_mulmx det_perm /= odd_tperm /=.
by rewrite expr1 mulrA mulrNN 2!mul1r -crossmul_triple.
Qed.

Lemma dotmul_crossmulA u v x : u *d (v *v x) = (u *v v) *d x.
Proof. by rewrite dotmul_crossmul_shift dotmulC. Qed.

Lemma dotmul_crossmulCA a b c : a *d (b *v c) = - b *d (a *v c).
Proof. 
do 2  rewrite dotmul_crossmulA. 
by rewrite crossmulNv crossmulC.
Qed.

Lemma det_triple_prod_mat u v (x : vector) : 
  \det (triple_prod_mat u v x) = (u *v v) *d x.
Proof. by rewrite -crossmul_triple dotmul_crossmulA. Qed.

Lemma det_crossmul_dotmul M a b (x : vector) : 
  (\det M *: (a *v b)) *d x = (((a *m M) *v (b *m M)) *m M^T) *d x.
Proof.
transitivity (\det M * \det (triple_prod_mat a b x)).
  by rewrite dotmulZv -crossmul_triple dotmul_crossmulA.
transitivity (\det (triple_prod_mat (a *m M) (b *m M) (x *m M))).
  by rewrite mulrC -det_mulmx mulmx_triple_prod_mat.
transitivity (((a *m M) *v (b *m M)) *d (x *m M)).
  by rewrite det_triple_prod_mat.
by rewrite dotmul_trmx.
Qed.

Lemma mulmx_crossmul' M (a b : vector) :
  \det M *: (a *v b) = ((a *m M) *v (b *m M)) *m M^T.
Proof. apply dotmul_eq => x; exact: det_crossmul_dotmul. Qed.

Lemma mulmx_crossmul M (a b : vector) : M \is a GRing.unit ->
  (a *v b) *m (\det M *: M^-1^T) = (a *m M) *v (b *m M).
Proof.
move=> invM.
move: (mulmx_crossmul' M a b) => /(congr1 (fun x => x *m M^T^-1)).
rewrite -mulmxA mulmxV ?unitmx_tr // mulmx1 => <-.  
by rewrite -scalemxAr trmx_inv scalemxAl.
Qed.

Lemma double_crossmul (u v w : 'rV[R]_3) :
 u *v (v *v w) = (u *d w) *: v - (u *d v) *: w.
Proof.
(*
have [->|u_neq0] := eqVneq u 0.
  by rewrite crossmul0v !dotmul0v !scale0r subr0.
have : exists M : 'M_3, u *m M = delta_mx 0 0.

rewrite !crossmulE; apply/rowP => i.
rewrite !dotmulE !(big_ord_recl, big_ord0, addr0) !mxE /=.
simpr; rewrite oppr0 opprB addr0.
by case: i => [[|[|[|?]]]] ? //=; simp_ord => //=; rewrite mulrC ?subrr.
Qed.

rewrite !mulrDl !mulrBr !mulrA ?opprB.
*)
apply/rowP => i.
have : i \in [:: ord0 ; 1 ; 2%:R].
  have : i \in enum 'I_3 by rewrite mem_enum.
  rewrite 3!enum_ordS (_ : enum 'I_0 = nil) // -enum0.
  apply eq_enum => i'; by move: (ltn_ord i').
rewrite inE; case/orP => [/eqP ->|].
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  rewrite /tnth /=.
  move : (_ * (_ * _)) => a. move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c. move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB -addrA (addrC (- b)) 2!addrA -addrA -opprB opprK.
  move: (a + d) => f. move: (b + c) => g.
  by rewrite [in RHS](addrC e) opprD addrA addrK.
rewrite inE; case/orP => [/eqP ->|].
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite /tnth /=.
  rewrite 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  move : (_ * (_ * _)) => a. move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c. move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB -addrA (addrC (- b)) 2!addrA -addrA -opprB opprK.
  rewrite [in RHS](addrC e) [in RHS]addrA.
  rewrite (addrC d).
  move: (a + d) => f.
  rewrite [in RHS](addrC e) [in RHS]addrA (addrC c).
  move: (b + c) => g.
  by rewrite (addrC g) opprD addrA addrK.
rewrite inE => /eqP ->.
  rewrite !crossmulE /dotmul !mxE.
  do 2 rewrite 3!big_ord_recl big_ord0 !mxE.
  rewrite -/1 -/2%:R !addr0 !mulrDl !mulrDr.
  simp_ord.
  rewrite /tnth /= 2!mulrN -!mulrA (mulrC (w 0 0)) (mulrC (w 0 1)) (mulrC (w 0 2%:R)).
  move : (_ * (_ * _)) => a. move : (_ * (_ * _)) => b.
  move : (_ * (_ * _)) => c. move : (_ * (_ * _)) => d.
  move : (_ * (_ * _)) => e.
  rewrite opprB -addrA (addrC (- b)) 2!addrA -addrA -opprB opprK [in RHS]addrA.
  move: (a + d) => f.
  rewrite [in RHS]addrA.
  move: (b + c) => g.
  by rewrite (addrC g) opprD addrA addrK.
Qed.

Lemma dotmul_crossmul2 (a b c : vector) : (a *v b) *v (a *v c) = (a *d (b *v c)) *: a.
Proof.
by rewrite double_crossmul (dotmulC _ a) dotmul_crossmulA crossmulvv dotmul0v 
  scale0r subr0 -dotmul_crossmulA.
Qed.

Lemma jacobi u v w : u *v (v *v w) + v *v (w *v u) + w *v (u *v v) = 0.
Proof.
(* consequence of double_crossmul *)
rewrite 3!double_crossmul.
rewrite !addrA -(addrA (_ *: v)) (dotmulC u v) -(addrC (_ *: w)) subrr addr0.
rewrite -!addrA addrC -!addrA (dotmulC w u) -(addrC (_ *: v)) subrr addr0.
by rewrite addrC dotmulC subrr.
Qed.

End crossmul.

Notation "*v%R" := (@crossmul _) : ring_scope.
Notation "u *v w" := (crossmul u w) (at level 40) : ring_scope.

Section orthogonal_rotation_def.

Variables (n : nat) (R : rcfType).

Definition orthogonal := [qualify M : 'M[R]_n | M *m M^T == 1%:M].
Fact orthogonal_key : pred_key orthogonal. Proof. by []. Qed.
Canonical orthogonal_keyed := KeyedQualifier orthogonal_key.

Definition rotation := [qualify M : 'M[R]_n | (M \is orthogonal) && (\det M == 1)].
Fact rotation_key : pred_key rotation. Proof. by []. Qed.
Canonical rotation_keyed := KeyedQualifier rotation_key.

End orthogonal_rotation_def.

Local Notation "''O_' n [ R ]" := (orthogonal n R)
  (at level 8, n at level 2, format "''O_' n [ R ]").

Local Notation "''SO_' n [ R ]" := (rotation n R)
  (at level 8, n at level 2, format "''SO_' n [ R ]").

Section orthogonal.

Variables (n' : nat) (R : rcfType).
Let n := n'.+1.

Lemma orthogonalE M : (M \is 'O_n[R]) = (M * M^T == 1). Proof. by []. Qed.

Lemma orthogonal1 : 1 \is 'O_n[R].
Proof. by rewrite orthogonalE trmx1 mulr1. Qed.

Lemma orthogonalEinv M : (M \is 'O_n[R]) = (M \is a GRing.unit) && (M^-1 == M^T).
Proof.
rewrite orthogonalE; have [Mu | notMu] /= := boolP (M \in unitmx); last first.
  by apply: contraNF notMu => /eqP /mulmx1_unit [].
by rewrite -(inj_eq (@mulrI _ M^-1 _)) ?unitrV // mulr1 mulKr.
Qed.

Lemma orthogonal_unit M : (M \is 'O_n[R]) -> (M \is a GRing.unit).
Proof. by rewrite orthogonalEinv => /andP []. Qed.

Lemma orthogonalV M : (M^T \is 'O_n[R]) = (M \is 'O_n[R]).
Proof.
by rewrite !orthogonalEinv unitmx_tr -trmxV (inj_eq (@trmx_inj _ _ _)).
Qed.

Lemma orthogonal_inv M : M \is 'O_n[R] -> M^-1 = M^T.
Proof. by rewrite orthogonalEinv => /andP [_ /eqP]. Qed.

Lemma orthogonalEC M : (M \is 'O_n[R]) = (M^T * M == 1).
Proof. by rewrite -orthogonalV orthogonalE trmxK. Qed.

Lemma orthogonal_det M : M \is 'O_n[R] -> `|\det M| = 1.
Proof.
move=> /eqP /(congr1 determinant); rewrite detM det_tr det1 => /eqP.
by rewrite sqr_norm_eq1 => /eqP.
Qed.

Lemma orthogonal_oppr_closed : oppr_closed 'O_n[R].
Proof. by move=> x; rewrite !orthogonalE linearN /= mulNr mulrN opprK. Qed.
Canonical orthogonal_is_oppr_closed := OpprPred orthogonal_oppr_closed.

Lemma orthogonal_divr_closed : divr_closed 'O_n[R].
Proof.
split => [| P Q HP HQ]; first exact: orthogonal1.
rewrite orthogonalE orthogonal_inv // trmx_mul trmxK -mulrA.
by rewrite -orthogonal_inv // mulKr // orthogonal_unit.
Qed.
Canonical orthogonal_is_mulr_closed := MulrPred orthogonal_divr_closed.
Canonical orthogonal_is_divr_closed := DivrPred orthogonal_divr_closed.
Canonical orthogonal_is_smulr_closed := SmulrPred orthogonal_divr_closed.
Canonical orthogonal_is_sdivr_closed := SdivrPred orthogonal_divr_closed.

Lemma rotationE M : (M \is 'SO_n[R]) = (M \is 'O_n[R]) && (\det M == 1). Proof. by []. Qed.

Lemma rotationV M : (M^T \is 'SO_n[R]) = (M \is 'SO_n[R]).
Proof. by rewrite rotationE orthogonalV det_tr -rotationE. Qed.

Lemma rotation_inv M : M \is 'SO_n[R] -> M^-1 = M^T.
Proof. by rewrite rotationE orthogonalEinv => /andP[/andP[_ /eqP]]. Qed.

Lemma rotation_det M : M \is 'SO_n[R] -> \det M = 1.
Proof. by move=> /andP[_ /eqP]. Qed.

Lemma rotation1 : 1 \is 'SO_n[R].
Proof. apply/andP; by rewrite orthogonal1 det1. Qed.

Lemma rotation_sub : {subset 'SO_n[R] <= 'O_n[R]}.
Proof. by move=> M /andP []. Qed.

Lemma rotation_divr_closed : divr_closed 'SO_n[R].
Proof.
split => [|P Q Prot Qrot]; first exact: rotation1.
rewrite rotationE rpred_div ?rotation_sub //=.
by rewrite det_mulmx det_inv !rotation_det // divr1.
Qed.

Canonical rotation_is_mulr_closed := MulrPred rotation_divr_closed.
Canonical rotation_is_divr_closed := DivrPred rotation_divr_closed.

End orthogonal.

Lemma orthogonalP {n} R M : 
  reflect (forall i j, row i M *d row j M = (i == j)%:R) (M \is 'O_n.+1[R]).
Proof.
apply: (iffP idP) => [|H] /=.
  rewrite orthogonalE => /eqP H i j.
  move/matrixP/(_ i j) : H; rewrite /dotmul !mxE => <-.
  apply eq_bigr => k _; by rewrite !mxE.
rewrite orthogonalE.
apply/eqP/matrixP => i j; rewrite !mxE.
rewrite -H /dotmul !mxE.
apply eq_bigr => k _; by rewrite !mxE.
Qed.

Lemma dotmul_conjc_eq0 {R : rcfType} n (v : 'rV[R[i]]_n.+1) : 
  (v *m map_mx conjc v^T == 0) = (v == 0).
Proof.
apply/idP/idP => [H|/eqP ->]; last by rewrite mul0mx.
have : \sum_(i < n.+1) v 0 i * (v 0 i)^* = 0.
  move/eqP/matrixP : H =>/(_ 0 0).
  rewrite !mxE => H; rewrite -{2}H.
  apply/eq_bigr => /= i _; by rewrite !mxE.
move/eqP; rewrite psumr_eq0 /= => [/allP K|]; last first.
  move=> i _; by rewrite -sqr_normc exprn_ge0.
apply/eqP/rowP => i.
move: (K i); rewrite /index_enum -enumT mem_enum inE => /(_ isT).
rewrite -sqr_normc sqrf_eq0 normr_eq0 => /eqP ->; by rewrite mxE.
Qed.

Lemma eigenvalue_O {R : rcfType} n M : M \is 'O_n.+1[R] -> forall k,
   k \in eigenvalue (map_mx (fun x => x%:C) M) -> `| k | = 1.
Proof.
move=> MSO /= k.
case/eigenvalueP => v kv v0.
move/(congr1 trmx)/(congr1 (fun x => map_mx conjc x)) : (kv).
rewrite trmx_mul map_mxM linearZ /= map_mxZ map_trmx.
move/(congr1 (fun x => (k *: v) *m x)).
rewrite -{1}kv -mulmxA (mulmxA (map_mx _ M)) (_ : map_mx _ M *m _ = 1%:M); last first.
  rewrite (_ : map_mx conjc _ = map_mx (fun x => x%:C) M^T); last first.
    apply/matrixP => i j; by rewrite !mxE conjc_real.
  rewrite orthogonalE in MSO.
  by rewrite -map_mxM mulmxE (eqP MSO) map_mx1.
rewrite mul1mx -scalemxAr /= -scalemxAl scalerA => /eqP.
rewrite -subr_eq0 -{1}(scale1r (v *m _)) -scalerBl scaler_eq0 => /orP [].
  by rewrite subr_eq0 mulrC -sqr_normc -{1}(expr1n _ 2) eqr_expn2 // ?ler01 // => /eqP.
by rewrite dotmul_conjc_eq0 (negbTE v0).
Qed.

Section orthogonal_crossmul.

Variable R : rcfType.

(* "From the geometrical definition, the cross product is invariant under 
   proper rotations about the axis defined by a × b"
   https://en.wikipedia.org/wiki/Cross_product *)
Lemma mulmxr_crossmulr r u v : r \is 'O_3[R] -> 
  (u *v v) *m r = \det r *: ((u *m r) *v (v *m r)).
Proof. 
move=> rO; move: (rO).
rewrite orthogonalEinv => /andP[r1 /eqP rT].
rewrite -mulmx_crossmul //.
move/eqP: (orthogonal_det rO).
rewrite eqr_norml // => /andP[ /orP[/eqP-> |/eqP->] _];
  rewrite ?scale1r rT trmxK //.
by rewrite -scalemxAr scalerA mulrNN !mul1r scale1r.
Qed.

Lemma eigenspace_trmx r (Hr : r \is 'O_3[R]) (n : 'rV[R]_3) :
  (n <= eigenspace r 1 <-> n <= eigenspace r^T 1)%MS.
Proof.
move: (Hr); rewrite orthogonalE => /eqP Hr1.
move: Hr; rewrite orthogonalEC => /eqP Hr2.
split.
  move/eigenspaceP; rewrite scale1r => nrn.
  apply/eigenspaceP; rewrite scale1r.
  by rewrite -{1}nrn -mulmxA mulmxE Hr1 mulmx1.
move/eigenspaceP; rewrite scale1r => nrn.
apply/eigenspaceP; rewrite scale1r.
by rewrite -{1}nrn -mulmxA mulmxE Hr2 mulmx1.
Qed.

Lemma mulmxr_crossmulr_SO r u v : r \is 'SO_3[R] ->
  (u *v v) *m r = (u *m r) *v (v *m r).
Proof. 
rewrite rotationE => /andP[rO /eqP detr1].
by rewrite mulmxr_crossmulr // detr1 scale1r.
Qed.

Lemma det_rotN1 (M : 'M[R]_3) : M \is 'SO_3[R] -> \det (M - 1) = 0.
Proof.
move=> MSO.
suff /eqP : \det (M - 1) = - \det (M - 1).
  by rewrite -subr_eq0 opprK -mulr2n -mulr_natr mulf_eq0 pnatr_eq0 orbF => /eqP.
rewrite -{1}det_tr.
move/eqP : MSO; rewrite rotationE => /eqP/andP[].
rewrite orthogonalEC => /eqP MMT /eqP detM.
rewrite -{1}MMT -{1}(mul1r M) -mulrBl trmx_mul.
rewrite linearD /= trmx1 linearN /= trmxK -opprB.
rewrite mulmxN -scaleN1r detZ -signr_odd expr1 mulN1r.
by rewrite det_mulmx det_tr detM mul1r.
Qed.

Lemma rot_eigen1 (M : 'M[R]_3) : M \is 'SO_3[R] -> eigenspace M 1 != 0.
Proof.
move/det_rotN1 => /eqP/det0P[n n0]; rewrite mulmxBr mulmx1 => /eqP.
rewrite subr_eq0 => /eqP nM.
apply/rowV0Pn; exists n => //.
apply/sub_kermxP.
by rewrite mulmxBr mulmx1 nM subrr.
Qed.

Lemma euler (M : 'M[R]_3) : M \is 'SO_3[R] -> {x : 'rV[R]_3 | (x != 0) && (x *m M == x)}.
Proof.
move/rot_eigen1 => H; apply sigW.
case/rowV0Pn : H => x /eigenspaceP Hx x0; exists x.
rewrite scale1r in Hx.
by rewrite x0 /= Hx.
Qed.

Lemma O3_RO (M : 'M[R]_3) (P : 'M[R]_2) : M = block_mx (1 : 'M_1) 0 0 P ->
  (M \is 'O_3[R]) = (P \is 'O_2[R]).
Proof.
move=> HM.
rewrite HM !orthogonalE (tr_block_mx (1 : 'M_1)) trmx1 2!trmx0.
rewrite -mulmxE (mulmx_block (1 : 'M_1) _ _ _ 1) !(mulmx0,mul0mx,mulmx1,mul1mx,addr0,add0r).
rewrite -[X in (_ == X) = _](@submxK _ 1 2 1 2).
rewrite (_ : ulsubmx _ = 1); last by apply/rowP => i; rewrite !mxE.
rewrite (_ : ursubmx _ = 0); last by apply/rowP => i; rewrite !mxE.
rewrite (_ : dlsubmx _ = 0); last by apply/colP => i; rewrite !mxE.
rewrite (_ : drsubmx _ = 1); last first.
  apply/matrixP => i j.
  case/boolP : (i == 0) => [/eqP ->|].
    case/boolP : (j == 0) => [/eqP ->|]; first by rewrite !mxE.
    rewrite ifnot01 => /eqP ->; by rewrite !mxE.
  rewrite ifnot01 => /eqP ->; by rewrite !mxE.
rewrite mulmxE.
apply/idP/idP => [|/eqP -> //].
by case/eqP/(@eq_block_mx _ 1 2 1 2) => _ _ _ ->.
Qed.

Lemma SO_RO (M : 'M[R]_3) (P : 'M[R]_2) : M = block_mx (1 : 'M_1) 0 0 P ->
  (M \is 'SO_3[R]) = (P \is 'SO_2[R]).
Proof.
move=> ->; by rewrite rotationE (@O3_RO _ P) // rotationE (@det_lblock _ 1 2) det1 mul1r.
Qed.

End orthogonal_crossmul.

Section norm.

Variables (R : rcfType) (n : nat).
Implicit Types u : 'rV[R]_n.

Definition norm u := Num.sqrt (u *d u).

Lemma normN a : norm (- a) = norm a.
Proof. by rewrite /norm dotmulNv dotmulvN opprK. Qed.

Lemma norm2 (k : R) : `| k | ^+ 2 = k ^+ 2.
Proof.
case: (ltrP 0 k) => [k0|]; first by rewrite gtr0_norm.
rewrite ler_eqVlt; case/orP => [/eqP ->|k0]; first by rewrite normr0.
by rewrite ltr0_norm // sqrrN.
Qed.

Lemma norm0 : norm 0 = 0.
Proof. by rewrite /norm dotmul0v sqrtr0. Qed.

Lemma norm_delta_mx i : norm (delta_mx 0 i) = 1.
Proof.
rewrite /norm dotmulE (bigD1 i) ?mxE //= ?eqxx mul1r big1 ?addr0 ?sqrtr1 //.
by move=> j /negPf eq_ij; rewrite mxE eqxx eq_ij mulr0.
Qed.

Lemma norm_ge0 u : norm u >= 0.
Proof. by apply sqrtr_ge0. Qed.
Hint Resolve norm_ge0.

Lemma normr_norm u : `|norm u| = norm u.
Proof. by rewrite ger0_norm. Qed.

Lemma norm_eq0 u : (norm u == 0) = (u == 0).
Proof. by rewrite -sqrtr0 eqr_sqrt // ?dotmulvv0 // le0dotmul. Qed.

Lemma normZ (k : R) u : norm (k *: u) = `|k| * norm u.
Proof.
by rewrite /norm dotmulvZ dotmulZv mulrA sqrtrM -expr2 ?sqrtr_sqr // sqr_ge0.
Qed.

Lemma dotmulvv u : u *d u = norm u ^+ 2.
Proof.
rewrite /norm [_ ^+ _]sqr_sqrtr // dotmulE sumr_ge0 //.
by move=> i _; rewrite sqr_ge0.
Qed.

Section norm1.

Variable u : 'rV[R]_n.
Hypothesis u1 : norm u = 1.

Lemma dotmul1 : u *m u^T = 1.
Proof.
by rewrite (mx11_scalar 1) mxE eqxx -(expr1n _ 2) -u1 mulr1n -dotmulvv
  -mx11_scalar.
Qed.

End norm1.

End norm.

Lemma norm_row_of_O {R : rcfType} n M : M \is 'O_n.+1[R] -> forall i, norm (row i M) = 1.
Proof.
move=> MSO i.
apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n; apply/eqP.
rewrite -dotmulvv; move/orthogonalP : MSO => /(_ i i) ->; by rewrite eqxx.
Qed.

Definition preserves_dotmul {R : rcfType} n (f : 'rV[R]_n -> 'rV[R]_n) :=
  forall a b, f a *d f b = a *d b.

Lemma orth_preserves_dotmul_helper R n v M : M \is 'O_n.+1[R] -> (v *m M) *d (v *m M) = v *d v.
Proof.
move=> HM; rewrite dotmul_trmx -mulmxA (_ : M *m _ = 1%:M) ?mulmx1 //.
by move: HM; rewrite orthogonalE => /eqP.
Qed.

Lemma orth_preserves_dotmul {R : rcfType} n (f : 'M[R]_n.+1) :
  preserves_dotmul (fun x : 'rV[R]_n.+1 => x *m f) <-> f \is 'O_n.+1[R].
Proof.
split => H.
  rewrite /preserves_dotmul in H.
  apply/orthogonalP => i j.
  by rewrite 2!rowE H dotmul_delta_mx mxE eqxx /= eq_sym.
move=> u v.
have := orth_preserves_dotmul_helper (u + v) H.
rewrite mulmxDl dotmulD.
rewrite dotmulD.
rewrite orth_preserves_dotmul_helper // (orth_preserves_dotmul_helper v H) //.
move/(congr1 (fun x => x - v *d v)).
rewrite -!addrA subrr 2!addr0.
move/(congr1 (fun x => - (u *d u) + x)).
rewrite !addrA (addrC (- (u *d u))) subrr 2!add0r.
rewrite -2!mulr2n => /eqP.
by rewrite eqr_pmuln2r // => /eqP.
Qed.

Definition preserves_norm {R : rcfType} n (f : 'rV[R]_n -> 'rV[R]_n) :=
  forall v, norm (f v) = norm v.

(* NB: useful? *)
Lemma orth_preserves_norm R n M : M \is 'O_n.+1[R] -> preserves_norm (fun x : 'rV[R]_n.+1 => x *m M).
Proof. move=> HM v; by rewrite /norm (proj2 (orth_preserves_dotmul M) HM). Qed.

Section norm2.

Variable R : rcfType.
Implicit Types u : 'rV[R]_2.

Lemma sqr_norm2 u : norm u ^+ 2 = u 0 0 ^+ 2 + u 0 1 ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum2E -2!expr2. Qed.

End norm2.

Section norm3.

Variable R : rcfType.
Implicit Types u : 'rV[R]_3.

Lemma sqr_norm u : norm u ^+ 2 = u 0 0 ^+ 2 + u 0 1 ^+ 2 + u 0 2%:R ^+ 2.
Proof. by rewrite -dotmulvv dotmulE sum3E !expr2. Qed.

Lemma norm_crossmul' u v : (norm (u *v v)) ^+ 2 = (norm u * norm v) ^+ 2 - (u *d v) ^+ 2 .
Proof.
rewrite sqr_norm crossmulE /SimplFunDelta /= !mxE /=.
transitivity (((u 0 0)^+2 + (u 0 1)^+2 + (u 0 2%:R)^+2)
  * ((v 0 0)^+2 + (v 0 1)^+2 + (v 0 2%:R)^+2)
  - (u 0 0 * v 0 0 + u 0 1 * v 0 1 + u 0 2%:R * v 0 2%:R)^+2).
  set u0 := u 0 0. set v0 := v 0 0.
  set u1 := u 0 1. set v1 := v 0 1.
  set u2 := u 0 2%:R. set v2 := v 0 2%:R.
  rewrite !sqrrB !mulrDr !mulrDl !sqrrD.
  set A := u1 * v2. set A' := u2 * v1.
  set B := u2 * v0. set B' := u0 * v2.
  set C := u0 * v1. set C' := u1 * v0.
  set U0 := u0 ^+ 2. set U1 := u1 ^+ 2. set U2 := u2 ^+ 2.
  set V0 := v0 ^+ 2. set V1 := v1 ^+ 2. set V2 := v2 ^+ 2.
  rewrite (_ : u0 * v0 * (u1 * v1) = C * C'); last first.
    rewrite /C /C' -2!mulrA; congr (_ * _).
    rewrite mulrA mulrC; congr (_ * _); by rewrite mulrC.
  rewrite mulrDl.
  rewrite (_ : u0 * v0 * (u2 * v2) = B * B'); last first.
    rewrite /B /B' [in RHS]mulrC -!mulrA; congr (_ * _).
    rewrite mulrA -(mulrC v2); congr (_ * _); by rewrite mulrC.
  rewrite (_ : u1 * v1 * (u2 * v2) = A * A'); last first.
    rewrite /A /A' -!mulrA; congr (_ * _).
    rewrite mulrA -(mulrC v2); congr (_ * _); by rewrite mulrC.
  rewrite (_ : (u0 * v0) ^+ 2 = U0 * V0); last by rewrite exprMn.
  rewrite (_ : (u1 * v1) ^+ 2 = U1 * V1); last by rewrite exprMn.
  rewrite (_ : (u2 * v2) ^+ 2 = U2 * V2); last by rewrite exprMn.
  rewrite 4![in RHS]opprD.
  (* U0 * V0 *)
  rewrite -3!(addrA (U0 * V0)) -3![in X in _ = _ + X](addrA (- (U0 * V0))).
  rewrite [in RHS](addrAC (U0 * V0)) [in RHS](addrA (U0 * V0)) subrr add0r.
  (* U1 * V1 *)
  rewrite -(addrC (- (U1 * V1))) -(addrC (U1 * V1)) (addrCA (U1 * V0 + _)).
  rewrite -3!(addrA (- (U1 * V1))) -![in X in _ = _ + X](addrA (U1 * V1)) addrCA.
  rewrite [in RHS](addrA (- (U1 * V1))) [in RHS](addrC (- (U1 * V1))) subrr add0r.
  (* U2 * V2 *)
  rewrite -(addrC (- (U2 * V2))) -(addrC (U2 * V2)) -(addrC (U2 * V2 + _)).
  rewrite [in RHS]addrAC 2!(addrA (- (U2 * V2))) -(addrC (U2 * V2)) subrr add0r.
  (* C * C' ^+ 2 *)
  rewrite (addrC (C ^+ 2 - _)) ![in LHS]addrA.
  rewrite (addrC (C * C' *- 2)) ![in RHS]addrA; congr (_ - _).
  rewrite (_ : U0 * V2 = B' ^+ 2); last by rewrite exprMn.
  rewrite (_ : U1 * V2 = A ^+ 2); last by rewrite exprMn.
  rewrite (_ : U0 * V1 = C ^+ 2); last by rewrite exprMn.
  rewrite (_ : U1 * V0 = C' ^+ 2); last by rewrite exprMn.
  rewrite (_ : U2 * V0 = B ^+ 2); last by rewrite exprMn.
  rewrite (_ : U2 * V1 = A' ^+ 2); last by rewrite exprMn.
  (* B' ^+ 2, A ^+ 2 *)
  rewrite -(addrC (B' ^+ 2)) -!addrA; congr (_ + (_ + _)).
  rewrite !addrA.
  (* B ^+ 2 *)
  rewrite -2!(addrC (B ^+ 2)) -!addrA; congr (_ + _).
  rewrite !addrA.
  (* C ^+ 2 *)
  rewrite -(addrC (C ^+ 2)) -!addrA; congr (_ + _).
  rewrite !addrA.
  (* C' ^+ 2 *)
  rewrite -(addrC (C' ^+ 2)) -!addrA; congr (_ + _).
  rewrite !addrA.
  (* A' ^+ 2 *)
  rewrite -(addrC (A' ^+ 2)) -!addrA; congr (_ + _).
  rewrite -!mulNrn !mulr2n !opprD.
  rewrite addrC -!addrA; congr (_ + _).
  rewrite addrA.
  rewrite addrC -!addrA; congr (_ + _).
  by rewrite addrC.
rewrite exprMn -2!sqr_norm; congr (_ - _ ^+ 2).
by rewrite dotmulE sum3E.
Qed.

Lemma orth_preserves_norm_crossmul M u v : M \is 'O_3[R] ->
  norm (u *v v) = norm ((u *m M) *v (v *m M)).
Proof.
move=> MO; rewrite -(orth_preserves_norm MO (u *v v)).
by rewrite (mulmxr_crossmulr u v MO) normZ (orthogonal_det MO) mul1r.
Qed.

Lemma norm_crossmul_normal u v : u *d v = 0 ->
  norm u = 1 -> norm v = 1 -> norm (u *v v) = 1.
Proof.
move=> uv0 u1 v1; apply/eqP.
rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 //.
by rewrite norm_crossmul' u1 v1 uv0 expr0n /= subr0 mulr1 // norm_ge0.
Qed.

Lemma dotmul_eq0_crossmul_neq0 (u v : 'rV[R]_3) : u != 0 -> v != 0 -> u *d v == 0 -> u *v v != 0.
Proof.
move=> u0 v0 uv0.
rewrite -norm_eq0 -(@eqr_expn2 _ 2) // ?norm_ge0 // exprnP expr0n -exprnP. 
rewrite norm_crossmul' (eqP uv0) expr0n subr0 -expr0n eqr_expn2 //.
by rewrite mulf_eq0 negb_or 2!norm_eq0 u0.
by rewrite mulr_ge0 // ?norm_ge0.
Qed.

Lemma crossmul0_dotmul (u v : 'rV[R]_3) : u *v v == 0 -> (u *d v) ^+ 2 = u *d u * (v *d v).
Proof.
rewrite crossmul0E => uv0.
rewrite !dotmulE expr2 !big_distrl /=.
apply eq_bigr => i _; rewrite -!mulrA; congr (_ * _).
rewrite 2!big_distrr /=.
apply eq_bigr => j /= _; rewrite !mulrA; congr (_ * _).
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite mulrC.
move/forallP : uv0 => /(_ i)/forallP/(_ j).
by rewrite ij implyTb => /eqP.
Qed.

End norm3.

Lemma matrix_is_orthogonal {R : rcfType} (M : 'M[R]_3) :
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 -> norm (row 2%:R M) = 1 ->
  row 0 M *d row 1 M = 0 -> row 0 M *d row 2%:R M = 0 -> row 1 M *d row 2%:R M = 0 ->
  M \is 'O_3[R].
Proof.
move=> ni nj nk xy0 xz0 yz0 /=.
apply/orthogonalP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulvv ni expr1n.
  rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite xy0.
  by rewrite xz0.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulC.
  rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite dotmulvv nj expr1n.
  by rewrite yz0.
case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite dotmulC xz0.
rewrite ifnot0 => /orP [] /eqP -> /=; first by rewrite dotmulC yz0.
by rewrite dotmulvv nk expr1n.
Qed.

Lemma matrix_is_rotation {R : rcfType} (M : 'M[R]_3) :
  norm (row 0 M) = 1 -> norm (row 1 M) = 1 ->
  row 0 M *d row 1 M = 0 ->
  row 2%:R M = row 0 M *v row 1 M -> M \is 'SO_3[R].
Proof.
move=> ni nj xy0 zxy0 /=.
rewrite rotationE; apply/andP; split.
  apply matrix_is_orthogonal => //.
  by rewrite zxy0 norm_crossmul_normal.
  by rewrite zxy0 dotmul_crossmulA crossmulvv dotmul0v.
  by rewrite zxy0 dotmul_crossmulCA crossmulvv dotmulv0.
rewrite (triple_prod_mat_rowE M) det_triple_prod_mat zxy0 dotmul_crossmulA.
rewrite crossmulC double_crossmul xy0 scale0r add0r opprK dotmulvv.
by rewrite ni expr1n scale1r dotmulvv nj expr1n.
Qed.

Lemma pnatr_is_a_unit {R : rcfType} n : n.+1%:R \is a @GRing.unit R.
Proof. by rewrite unitfE pnatr_eq0. Qed.

Section angle.

Variable R : rcfType.
Record angle := Angle {
  expi : R[i]; 
  _ : `| expi | == 1
}.

Lemma ReZ (x : R[i]) (k : R) : Re (k%:C * x) = k * Re x.
Proof. 
case: x => a b /=; by rewrite mul0r subr0.
Qed.

Fact angle0_subproof : `| 1 / `| 1 | | == 1 :> R[i].
Proof. by rewrite normr1 divr1 normr1. Qed.

Definition angle0 := Angle angle0_subproof.

Canonical angle_subType := [subType for expi].

Lemma normr_expi a : `|expi a| = 1.
Proof. by case: a => x /= /eqP. Qed.

Lemma expi_eq0 a : (expi a == 0) = false.
Proof. case: a => /= a /eqP Ha; apply/negbTE; by rewrite -normr_gt0 Ha. Qed.

Definition arg (x : R[i]) : angle := insubd angle0 (x / `| x |). 

Lemma argZ x (k : R) : 0 < k -> arg (k %:C * x) = arg x.
Proof.
move=> k0; rewrite /arg; congr (insubd _ _).
rewrite normrM gtr0_norm; last by rewrite ltcR.
rewrite -mulf_div divff ?mul1r //.
by rewrite lt0r_neq0 // ltcR.
Qed.

Lemma argZ_neg x (k : R) : k < 0 -> arg (k %:C * x) = arg (- x).
Proof.
move=> k0; rewrite /arg; congr (insubd _ _).
rewrite normrM ltr0_norm; last by rewrite ltcR.
rewrite -mulf_div invrN mulrN divff ?mul1r; last by rewrite ltr0_neq0 // ltcR.
by rewrite mulNr mul1r normrN mulNr.
Qed.

Lemma expiK : cancel expi arg.
Proof.
move=> a; apply/val_inj=> /=.
by rewrite insubdK ?normr_expi ?divr1 // -topredE /= normr_expi.
Qed.

Lemma expi_arg x : x != 0 -> expi (arg x) = x / `|x|.
Proof.
move=> Nx_neq0; rewrite insubdK //.
by rewrite -topredE /= normrM normfV normr_id divff // normr_eq0.
Qed.

Lemma expi_conjc (a : R[i]) : a != 0 -> (expi (arg a))^-1 = expi (arg a^*).
Proof.
case: a => a b a0 /=; rewrite expi_arg // expi_arg //; last first.
  apply: contra a0 => a0; by rewrite -conjc_eq0.
rewrite invc_norm (_ : `| _ | = 1); last first.
  by rewrite normrM normrV ?unitfE ?normr_eq0 // normr_id divrr // unitfE normr_eq0.
rewrite exprnN exp1rz mul1r. simpc. by rewrite /= sqrrN.
Qed.

Lemma mul_norm_arg x : x = `|x| * expi (arg x).
Proof. 
have [x0|x_neq0] := boolP (x == 0); first by rewrite (eqP x0) normr0 mul0r.
by rewrite expi_arg // mulrC mulfVK // normr_eq0. 
Qed.

Lemma argK x : `|x| = 1 -> expi (arg x) = x.
Proof. by move=> Nx1; rewrite expi_arg ?Nx1 ?divr1 // -normr_gt0 Nx1. Qed.

Lemma arg_Re k : 0 < k -> arg k%:C = arg 1.
Proof.
move=> k0.
apply val_inj => /=.
rewrite expi_arg; last by rewrite lt0r_neq0 // ltcR.
rewrite ger0_norm; last by rewrite ler0c ler_eqVlt k0 orbC.
rewrite divff //; last by rewrite lt0r_neq0 // ltcR.
by rewrite argK // ger0_norm // ler01.
Qed.

Lemma arg_Re_neg k : k < 0 -> arg k%:C = arg (- 1).
Proof.
move=> k0.
apply val_inj => /=.
rewrite expi_arg; last by rewrite ltr0_neq0 // ltcR.
rewrite ltr0_norm; last by rewrite ltcR.
rewrite argK; last by rewrite normrN1.
by rewrite invrN mulrN divff // ltr0_neq0 // ltcR.
Qed.

Definition add_angle a b := arg (expi a * expi b).
Definition opp_angle a := arg (expi a)^-1.

Lemma add_angleA : associative add_angle.
Proof.
by move=> ???; rewrite /add_angle argK ?mulrA ?argK // ?normrM 2!normr_expi mulr1.
Qed.

Lemma add_angleC : commutative add_angle.
Proof. move=> a b; by rewrite /add_angle mulrC. Qed.

Lemma add_0angle x : add_angle (arg 1) x = x.
Proof. by rewrite /add_angle argK ?normr1 ?mul1r ?expiK. Qed.

Lemma expi_is_unit x : expi x \is a GRing.unit. 
Proof. by rewrite unitfE -normr_eq0 normr_expi oner_eq0. Qed.

Lemma add_Nangle x : add_angle (opp_angle x) x = arg 1.
Proof. 
rewrite /add_angle /opp_angle argK; first by rewrite mulVr // expi_is_unit.
by rewrite normrV ?expi_is_unit // normr_expi invr1.
Qed.

Definition angle_eqMixin := [eqMixin of angle by <:].
Canonical angle_eqType := EqType angle angle_eqMixin.
Definition angle_choiceMixin := [choiceMixin of angle by <:].
Canonical angle_choiceType := ChoiceType angle angle_choiceMixin.
Definition angle_ZmodMixin := ZmodMixin add_angleA add_angleC add_0angle add_Nangle.
Canonical angle_ZmodType := ZmodType angle angle_ZmodMixin.

Lemma add_angleE (a b : angle) : a + b = add_angle a b.
Proof. done. Qed.

Lemma opp_angleE (a : angle) : - a = opp_angle a.
Proof. done. Qed.

Lemma argc (z : R[i]) : z != 0 -> arg z^* = - arg z.
Proof.
case: z => a b z0 /=; by rewrite {2}/arg opp_angleE /opp_angle expi_conjc //= expiK.
Qed.

Definition pi := arg (-1).

Lemma expipi : expi pi = -1. Proof. by rewrite argK ?normrN1. Qed.

Definition pihalf := (arg (0 +i* 1) : angle).

Lemma arg1 : arg 1 = 0.
Proof. apply val_inj => /=; by rewrite argK // normr1. Qed.

Lemma argN1 : arg (- 1) = pi.
Proof. apply val_inj => /=; by rewrite argK // ?normrN1. Qed.

Lemma expi_inj : injective expi.
Proof. move=> [a a1] [b b1] /= ab; by apply/val_inj. Qed.

Lemma expiD a b : expi (a + b) = expi a * expi b.
Proof.
move: a b => [a a1] [b b1] /=.
by rewrite /add_angle /= argK // normrM  (eqP a1) (eqP b1) mulr1.
Qed.

Lemma expi2pi : expi (pi + pi) = 1.
Proof. by rewrite /pi expiD argK // ?normrN1 // mulrNN mulr1. Qed.

Lemma pi2 : pi *+ 2 = 0.
Proof. apply expi_inj => //; by rewrite expi2pi -arg1 argK // normr1. Qed.

Definition cos a := Re (expi a).
Definition sin a := Im (expi a).
Definition tan a := sin a / cos a.

Lemma sin_pihalf : sin pihalf = 1.
Proof.
have i1 : `|'i| = 1 :> R[i] by rewrite normc_def /= expr0n add0r expr1n sqrtr1.
rewrite /sin /pihalf expi_arg //.
by rewrite i1 divr1.
by rewrite -normr_eq0 i1 oner_neq0.
Qed.

Lemma cos_pihalf : cos pihalf = 0.
Proof.
have i1 : `|'i| = 1 :> R[i] by rewrite normc_def /= expr0n add0r expr1n sqrtr1.
rewrite /cos /pihalf expi_arg //.
by rewrite i1 divr1.
by rewrite -normr_eq0 i1 oner_neq0.
Qed.

Lemma cos2Dsin2 a : (cos a) ^+ 2 + (sin a) ^+ 2 = 1.
Proof.
move: (add_Re2_Im2 (expi a)).
by rewrite normr_expi expr1n => /(congr1 (@Re R)) => /= <-.
Qed.

Lemma sin2cos2 a : sin a ^+ 2 = 1 - cos a ^+ 2.
Proof. move/eqP: (cos2Dsin2 a); by rewrite eq_sym addrC -subr_eq => /eqP. Qed.

Lemma cos2sin2 a : cos a ^+ 2 = 1 - sin a ^+ 2.
Proof. move/eqP: (cos2Dsin2 a); by rewrite eq_sym -subr_eq => /eqP. Qed.

Lemma cos2_tan2 x : cos x != 0 -> 1 / (cos x) ^+ 2 = 1 + (tan x) ^+ 2.
Proof.
move=> cosx; rewrite /tan exprMn sin2cos2 mulrBl -exprMn divrr ?unitfE //.
by rewrite expr1n addrCA subrr addr0 div1r mul1r exprVn.
Qed.

Lemma expi_cos_sin a : expi a = cos a +i* sin a.
Proof. by case: a => -[a0 a1] Ha; rewrite /cos /sin. Qed.

Lemma sinD a b : sin (a + b) = sin a * cos b + cos a * sin b.
Proof. by rewrite {1}/sin expiD 2!expi_cos_sin /= addrC. Qed.

Lemma sin_mulr2n a : sin (a *+ 2) = (cos a * sin a) *+ 2.
Proof. by rewrite mulr2n sinD mulrC -mulr2n. Qed.

Lemma cosD a b : cos (a + b) = cos a * cos b - sin a * sin b.
Proof. by rewrite {1}/cos expiD 2!expi_cos_sin /= addrC. Qed.

Lemma cosN a : cos (- a) = cos a.
Proof.
case: a => -[a b] ab; rewrite opp_angleE /cos /opp_angle /=.
rewrite invc_norm (eqP ab) expr1n invr1 mul1r expi_arg; last first.
  by rewrite conjc_eq0 -normr_eq0 (eqP ab) oner_eq0.
by rewrite normcJ (eqP ab) divr1.
Qed.

Lemma sinN a : sin (- a) = - sin a.
Proof.
case: a => -[a b] ab; rewrite opp_angleE /sin /opp_angle /=.
rewrite invc_norm (eqP ab) expr1n invr1 mul1r expi_arg; last first.
  by rewrite conjc_eq0 -normr_eq0 (eqP ab) oner_eq0.
by rewrite normcJ (eqP ab) divr1.
Qed.

Lemma cosB a b : cos (a - b) = cos a * cos b + sin a * sin b.
Proof. by rewrite cosD cosN sinN mulrN opprK. Qed.

Lemma sinB a b : sin (a - b) = sin a * cos b - cos a * sin b.
Proof. by rewrite sinD cosN sinN mulrN. Qed.

Lemma cosDpihalf a : cos (a + pihalf) = - sin a.
Proof. by rewrite cosD cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma cosBpihalf a : cos (a - pihalf) = sin a.
Proof. by rewrite cosB cos_pihalf sin_pihalf mulr0 add0r mulr1. Qed.

Lemma sinBpihalf a : sin (a - pihalf) = - cos a.
Proof. by rewrite sinB cos_pihalf sin_pihalf mulr0 add0r mulr1. Qed.

Lemma expiNi : expi (- arg 'i) = -'i :> R[i].
Proof.
have i1 : `|'i| = 1 :> R[i] by rewrite normc_def /= expr0n add0r expr1n sqrtr1.
rewrite expi_cos_sin sinN cosN /cos /sin expi_arg; last by rewrite -normr_eq0 i1 oner_neq0.
rewrite i1 divr1 /=; apply/eqP; by rewrite eq_complex /= oppr0 2!eqxx.
Qed.

Lemma tanN x : tan (- x) = - tan x :> R.
Proof. by rewrite /tan sinN cosN mulNr. Qed.

Lemma cos0 : cos 0 = 1.
Proof. by rewrite /cos -arg1 argK // ger0_norm // ler01. Qed.

Lemma cos_max a : `| cos a | <= 1.
Proof.
rewrite -lecR (ler_trans (normc_ge_Re _)) //; by case: a => ? /= /eqP ->. 
Qed.

Lemma cos0_inv a : cos a = 0 -> a = pihalf \/ a = -pihalf.
Proof.
case: a => -[a b] ni; rewrite /cos /= => a0.
have [b1|b1] : b = 1 \/ b = - 1.
  move: ni.
  rewrite a0 normc_def /= expr0n add0r sqrtr_sqr eq_complex /= eqxx andbT.
  case: (lerP 0 b) => b0.
  + rewrite ger0_norm // => /eqP ->; by left.
  + rewrite ltr0_norm // eqr_oppLR => /eqP ->; by right.
- left; apply val_inj => /=;
  by rewrite /pihalf argK // ?a0 ?b1 // normc_def /= expr0n add0r expr1n sqrtr1.
- right; apply val_inj => /=.
  by rewrite /pihalf a0 b1 /= expiNi; apply/eqP; rewrite eq_complex /= oppr0 2!eqxx.
Qed.

Lemma sin0 : sin 0 = 0.
Proof.
by move/eqP: (sin2cos2 0); rewrite cos0 (expr2 1) mulr1 subrr sqrf_eq0 => /eqP.
Qed.

Lemma tan0 : tan 0 = 0 :> R.
Proof. by rewrite /tan sin0 cos0 mul0r. Qed.

Lemma abs_sin a : `| sin a | = Num.sqrt (1 - cos a ^+ 2).
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) //; last by rewrite sqrtr_ge0.
rewrite -normrX ger0_norm; last by rewrite sqr_ge0.
rewrite sqr_sqrtr; last first.
  by rewrite lter_sub_addr add0r -norm2 exprn_ilte1 // cos_max.
by rewrite -subr_eq opprK addrC cos2Dsin2.
Qed.

Lemma expi0 : expi 0 = 1.
Proof. by rewrite expi_cos_sin cos0 sin0. Qed.

Lemma expi_expr k a : expi a ^+ k = expi (a *+ k).
Proof.
elim: k => [|k ih]; by
  [rewrite expr0 mulr0n expi0 | rewrite exprS ih mulrS expiD].
Qed.

Lemma arg0_inv (x : R[i]) a : a != 0 -> `|x| = a -> arg x = 0 -> x = a.
Proof.
move=> a0; case: x => x y norma H.
rewrite -(mulr1 a) -expi0 -H expi_arg; last by rewrite -normr_eq0 norma.
by rewrite norma mulrCA divrr // mulr1.
Qed.

Lemma argpi_inv (x : R[i]) a : a != 0 -> `|x| = a -> arg x = pi -> x = -a.
Proof.
move=> a0; case: x => x y norma H.
rewrite -(mulrN1 a) -expipi -H expi_arg; last by rewrite -normr_eq0 norma.
by rewrite norma mulrCA divrr // mulr1.
Qed.

Lemma cos1_angle0 a : cos a = 1 -> a = 0.
Proof.
case: a; rewrite /cos /=; case => x y xy /= x1. 
have /eqP y0 : y == 0.
  move: xy; rewrite x1 normc_def /= expr1n eq_complex /= eqxx andbT.
  rewrite -(@eqr_expn2 _ 2%N) // ?ler01 //; last by rewrite sqrtr_ge0.
  rewrite sqr_sqrtr; last by apply addr_ge0 => //; rewrite ?ler01 // sqr_ge0.
  by rewrite expr1n eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0.
by apply val_inj => /=; rewrite x1 y0 expi0 complexr0.
Qed.

Lemma cosN1_angle0 a : cos a = -1 -> a = pi.
Proof.
case: a => a Ha; rewrite /cos /=; case: a Ha => x y xy /= x1. 
have y0 : y = 0.
  move: xy.
  rewrite x1 normc_def /= sqrrN expr1n eq_complex /= eqxx andbT.
  rewrite -(@eqr_expn2 _ 2%N) // ?ler01 //; last by rewrite sqrtr_ge0.
  rewrite sqr_sqrtr; last by apply addr_ge0 => //; rewrite ?ler01 // sqr_ge0.
  by rewrite expr1n eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
apply val_inj => /=; rewrite x1 y0 expipi complexr0.
by rewrite real_complexE; apply/eqP; rewrite eq_complex /= oppr0 2!eqxx.
Qed.

Lemma cos1sin0 a : cos a = 1 -> sin a = 0.
Proof.
case: a => -[a b] ab1; rewrite /cos /sin /= => a1; move: ab1.
rewrite {}a1 normc_def /= expr1n => /eqP[] /(congr1 (fun x => x ^+ 2)).
rewrite expr1n sqr_sqrtr; last by rewrite addr_ge0 // ?ler01 // sqr_ge0.
by move/eqP; rewrite eq_sym addrC -subr_eq subrr eq_sym sqrf_eq0 => /eqP.
Qed.

Lemma cos0sin1 a : cos a = 0 -> `| sin a | = 1.
Proof.
case: a => -[a b] ab1; rewrite /cos /sin /= => a1; move: ab1.
rewrite {}a1 normc_def /= expr0n add0r => /eqP[]; by rewrite sqrtr_sqr.
Qed.

Lemma sin0cos1 a : sin a = 0 -> `| cos a | = 1.
Proof.
case: a => -[a b] ab1; rewrite /cos /sin /= => a1; move: ab1.
rewrite {}a1 normc_def /= expr0n => /eqP[] /(congr1 (fun x => x ^+ 2)).
rewrite expr1n sqr_sqrtr; last by rewrite addr_ge0 // ?ler01 // sqr_ge0.
by move/eqP; rewrite addr0 -{1}(@expr1n _ 2%N) -norm2 eqr_expn2 // ?ler01 // => /eqP.
Qed.

(*
sin(t) = ( exp(it) - exp(-it) )/2i
cos(t) = ( exp(it) + exp(-it) )/2
*)

Definition asin (x : R) : angle := arg (Num.sqrt (1 - x^2) +i* x).
Definition acos (x : R) : angle := arg (x +i* Num.sqrt (1 - x^2)).
Definition atan (x : R) : angle := if x == 0 then 0 else arg ((x^-1 +i* 1) *~ sgz (x)).

Lemma atan0 : atan 0 = 0.
Proof. by rewrite /atan eqxx. Qed.

Lemma atanN x : - atan (- x) = atan x.
Proof.
rewrite /atan eqr_oppLR oppr0.
case: ifPn => [|x0]; first by rewrite oppr0.
rewrite -argc.
  congr arg; apply/eqP.
  rewrite sgzN mulrNz /= eq_complex /=.
  move: x0; rewrite neqr_lt => /orP [] x0.
    by rewrite ltr0_sgz // 2!mulrN1z opprK /= invrN 2!eqxx.
  by rewrite gtr0_sgz // 2!mulr1z /= invrN 2!opprK 2!eqxx.
move: x0; rewrite neqr_lt => /orP [] x0.
  by rewrite gtr0_sgz ?oppr_gt0 // mulr1z eq_complex /= negb_and oner_neq0 orbC.
rewrite ltr0_sgz -?oppr_gt0 ?opprK // mulrN1z eq_complex /= negb_and orbC.
by rewrite eqr_oppLR oppr0 oner_neq0.
Qed.

(* The following lemmas are true in specific domains only, such as
]-pi/2, pi/2[ = [pred a | cos a > 0] 
]0, pi[ = [pred a | sin a > 0] 
[-pi/2, pi/2[ = [pred a | cos a > 0] 
[0, pi] = [pred a | sin a >= 0] 
[0, pi[ = [pred a | sin a >= 0 && a != pi] 
*)

Definition Opi_closed := [pred a | 0 <= sin a].
Definition piO_closed := [pred a | sin a < 0].

(* ]-pi/2, pi/2[ *)
Definition Npi2pi2_open : pred angle := [pred a | cos a > 0].
Lemma Npi2pi2_openP a : (a \in Npi2pi2_open) = (0 < cos a).
Proof. by rewrite inE. Qed.

(*cancel acos cos*)
Lemma acosK (r : R) : -1 <= r <= 1 -> cos (acos r) = r.
Proof. 
move=> rdom; rewrite /acos /cos argK // normc_def /= sqr_sqrtr; last first.
  by rewrite subr_ge0 -ler_sqrt // ?ltr01 // sqrtr1 -exprnP sqrtr_sqr ler_norml.
by rewrite addrC subrK sqrtr1.
Qed.

(*cancel cos acos*)
Lemma cosK a : a \in Opi_closed -> acos (cos a) = a.
Proof.
rewrite inE => adoml; rewrite /acos /cos /= expi_cos_sin /= -sin2cos2. 
by rewrite sqrtr_sqr /= ger0_norm // -expi_cos_sin expiK.
Qed.

Lemma cosKN a : a \in piO_closed -> acos (cos a) = - a.
Proof.
rewrite inE => adoml; rewrite /acos /cos /= expi_cos_sin /= -sin2cos2.
rewrite sqrtr_sqr /= ltr0_norm //.
move: (expi_cos_sin (- a)); rewrite cosN sinN => <-; by rewrite expiK.
Qed.

(*cancel asin sin*)
Lemma asinK r : -1 <= r <= 1 -> sin (asin r) = r.
Proof.
move=> rdom; rewrite /sin /asin argK // normc_def /= sqr_sqrtr; last first.
  by rewrite subr_ge0 -ler_sqrt // ?ltr01 // sqrtr1 -exprnP sqrtr_sqr ler_norml.
by rewrite subrK sqrtr1.
Qed.

Lemma atan_in x : atan x \in Npi2pi2_open.
Proof.
case/boolP : (x == 0) => [/eqP ->|x0].
  by rewrite atan0 inE cos0 ltr01.
rewrite Npi2pi2_openP /atan (negbTE x0) /cos => [:myRe0].
rewrite expi_arg.
  rewrite normc_def => [:myltr0].
  rewrite Re_scale.
    rewrite divr_gt0 //.
      abstract: myRe0.
      move/ltr_total : x0 => /orP [] x0; last by rewrite gtr0_sgz //= invr_gt0.
      by rewrite ltr0_sgz //= ltr_oppr oppr0 invr_lt0.
   abstract: myltr0.
   rewrite -ltcR -normc_def normr_gt0 eq_complex /= negb_and.
   move/ltr_total : x0 => /orP [] x0; last by rewrite gtr0_sgz //= invr_eq0 gtr_eqF.
   by rewrite ltr0_sgz //= eqr_oppLR oppr0 invr_eq0 ltr_eqF.
 by rewrite gtr_eqF.
by rewrite eq_complex /= negb_and gtr_eqF.
Qed.

Lemma atanKpos x : 0 < x -> tan (atan x) = x.
Proof.
move=> x0; rewrite /atan gtr_eqF // gtr0_sgz // mulr1z /tan /sin /cos.
rewrite expi_arg /=; last by rewrite eq_complex /= negb_and oner_neq0 orbT.
rewrite mul0r oppr0 mulr0 add0r mulr0 subr0 expr0n addr0 expr1n.
rewrite sqr_sqrtr; last by rewrite addr_ge0 // ?ler01 // sqr_ge0.
set y := Num.sqrt _ / _; move=> [:yunit].
rewrite mul1r invrM; last 2 first.
  by rewrite unitrV unitfE gtr_eqF. 
  abstract: yunit.
  rewrite unitfE /y mulf_eq0 negb_or sqrtr_eq0 -ltrNge invr_eq0.
  move=> [:x2D1]; apply/andP; split.
    abstract: x2D1.
    by rewrite addr_gt0 // ?ltr01 // exprn_even_gt0 //= invr_eq0 gtr_eqF.
  by rewrite gtr_eqF.
by rewrite mulrA divrr // invrK mul1r.
Qed.

Lemma atanKneg x : x < 0 -> tan (atan x) = x.
Proof.
rewrite -oppr_gt0 => x0; rewrite /atan ltr_eqF -?oppr_gt0 //.
move/eqP: (atanKpos x0); rewrite -eqr_oppLR => /eqP H.
by rewrite -{3}H {H} -[in RHS]tanN atanN /atan ltr_eqF // -oppr_gt0.
Qed.

Lemma atanK x : tan (atan x) = x.
Proof.
case: (lerP 0 x); last by apply atanKneg.
rewrite ler_eqVlt => /orP [/eqP <-|]; by [rewrite atan0 tan0 | apply atanKpos].
Qed.

Lemma sin_atan2 (x : R) : sin (atan x) ^+ 2 = x ^+ 2 / (1 + x ^+ 2).
Proof.
case/boolP : (x == 0) => [/eqP ->|x0].
  by rewrite atan0 sin0 expr0n /= mul0r.
rewrite sin2cos2.
apply/eqP; rewrite -eqr_opp opprB subr_eq; apply/eqP.
rewrite -mulNr.
have /divrr H : 1 + x ^+ 2 \in GRing.unit.
  by rewrite unitfE gtr_eqF // -(addr0 0) ltr_le_add // ?ltr01 // sqr_ge0.
rewrite -{2}H {H} addrC mulNr -mulrBl -invf_div -[LHS]invrK; congr (_ ^-1).
rewrite -exprVn -div1r expr_div_n expr1n cos2_tan2.
  by rewrite atanK addrK divr1.
by rewrite gtr_eqF // -Npi2pi2_openP atan_in.
Qed.

Lemma sin_atan_ltr0 (x : R) : x < 0 -> sin (atan x) < 0.
Proof.
move=> x0.
rewrite /sin /atan ltr_eqF // ltr0_sgz // mulrN1z /= expi_arg //=.
  rewrite expr0n addr0 mul0r oppr0 mulr0 add0r.
  rewrite sqr_sqrtr; last by rewrite addr_ge0 // sqr_ge0.
  rewrite pmulr_llt0; first by rewrite oppr_lt0 ltr01.
  rewrite (sqrrN 1) expr1n divr_gt0 //.
    rewrite sqrtr_gt0 addr_gt0 // ?ltr01 //.
    by rewrite exprn_gt0 // oppr_gt0 invr_lt0.
  by rewrite addr_gt0 // ?ltr01 // exprn_gt0 // oppr_gt0 invr_lt0.
by rewrite eq_complex /= negb_and /= orbC eqr_oppLR oppr0 oner_eq0.
Qed.

Lemma sin_atan_gtr0 (x : R) : 0 < x -> 0 < sin (atan x).
Proof.
move=> x0.
by rewrite -atanN sinN -oppr_lt0 opprK sin_atan_ltr0 // oppr_lt0.
Qed.

Lemma sin_atan (x : R) : sin (atan x) = x / Num.sqrt (1 + x ^+ 2).
Proof.
apply/eqP.
case/boolP : (x == 0) => [/eqP ->|].
  by rewrite atan0 sin0 mul0r.
move/ltr_total => /orP [] x0.
  rewrite -eqr_opp -(@eqr_expn2 _ 2) //; last 2 first.
    move/sin_atan_ltr0 : x0; by rewrite oppr_ge0 => /ltrW.
    by rewrite -mulNr divr_ge0 // ?sqrtr_ge0 // oppr_ge0 ltrW.
  by rewrite 2!sqrrN sin_atan2 exprMn exprVn sqr_sqrtr // addr_ge0 // ?ler01 // sqr_ge0.
rewrite -(@eqr_expn2 _ 2) //; last 2 first.
  by rewrite ltrW // sin_atan_gtr0.
  by rewrite mulr_ge0 // ?invr_ge0 ?sqrtr_ge0 // ltrW.
by rewrite sin_atan2 exprMn exprVn sqr_sqrtr // addr_ge0 // ?ler01 // sqr_ge0.
Qed.

Lemma sin_acos x : `|x| <= 1 -> sin (acos x) = Num.sqrt (1 - x ^ 2).
Proof.
move=> Nx_le1; rewrite /sin /acos argK //; simpc; rewrite sqr_sqrtr.
  by rewrite addrC addrNK sqrtr1.
by rewrite subr_ge0 -[_ ^ _]real_normK ?num_real // exprn_ile1.
Qed.

Lemma cos_atan x : atan x \in Npi2pi2_open -> cos (atan x) = 1 / Num.sqrt (1 + x ^+ 2).
Proof.
rewrite Npi2pi2_openP ltr_neqAle => /andP [H1 H2].
move: (H1); rewrite eq_sym; move/cos2_tan2.
rewrite atanK => <-.
rewrite sqrtrM ?ler01 // sqrtr1 2!mul1r.
rewrite -exprVn sqrtr_sqr ger0_norm; by [rewrite invrK | rewrite invr_ge0].
Qed.

Lemma moivre n a : (cos a +i* sin a) ^+n = cos (a *+ n) +i* sin (a *+ n).
Proof.
rewrite -!expi_cos_sin.
elim: n => [|n ih]; by [rewrite expr0 mulr0n expi0 | rewrite expi_expr].
Qed.

Lemma Re_half_anglec (x : R[i]) : `|x| = 1 -> 0 <= 1 + Re x.
Proof.
move=> x1; rewrite -ler_subl_addr add0r.
suff : `| Re x |%:C <= `|x|; last by rewrite normc_ge_Re.
rewrite x1 -lecR; apply: ler_trans; by rewrite lecR ler_normr lerr orbT.
Qed.

Lemma Im_half_anglec (x : R[i]) : `|x| = 1 -> Re x <= 1.
Proof.
move=> x1; suff : `| Re x |%:C <= `|x|; last by rewrite normc_ge_Re.
rewrite x1 -lecR; apply: ler_trans; by rewrite lecR ler_normr lerr.
Qed.

Lemma eq_angle (a b : angle) : (a == b) = ((cos a == cos b) && (sin a == sin b)).
Proof.
case: a b => [[a b] ab] [[c d] cd].
rewrite /cos /= /sin /=.
apply/idP/idP; first by case/eqP => -> ->; rewrite 2!eqxx.
case/andP => /eqP ac /eqP bd.
apply/eqP/val_inj => /=; by rewrite ac bd.
Qed.

Definition half_anglec (x : R[i]) :=
  if 0 <= Im x then 
    Num.sqrt ((1 + Re x) / 2%:R) +i* Num.sqrt ((1 - Re x) / 2%:R)
  else
    Num.sqrt ((1 + Re x) / 2%:R) -i* Num.sqrt ((1 - Re x) / 2%:R).

Lemma norm_half_anglec (x : R[i]) : `|x| = 1 -> `|half_anglec x| == 1.
Proof.
move=> x1.
rewrite /half_anglec.
case: ifP => a0.
  rewrite normc_def /= sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // Re_half_anglec.
  rewrite sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
  by rewrite mulrC (mulrC (1 - Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatr_is_a_unit // sqrtr1.
rewrite normc_def /= sqr_sqrtr; last first.
  by rewrite divr_ge0 // ?Re_half_anglec // ler0n.
rewrite sqrrN sqr_sqrtr; last first.
  by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
by rewrite mulrC (mulrC (1 - Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatr_is_a_unit // sqrtr1.
Qed.

Definition half_angle (x : angle) := Angle (norm_half_anglec (normr_expi x)).

Lemma halfP (a : angle) : half_angle a + half_angle a = a.
Proof.
apply/eqP.
rewrite eq_angle; apply/andP; split.
  rewrite /cos /= add_angleE /add_angle /half_angle /= argK; last first.
    by rewrite normrM (eqP (norm_half_anglec (normr_expi _))) mulr1.
  rewrite /half_anglec. simpc. rewrite /=.
  move=> [:tmp].
  case: ifP => a0 /=.
    abstract: tmp.
    rewrite -2!expr2 sqr_sqrtr; last first.
      by rewrite divr_ge0 // ?Re_half_anglec // ?normr_expi // ler0n.
    rewrite sqr_sqrtr; last first.
      by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec // normr_expi.
    rewrite mulrC (mulrC (_ - _)) -mulrBr opprB addrC addrA subrK -mulr2n.
    by rewrite -(mulr_natl (Re _)) mulrA mulVr ?pnatr_is_a_unit // mul1r eqxx.
  rewrite mulNr mulrN opprK; exact: tmp.
rewrite /sin /= add_angleE /add_angle /half_angle /= argK; last first.
  by rewrite normrM (eqP (norm_half_anglec (normr_expi _))) mulr1.
rewrite /half_anglec. simpc. rewrite /=.
case: ifPn => a0 /=.
  rewrite mulrC -mulr2n -mulr_natl sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
  rewrite mulrAC sqrtrM; last by rewrite Re_half_anglec // normr_expi.
  rewrite -!mulrA -sqrtrM; last by rewrite invr_ge0 ler0n.
  rewrite -expr2 sqrtr_sqr !mulrA mulrC normrV ?unitfE ?pnatr_eq0 //.
  rewrite normr_nat !mulrA mulVr ?mul1r ?unitfE ?pnatr_eq0 //.
  rewrite -sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
  rewrite -subr_sqr expr1n.
  rewrite -(@eqr_expn2 _ 2%N) //; last by rewrite sqrtr_ge0.
  by rewrite -sin2cos2 sqr_sqrtr // sqr_ge0.
rewrite mulrN mulNr -opprB opprK eqr_oppLR.
rewrite mulrC -mulr2n -mulr_natl sqrtrM; last by rewrite Re_half_anglec // normr_expi.
rewrite mulrAC sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
rewrite -!mulrA -sqrtrM; last by rewrite invr_ge0 ler0n.
rewrite -expr2 sqrtr_sqr !mulrA mulrC normrV ?unitfE ?pnatr_eq0 //.
rewrite normr_nat !mulrA mulVr ?mul1r ?unitfE ?pnatr_eq0 //.
rewrite -sqrtrM; last by rewrite Re_half_anglec // normr_expi.
rewrite mulrC -subr_sqr expr1n.
rewrite -(@eqr_expn2 _ 2%N) //; last 2 first.
  by rewrite sqrtr_ge0.
  by rewrite ltrW // oppr_gt0 ltrNge.
by rewrite -sin2cos2 sqrrN sqr_sqrtr // sqr_ge0.
Qed.

Definition vec_angle v w : angle := arg (v *d w +i* norm (v *v w)).

Lemma vec_anglev0 v : vec_angle v 0 = vec_angle 0 0.
Proof. by rewrite /vec_angle 2!dotmulv0 2!crossmulv0. Qed.

Lemma vec_angle0v v : vec_angle 0 v = vec_angle 0 0.
Proof. by rewrite /vec_angle 2!dotmul0v 2!crossmul0v. Qed.

Definition vec_angle0 := (vec_anglev0, vec_angle0v).

Lemma cos_vec_angleNv v w : v != 0 -> w != 0 ->
  cos (vec_angle (- v) w) = - cos (vec_angle v w).
Proof.
move=> a0 b0.
rewrite /vec_angle /cos crossmulNv normN expi_arg; last first.
  rewrite eq_complex /= negb_and.
  case/boolP : (v *d w == 0) => ab; last by rewrite dotmulNv oppr_eq0 ab.
  by rewrite dotmulNv (eqP ab) oppr0 eqxx /= norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite expi_arg; last first.
  rewrite eq_complex /= negb_and.
  by case/boolP : (_ == 0) => ab //=; rewrite norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite (_ : `|- v *d w +i* _| = `|v *d w +i* norm (v *v w)|); last first.
  by rewrite 2!normc_def /= dotmulNv sqrrN.
by rewrite /= mul0r oppr0 mulr0 subr0 expr0n /= addr0 subr0 dotmulNv mulNr.
Qed.

Lemma cos_vec_anglevN v w : v != 0 -> w != 0 ->
  cos (vec_angle v (- w)) = - cos (vec_angle v w).
Proof.
move=> a0 b0.
rewrite /vec_angle /cos crossmulC crossmulNv opprK dotmulvN.
rewrite [in LHS]expi_arg; last first.
  rewrite eq_complex /= negb_and.
  case/boolP : (v *d w == 0) => vw; rewrite oppr_eq0 vw //=.
  by rewrite norm_eq0 dotmul_eq0_crossmul_neq0 // dotmulC.
rewrite expi_arg; last first.
  rewrite eq_complex /= negb_and.
  by case/boolP : (_ == 0) => ab //=; rewrite norm_eq0 dotmul_eq0_crossmul_neq0.
rewrite (_ : `| _ +i* norm (w *v _)| = `|v *d w +i* norm (v *v w)|); last first.
  by rewrite 2!normc_def /= sqrrN crossmulC normN.
by rewrite /= mul0r oppr0 mulr0 expr0n /= addr0 subr0 mulr0 subr0 mulNr.
Qed.

Lemma vec_angleC v w : vec_angle v w = vec_angle w v.
Proof. by rewrite /vec_angle dotmulC crossmulC normN. Qed.

Lemma vec_angleZ u v k : 0 < k -> vec_angle u (k *: v) = vec_angle u v.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0 k0]; first by rewrite scaler0 !vec_angle0.
by rewrite /vec_angle dotmulvZ linearZ normZ ger0_norm ?ltrW // complexZ argZ.
Qed.

Lemma vec_angleZ_neg u v k : k < 0 -> vec_angle u (k *: v) = vec_angle (- u) v.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite oppr0 !vec_angle0.
case/boolP : (v == 0) => [/eqP ->|v0 k0]; first by rewrite scaler0 !vec_angle0.
rewrite /vec_angle dotmulvZ linearZ /= normZ ltr0_norm //.
by rewrite mulNr complexZ argZ_neg // opp_conjc dotmulNv crossmulNv normN.
Qed.

Lemma vec_anglevv u : u != 0 -> vec_angle u u = 0.
Proof.
move=> u0.
rewrite /vec_angle /= crossmulvv norm0 complexr0 dotmulvv arg_Re ?arg1 //.
by rewrite ltr_neqAle sqr_ge0 andbT eq_sym sqrf_eq0 norm_eq0.
Qed.

Lemma polarization_identity (v w : 'rV[R]_3) :
  v *d w = 1 / 4%:R * (norm (v + w) ^+ 2 - norm (v - w) ^+ 2).
Proof.
apply: (@mulrI _ 4%:R); first exact: pnatr_is_a_unit.
rewrite [in RHS]mulrA div1r divrr ?pnatr_is_a_unit // mul1r.
rewrite -2!dotmulvv dotmulD dotmulD mulr_natl (addrC (v *d v)).
rewrite (_ : 4 = 2 + 2)%N // mulrnDr -3![in RHS]addrA; congr (_ + _).
rewrite opprD addrCA 2!addrA -(addrC (v *d v)) subrr add0r.
by rewrite addrC opprD 2!dotmulvN dotmulNv opprK subrK -mulNrn opprK.
Qed.

Lemma dotmul_cos u v : u *d v = norm u * norm v * cos (vec_angle u v).
Proof.
wlog /andP[u0 v0] : u v / (u != 0) && (v != 0).
  case/boolP : (u == 0) => [/eqP ->{u}|u0]; first by rewrite dotmul0v norm0 !mul0r.
  case/boolP : (v == 0) => [/eqP ->{v}|v0]; first by rewrite dotmulv0 norm0 !(mulr0,mul0r).
  apply; by rewrite u0.
rewrite /vec_angle /cos. set x := _ +i* _.
case/boolP  : (x == 0) => [|x0].
  rewrite eq_complex /= => /andP[/eqP H1 H2].
  exfalso.
  move: H2; rewrite norm_eq0 => /crossmul0_dotmul/esym.
  rewrite H1 expr0n (_ : (_ == _)%:R = 0) // => /eqP.
  by rewrite 2!dotmulvv mulf_eq0 2!expf_eq0 /= 2!norm_eq0 (negbTE u0) (negbTE v0).
case/boolP : (u *d v == 0) => uv0.
  by rewrite (eqP uv0) expi_arg //= (eqP uv0) !mul0r -mulrN opprK mulr0 addr0 mulr0.
rewrite expi_arg //.
rewrite normc_def Re_scale; last first.
  rewrite sqrtr_eq0 -ltrNge -(addr0 0) ltr_le_add //.
    by rewrite exprnP /= ltr_neqAle sqr_ge0 andbT eq_sym -exprnP sqrf_eq0.
  by rewrite /= sqr_ge0.
rewrite /=.
rewrite norm_crossmul' addrC subrK sqrtr_sqr ger0_norm; last first.
  by rewrite mulr_ge0 // norm_ge0.
rewrite mulrA mulrC mulrA mulVr ?mul1r //.
by rewrite unitrMl // unitfE norm_eq0.
Qed.

Lemma dotmul0_vec_angle u v : u != 0 -> v != 0 -> 
  u *d v = 0 -> `| sin (vec_angle u v) | = 1.
Proof.
move=> u0 v0 /eqP.
rewrite dotmul_cos mulf_eq0 => /orP [ | /eqP/cos0sin1 //].
by rewrite mulf_eq0 2!norm_eq0 (negbTE u0) (negbTE v0).
Qed.

Lemma normD a b : norm (a + b) = 
  Num.sqrt (norm a ^+ 2 + norm a * norm b * cos (vec_angle a b) *+ 2 + norm b ^+ 2).
Proof.
rewrite /norm dotmulD {1}dotmulvv sqr_sqrtr ?le0dotmul //.
by rewrite sqr_sqrtr ?le0dotmul // (dotmul_cos a b).
Qed.

Lemma normB a b : norm (a - b) = 
  Num.sqrt (norm a ^+ 2 + norm a * norm b * cos (vec_angle a b) *- 2 + norm b ^+ 2).
Proof.
rewrite /norm dotmulD {1}dotmulvv sqr_sqrtr ?le0dotmul //.
rewrite sqr_sqrtr ?le0dotmul // !dotmulvv !sqrtr_sqr normN dotmulvN dotmul_cos.
by rewrite ger0_norm ?norm_ge0 // ger0_norm ?norm_ge0 // mulNrn.
Qed.

Lemma cosine_law' a b c :
  norm (b - c) ^+ 2 = norm (c - a) ^+ 2 + norm (b - a) ^+ 2 -
  norm (c - a) * norm (b - a) * cos (vec_angle (b - a) (c - a)) *+ 2.
Proof.
rewrite -[in LHS]dotmulvv (_ : b - c = b - a - (c - a)); last first.
  by rewrite -!addrA opprB (addrC (- a)) (addrC a) addrK.
rewrite dotmulD dotmulvv [in X in _ + _ + X = _]dotmulvN dotmulNv opprK.
rewrite dotmulvv dotmulvN addrAC (addrC (norm (b - a) ^+ _)); congr (_ + _).
by rewrite dotmul_cos mulNrn (mulrC (norm (b - a))).
Qed.

Lemma cosine_law a b c : norm (c - a) != 0 -> norm (b - a) != 0 ->
  cos (vec_angle (b - a) (c - a)) = 
  (norm (b - c) ^+ 2 - norm (c - a) ^+ 2 - norm (b - a) ^+ 2) /
  (norm (c - a) * norm (b - a) *- 2).
Proof.
move=> H0 H1.
rewrite (cosine_law' a b c) -2!addrA addrCA -opprD subrr addr0.
rewrite -mulNrn -mulr_natr mulNr -mulrA -(mulrC 2%:R) mulrA.
rewrite -mulNrn -[in X in _ = - _ / X]mulr_natr 2!mulNr invrN mulrN opprK.
rewrite mulrC mulrA mulVr ?mul1r // unitfE mulf_eq0 negb_or pnatr_eq0 andbT.
by rewrite mulf_eq0 negb_or H0 H1.
Qed.

Lemma norm_crossmul u v : 
  norm (u *v v) = norm u * norm v * `| sin (vec_angle u v) |.
Proof.
suff /eqP : (norm (u *v v))^+2 = (norm u * norm v * `| sin (vec_angle u v) |)^+2.
  rewrite -eqr_sqrt ?sqr_ge0 // 2!sqrtr_sqr ger0_norm; last by rewrite norm_ge0.
  rewrite ger0_norm; first by move/eqP.
  by rewrite -mulrA mulr_ge0 // ?norm_ge0 // mulr_ge0 // ? norm_ge0.
rewrite norm_crossmul' dotmul_cos !exprMn.
apply/eqP; rewrite subr_eq -mulrDr.
rewrite real_normK; first by rewrite addrC cos2Dsin2 mulr1.
rewrite /sin; case: (expi _) => a b /=; rewrite realE //.
case: (lerP 0 b) => //= b0; by rewrite ltrW.
Qed.

Lemma norm_dotmul_crossmul (u v : 'rV[R]_3) : u != 0 -> v != 0 ->
  `|u *d v +i* norm (u *v v)| = (norm u * norm v)%:C.
Proof.
move=> u0 v0 .
rewrite {1}dotmul_cos {1}norm_crossmul normc_def.
rewrite exprMn (@exprMn _ 2 _ `| sin _ |) -mulrDr.
rewrite sqrtrM ?sqr_ge0 // norm2 cos2Dsin2 sqrtr1 mulr1.
rewrite sqrtr_sqr normrM; by do 2 rewrite ger0_norm ?norm_ge0 //.
Qed.

Lemma vec_angle0_inv u v : u != 0 -> v != 0 ->
  vec_angle u v = 0 -> u = (norm u / norm v) *: v.
Proof.
move=> u1 v1; rewrite /vec_angle => uv.
move: (norm_dotmul_crossmul u1 v1) => /arg0_inv/(_ uv)/eqP.
rewrite eq_complex {1}rmorphM /= mulf_eq0 negb_or.
rewrite eq_complex /= eqxx norm_eq0 andbT u1 eq_complex eqxx norm_eq0 andbT v1.
move/(_ isT) => /andP[].
rewrite dotmul_cos -{2}(mulr1 (norm u * norm v)); move/eqP/mulrI.
rewrite unitfE mulf_eq0 negb_or 2!norm_eq0 u1 v1 => /(_ isT) => uv1 ?.
apply/eqP; rewrite -subr_eq0 -norm_eq0 normB vec_angleZ; last first.
  by rewrite divr_gt0 // lt0r norm_ge0 norm_eq0 ?u1 ?v1.
rewrite uv1 mulr1 !normZ ger0_norm; last by rewrite divr_ge0 // norm_ge0.
by rewrite -!mulrA mulVr ?unitfE // ?norm_eq0 // mulr1 -expr2 addrAC -mulr2n subrr sqrtr0.
Qed.

Lemma vec_anglepi_inv u v : u != 0 -> v != 0 ->
  vec_angle u v = pi -> u = - (norm u / norm v) *: v.
Proof.
move=> u1 v1; rewrite /vec_angle => uv.
move: (norm_dotmul_crossmul u1 v1) => /argpi_inv/(_ uv)/eqP.
rewrite eq_complex {1}rmorphM /= mulf_eq0 negb_or.
rewrite eq_complex /= eqxx andbT norm_eq0 u1 eq_complex /= eqxx andbT norm_eq0 v1.
move/(_ isT) => /andP[].
rewrite dotmul_cos -{1}(mulrN1 (norm u * norm v)).
move/eqP/mulrI; rewrite unitfE mulf_eq0 negb_or 2!norm_eq0 u1 v1.
move/(_ isT) => uv1 ?.
apply/eqP; rewrite -subr_eq0 -norm_eq0 normB vec_angleZ_neg; last first.
  by rewrite oppr_lt0 divr_gt0 // lt0r norm_ge0 norm_eq0 ?u1 ?v1.
rewrite scaleNr normN cos_vec_angleNv // uv1 opprK.
rewrite mulr1 !normZ ger0_norm; last by rewrite divr_ge0 // norm_ge0.
by rewrite -!mulrA mulVr ?unitfE // ?norm_eq0 // mulr1 -expr2 addrAC -mulr2n subrr sqrtr0.
Qed.

Lemma dotmul1_inv (u v : 'rV[R]_3) : norm u = 1 -> norm v = 1 -> u *d v = 1 -> u = v.
Proof.
move=> u1 v1; rewrite dotmul_cos u1 v1 2!mul1r => /cos1_angle0/vec_angle0_inv.
rewrite -2!norm_eq0 u1 v1 oner_neq0 div1r invr1 scale1r; by apply.
Qed.

Lemma dotmulN1_inv (u v : 'rV[R]_3) : norm u = 1 -> norm v = 1 -> u *d v = - 1 -> u = - v.
Proof.
move=> u1 v1; rewrite dotmul_cos u1 v1 2!mul1r => /cosN1_angle0/vec_anglepi_inv.
rewrite -2!norm_eq0 u1 v1 oner_neq0 div1r invr1 scaleN1r; by apply.
Qed.

Lemma cos_vec_angle a b : a != 0 -> b != 0 ->
  `| cos (vec_angle a b) | = Num.sqrt (1 - (norm (a *v b) / (norm a * norm b)) ^+ 2).
Proof.
move=> Ha Hb.
rewrite norm_crossmul mulrAC divrr // ?mul1r.
  by rewrite norm2 -cos2sin2 sqrtr_sqr.
by rewrite unitfE mulf_neq0 // norm_eq0.
Qed.

Lemma orth_preserves_vec_angle M v w : M \is 'O_3[R] ->
  vec_angle v w = vec_angle (v *m M) (w *m M).
Proof.
move=> MO; move/(proj2 (orth_preserves_dotmul _))/(_ v w) : (MO).
by rewrite /vec_angle => ->; rewrite -orth_preserves_norm_crossmul.
Qed.

End angle.

Lemma norm2_cossin {R : rcfType} (v :'rV[R]_2) :
  norm v = 1 -> exists a, v 0 0 = cos a /\ v 0 1 = sin a.
Proof.
move=> v1.
have {v1}v1 : `| v 0 0 +i* v 0 1 | = 1 by rewrite normc_def /= -sqr_norm2 sqrtr_sqr v1 normr1.
exists (arg (v 0 0 +i* v 0 1)); split.
  rewrite /cos expi_arg //; last by rewrite -normr_eq0 v1 oner_neq0.
  by rewrite v1 divr1.
rewrite /sin expi_arg //; last by rewrite -normr_eq0 v1 oner_neq0.
by rewrite v1 divr1.
Qed.

Definition RO {R : rcfType} (a : angle R) :=
  double_prod_mat (row2 (cos a) (- sin a)) (row2 (sin a) (cos a)).

Lemma tr_RO {R : rcfType} (a : angle R) : \tr (RO a) = (cos a) *+ 2.
Proof. by rewrite /mxtrace sum2E !mxE /= mulr2n. Qed.

Lemma RO_is_O {R : rcfType} (a : angle R) : RO a \is 'O_2[R].
Proof.
apply/orthogonalP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite dotmulE sum2E !mxE /= mulrN mulNr opprK -2!expr2 cos2Dsin2.
  rewrite ifnot01 => /eqP ->; by rewrite dotmulE sum2E !mxE /= mulNr mulrC subrr.
rewrite ifnot01 => /eqP ->.
case/boolP : (j == 0) => [/eqP ->|]; first by rewrite dotmulE sum2E !mxE /= mulrN mulrC subrr.
rewrite ifnot01 => /eqP ->; by rewrite dotmulE sum2E !mxE /= addrC -2!expr2 cos2Dsin2.
Qed.

Lemma RO_is_SO {R : rcfType} (a : angle R) : RO a \is 'SO_2[R].
Proof.
by rewrite rotationE RO_is_O /= det_mx22 !mxE /= mulNr opprK -2!expr2 cos2Dsin2.
Qed.

Lemma rot2d {R : rcfType} (M : 'M[R]_2) : M \is 'SO_2[R] ->
  exists a : angle R, M = RO a /\ (a \in piO_closed R \/ a \in Opi_closed R).
Proof.
move=> MSO.
move: (MSO); rewrite rotationE => /andP[MO _].
case: (norm2_cossin (norm_row_of_O MO 0)); rewrite !mxE => a [a1 a2].
case: (norm2_cossin (norm_row_of_O MO 1)); rewrite !mxE => b [b1 b2].
move/orthogonalP : (MO) => /(_ 0 1) /=.
rewrite dotmulE sum2E !mxE a1 a2 b1 b2 -cosB.
case/cos0_inv => abpi.
  exfalso.
  move/rotation_det : MSO.
  rewrite det_mx22 a1 a2 b1 b2 mulrC -(mulrC (cos b)) -sinB => /esym/eqP.
  rewrite -eqr_opp -sinN opprB abpi sin_pihalf -subr_eq0.
  by rewrite -opprD eqr_oppLR oppr0 -(natrD _ 1 1) pnatr_eq0.
have Hsinb : sin b = cos a.
  by move/eqP : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC cosBpihalf.
have Hcosb : cos b = - sin a.
  by move/eqP : (abpi); rewrite subr_eq => /eqP ->; rewrite addrC sinBpihalf opprK.
rewrite {}Hsinb in b2.
rewrite {}Hcosb {abpi b} in b1.
case: (ltrP 0 (sin a)) => sa_ge0.
  exists (- a); split; last first.
    left; by rewrite inE sinN ltr_oppl oppr0.
  apply/matrixP => i j.
  rewrite !mxE /=.
  case: ifPn => [/eqP ->|]; first rewrite !mxE /=.
    case: ifPn => [/eqP ->|]; first by rewrite a1 cosN.
    rewrite ifnot01 => /eqP -> /=; by rewrite a2 sinN opprK.
  rewrite ifnot01 => /eqP -> /=; rewrite !mxE /=.
  case: ifPn => [/eqP ->|]; first by rewrite b1 sinN.
  rewrite ifnot01 => /eqP -> /=; by rewrite b2 cosN.
exists (- a); split; last first.
  right; by rewrite inE sinN lter_oppE.
apply/matrixP => i j.
rewrite !mxE /=.
case: ifPn => [/eqP ->|]; first rewrite !mxE /=.
  case: ifPn => [/eqP -> //|].
  by rewrite cosN.
  rewrite ifnot01 => /eqP -> /=.
  by rewrite sinN opprK.
rewrite ifnot01 => /eqP -> /=; rewrite !mxE /=.
case: ifPn => [/eqP ->|].
  by rewrite sinN.
rewrite ifnot01 => /eqP -> /=.
by rewrite cosN.
Qed.

Lemma tr_SO2 {R : rcfType} (P : 'M[R]_2) : P \is 'SO_2[R] -> `|\tr P| <= 2%:R.
Proof.
case/rot2d => a [PRO _]; move: (cos_max a) => ca.
rewrite PRO tr_RO -(mulr_natr (cos a)) normrM normr_nat.
by rewrite -[in X in _ <= X]mulr_natr ler_pmul.
Qed.

Section colinear.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Type u v : vector.

Definition colinear u v := u *v v == 0.

Lemma scale_colinear k v : colinear (k *: v) v.
Proof. by rewrite /colinear crossmulC linearZ /= crossmulvv scaler0 oppr0. Qed.

Lemma colinear_refl : reflexive colinear.
Proof. move=> ?; by rewrite /colinear crossmulvv. Qed.

Lemma colinear0 u : colinear 0 u.
Proof. by rewrite /colinear crossmul0v. Qed.

Lemma colinear_sym : symmetric colinear.
Proof. by move=> u v; rewrite /colinear crossmulC -eqr_opp opprK oppr0. Qed.

Lemma colinear_trans v u w : u != 0 -> colinear v u -> colinear u w -> colinear v w.
Proof.
move=> u0.
rewrite /colinear => vu0 uw0.
move: (jacobi u v w).
rewrite (crossmulC u v) (eqP vu0) oppr0 crossmulv0 addr0.
rewrite (crossmulC w u) (eqP uw0) oppr0 crossmulv0 addr0.
rewrite double_crossmul => /eqP; rewrite subr_eq0.
case/boolP : (v == 0) => [/eqP ->|v0]; first by rewrite crossmul0v.
case/boolP : (w == 0) => [/eqP ->|w0]; first by rewrite crossmulv0.
have uw0' : u *d w != 0.
  apply: contraL uw0.
  by apply dotmul_eq0_crossmul_neq0.
move/eqP/(congr1 (fun x => (u *d w)^-1 *: x )).
rewrite scalerA mulVr // ?unitfE // scale1r => ->.
by rewrite scalerA crossmulC linearZ /= crossmulvv scaler0 oppr0.
Qed.

Lemma colinearZ1 u v k : colinear u v -> colinear (k *: u) v.
Proof.
rewrite /colinear => uv.
by rewrite /colinear crossmulC linearZ /= crossmulC (eqP uv) oppr0 scaler0 oppr0.
Qed.

Lemma colinearZ2 u v k : k != 0 -> colinear (k *: u) v -> colinear u v.
Proof.
move=> k0; rewrite /colinear.
by rewrite crossmulC linearZ /= crossmulC scalerN opprK scalemx_eq0 (negbTE k0).
Qed.

Lemma colinearP u v :
  reflect (v == 0 \/
           (v != 0 /\ exists k, `| k | = norm u / norm v /\ u = k *: v))
          (colinear u v).
Proof.
apply: (iffP idP); last first.
  case => [/eqP ->|]; first by rewrite colinear_sym colinear0.
  case => v0 [k [k0 ukv]].
  by rewrite /colinear ukv crossmulC linearZ /= crossmulvv scaler0 oppr0.
rewrite /colinear => uv.
case/boolP : (v == 0) => v0; [by left | right; split; first by done].
case/boolP : (u == 0) => u0.
  by exists (norm u / norm v); rewrite (eqP u0) norm0 mul0r normr0 scale0r.
have : vec_angle u v = 0 \/ vec_angle u v = pi R.
  rewrite /vec_angle (eqP uv) norm0.
  case: (lerP 0 (u *d v)) => udv; [left | right].
    rewrite arg_Re // ltr_neqAle udv andbT.
    apply/eqP => /esym/eqP/dotmul_eq0_crossmul_neq0.
    by rewrite u0 v0 uv => /(_ isT isT).
  by rewrite arg_Re_neg.
case => [ /(vec_angle0_inv u0 v0) | /(vec_anglepi_inv u0 v0)] ukv.
  exists (norm u / norm v); split => //.
  by rewrite ger0_norm // divr_ge0 // norm_ge0.
exists (- (norm u / norm v)); split => //.
by rewrite normrN ger0_norm // divr_ge0 // norm_ge0.
Qed.

End colinear.

Section normalize.

Variables (R : rcfType) (n : nat).
Let vector := 'rV[R]_n.
Implicit Type u v : vector.

Definition normalize v := 1 / norm v *: v.

Lemma normalizeI v : norm v = 1 -> normalize v = v.
Proof. move=> v1; by rewrite /normalize v1 divrr ?scale1r // unitr1. Qed.

Lemma norm_normalize v : v != 0 -> norm (normalize v) = 1.
Proof.
move=> v0; rewrite /normalize normZ ger0_norm; last first.
  by rewrite divr_ge0 // ?ler01 // norm_ge0.
by rewrite div1r mulVr // unitf_gt0 // ltr_neqAle norm_ge0 andbT eq_sym norm_eq0.
Qed.

Lemma normalize_eq0 v : (normalize v == 0) = (v == 0).
Proof.
apply/idP/idP => [|/eqP ->]; last by rewrite /normalize scaler0.
case/boolP : (v == 0) => [//| /norm_normalize].
rewrite -norm_eq0 => -> /negPn; by rewrite oner_neq0.
Qed.

Lemma norm_scale_normalize u : norm u *: normalize u = u.
Proof.
case/boolP : (u == 0) => [/eqP -> {u}|u0]; first by rewrite norm0 scale0r.
by rewrite /normalize scalerA div1r divrr ?scale1r // unitfE norm_eq0.
Qed.

Lemma normalizeZ u (u0 : u != 0) k (k0 : 0 < k) : normalize (k *: u) = normalize u.
Proof.
rewrite /normalize normZ gtr0_norm // div1r invrM ?unitfE ?gtr_eqF //; last first.
  by rewrite ltr_neqAle norm_ge0 eq_sym norm_eq0 u0.
by rewrite scalerA -mulrA mulVr ?mulr1 ?unitfE ?gtr_eqF // div1r.
Qed.

Lemma dotmul_normalize u : u *d normalize u = norm u.
Proof.
case/boolP : (u == 0) => [/eqP ->{u}|u0]; first by rewrite norm0 dotmul0v.
rewrite -{1}(norm_scale_normalize u) dotmulZv dotmulvv norm_normalize //.
by rewrite expr1n mulr1.
Qed.

End normalize.

Section axial_normal_decomposition.

Variables (R : rcfType).
Let vector := 'rV[R]_3.
Implicit Type u v : vector.

Definition axialcomp v u := v *m (u^T *m u).

(* normal component of v w.r.t. u *)
Definition normalcomp v u := v *m (1 - u^T *m u).

Lemma decomp v u : v = axialcomp v u + normalcomp v u.
Proof. by rewrite /axialcomp /normalcomp mulmxBr mulmx1 addrCA subrr addr0. Qed.

Definition orthogonalize v u := normalcomp v (normalize u).

Lemma normalcomp_colinear v u : normalcomp v u = 0 -> colinear v u.
Proof.
rewrite /normalcomp mulmxBr mulmx1 => /eqP.
rewrite subr_eq add0r => /eqP ->.
rewrite /colinear mulmxA (mx11_scalar (v *m u^T)) -/(dotmul v u).
by rewrite  mul_scalar_mx crossmulC linearZ /= crossmulvv scaler0 oppr0.
Qed.

Lemma normalcompP u v : u *d normalcomp v (normalize u) = 0.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite dotmul0v.
rewrite /normalcomp mulmxBr mulmx1 dotmulDr dotmulvN mulmxA.
rewrite (mx11_scalar (v *m _)) mul_scalar_mx dotmulvZ dotmul_normalize.
rewrite -/(v *d _) /normalize dotmulvZ mulrAC div1r mulVr ?unitfE ?norm_eq0 //.
by rewrite mul1r dotmulC subrr.
Qed.

Lemma axialnormal v e : norm e = 1 -> axialcomp v e *d normalcomp v e = 0.
Proof.
move=> e1.
rewrite /axialcomp /normalcomp mulmxBr mulmx1 dotmulDr dotmulvN {2}/dotmul.
by rewrite 2!trmx_mul trmxK -!mulmxA (mulmxA e) dotmul1 // mul1mx /dotmul -!mulmxA subrr.
Qed.

Lemma ortho_normalcomp u v : u *d v = 0 -> normalcomp u v = u.
Proof.
move=> uv0.
rewrite /normalcomp mulmxBr mulmx1 mulmxA (mx11_scalar (u *m _)).
by rewrite -/(u *d _) uv0 /= mul_scalar_mx scale0r subr0.
Qed.

End axial_normal_decomposition.

Section orthonormal_frame.

Variable R : rcfType.
Let vector := 'rV[R]_3. 
Let coordinate := 'rV[R]_3.
Implicit Type p : coordinate.

Section non_oriented_frame.
Variables i j k : vector.

(* not necessarily oriented *)
CoInductive oframe := mkOFrame of
  norm i = 1  &  norm j = 1  &  norm k = 1 &
  i *d j = 0  &  j *d k = 0  &  i *d k = 0.

Lemma orthogonal_expansion_helper : oframe ->
  forall p, p *d i = 0 -> p *d j = 0 -> p *d k = 0 -> p = 0.
Proof.
case=> ni nj nk ij jk ik p.
do 3 rewrite dotmulE sum3E.
move=> H1 H2 H3.
have /eqP : p *m (triple_prod_mat i j k) ^T = 0.
  by rewrite triple_prod_mat_mulmx dotmulE sum3E H1 dotmulE sum3E H2 dotmulE sum3E H3 row30.
rewrite mul_mx_rowfree_eq0; first by move/eqP.
apply/row_freeP; exists (triple_prod_mat i j k).
apply/eqP; rewrite -orthogonalEC.
apply matrix_is_orthogonal; by rewrite !rowK.
Qed.

Lemma orthogonal_expansion p : oframe ->
  p = (p *d i) *: i + (p *d j) *: j + (p *d k) *: k.
Proof.
case=> x1 y1 z1 xy xz yz.
set y : vector := (p *d i) *: i + (p *d j) *: j + (p *d k) *: k.
suff /eqP : p - y = 0; first by rewrite subr_eq0 => /eqP.
apply orthogonal_expansion_helper.
- by apply mkOFrame.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv dotmulvv x1 expr1n mulr1.
  rewrite 2!opprD 2!addrA subrr add0r dotmulZv (dotmulC j) xy mulr0 oppr0.
  by rewrite dotmulZv (dotmulC k) yz mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv xy mulr0 add0r.
  rewrite dotmulZv dotmulvv y1 expr1n mulr1 opprD addrA subrr.
  by rewrite dotmulZv (dotmulC k) xz mulr0 subrr.
- rewrite dotmulDl dotmulNv /y 2!dotmulDl dotmulZv yz mulr0 add0r dotmulZv.
  by rewrite xz mulr0 add0r dotmulZv dotmulvv z1 expr1n mulr1 subrr.
Qed.

Definition frame_sgn (_ : oframe) := i *d (j *v k).

Lemma normi (f : oframe) : norm i = 1. Proof. by case: f. Qed.
Lemma normj (f : oframe) : norm j = 1. Proof. by case: f. Qed.
Lemma normk (f : oframe) : norm k = 1. Proof. by case: f. Qed.

Lemma idotj (f : oframe) : i *d j = 0. Proof. by case: f. Qed.
Lemma jdotk (f : oframe) : j *d k = 0. Proof. by case: f. Qed.
Lemma idotk (f : oframe) : i *d k = 0. Proof. by case: f. Qed.

Lemma frame_sgn1 (f : oframe) : `| frame_sgn f | = 1.
Proof.
case: f => x1 y1 z1 xy yz xz; rewrite /frame_sgn crossmul_triple.
apply/orthogonal_det/matrix_is_orthogonal; by rewrite !rowK.
Qed.

Lemma oframek (f : oframe) : k = i *v j \/ k = - i *v j.
Proof.
move: (frame_sgn1 f).
case: (lerP 0 (i *d (j *v k))) => H.
  rewrite ger0_norm // => {H}.
  rewrite /frame_sgn dotmul_crossmulA.
  move/dotmul1_inv => H; left; rewrite H //.
  case: f => He1 He2 ? e1e2 *.
  rewrite norm_crossmul He1 He2 2!mul1r cos0sin1 //.
  do 2 rewrite -[LHS](mul1r).
  rewrite -{1}He1 -He2 mulrA.
  by rewrite -dotmul_cos.
  by case: f.
rewrite ltr0_norm // => {H} /eqP.
rewrite eqr_oppLR => /eqP.
rewrite /frame_sgn dotmul_crossmulA.
move/dotmulN1_inv => H; right. rewrite crossmulNv H // ?opprK //.
case: f => He1 He2 ? e1e2 *.
rewrite norm_crossmul He1 He2 2!mul1r cos0sin1 //.
do 2 rewrite -[LHS](mul1r).
rewrite -{1}He1 -He2 mulrA.
by rewrite -dotmul_cos.
by case: f.
Qed.

Lemma oframe_pos (f : oframe) : k = i *v j -> frame_sgn f = 1.
Proof.
move=> H.
rewrite /frame_sgn H double_crossmul dotmulvv (dotmulC j).
case: f => normu1 -> _ -> _ _.
by rewrite scale0r subr0 expr1n scale1r dotmulvv normu1 expr1n.
Qed.

Lemma oframe_neg (f : oframe) : k = - i *v j -> frame_sgn f = - 1.
Proof.
move=> H.
rewrite /frame_sgn H double_crossmul dotmulvv dotmulvN scaleNr opprK (dotmulC j).
case: f => normu1 -> _ -> _ _.
by rewrite scale0r addr0 expr1n scale1r dotmulvN dotmulvv normu1 expr1n.
Qed.

Lemma frame_pos_crossmul (f : oframe) : frame_sgn f = 1 -> k = i *v j.
Proof.
case: (oframek f) => // /(oframe_neg f) -> /esym/eqP.
by rewrite -subr_eq0 opprK -mulr2n pnatr_eq0.
Qed.

Lemma oframe_posP (f : oframe) : k = i *v j -> j = k *v i /\ i = j *v k.
Proof.
move=> H; split.
  rewrite H crossmulC double_crossmul.
  case: f => x1 ? ? K *.
  by rewrite K scale0r add0r opprK dotmulvv x1 expr1n scale1r.
rewrite H double_crossmul.
case: f => ? y1 ? K *.
by rewrite dotmulvv y1 expr1n scale1r dotmulC K scale0r subr0.
Qed.

Lemma oframe_negP (f : oframe) : k = - i *v j -> j = i *v k /\ i = k *v j.
Proof.
move=> H; split.
  rewrite H crossmulNv crossmulvN double_crossmul.
  case: f => x1 ? ? K *.
  by rewrite dotmulvv x1 expr1n scale1r K scale0r add0r opprK.
rewrite H crossmulNv crossmulC crossmulvN opprK double_crossmul.
case: f => ? y1 ? K *.
by rewrite dotmulvv y1 expr1n scale1r dotmulC K scale0r subr0.
Qed.

(* lemma 3.5, p.110, o'neill *)
Lemma crossmul_oframe_sgn (f : oframe) v v1 v2 v3 w w1 w2 w3 :
  v = v1 *: i + v2 *: j + v3 *: k ->
  w = w1 *: i + w2 *: j + w3 *: k ->
  v *v w = frame_sgn f *: ((v2 * w3 - v3 * w2) *: i -
                           (v1 * w3 - v3 * w1) *: j +
                           (v1 * w2 - v2 * w1) *: k).
Proof.
move=> -> ->.
rewrite !linearD /=.
rewrite !linearZ /=.
rewrite (crossmulC _ i).
rewrite (crossmulC _ j).
rewrite (crossmulC _ k).
rewrite !linearD /=.
rewrite (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 add0r.
case: (oframek f) => e3e1e2.
  case: (oframe_posP f e3e1e2) => H1 H2.
  rewrite (_ : _ *v _ = v2 *: k); last by rewrite linearZ /= -e3e1e2.
  rewrite scalerN (_ : _ *v _ = - v3 *: j); last first.
    by rewrite linearZ /= crossmulC -H1 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = - v1 *: k); last first.
    by rewrite linearZ /= crossmulC e3e1e2 scalerN scaleNr.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  rewrite (_ : _ *v _ = v3 *: i); last by rewrite linearZ /= -H2.
  rewrite scalerN (_ : _ *v _ = v1 *: j); last by rewrite linearZ /= H1.
  rewrite scalerN (_ : _ *v _ = - v2 *: i); last first.
    by rewrite linearZ /= crossmulC -H2 scaleNr scalerN.
  rewrite scaleNr opprK (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite scalerN scaler0 subr0.
  rewrite (oframe_pos f e3e1e2).
  rewrite !scale1r -![in LHS]addrA addrC.
  rewrite -![in LHS]addrA.
  rewrite addrCA. 
  rewrite addrC.
  rewrite ![in LHS]addrA.
  rewrite -addrA; congr (_ + _); last first.
    by rewrite !scalerA -scaleNr -scalerDl /= addrC mulrC (mulrC w1).
  rewrite -addrA addrACA addrC; congr (_ + _).
    by rewrite -scaleNr !scalerA -scalerDl addrC mulrC mulNr (mulrC w2).
  by rewrite !scalerA -scalerBl scalerN -scaleNr opprB mulrC (mulrC w3).
case: (oframe_negP f e3e1e2) => H1 H2.
rewrite (_ : _ *v _ = - v2 *: k); last first.
  by rewrite linearZ /= e3e1e2 crossmulNv scalerN scaleNr opprK.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = v3 *: j); last first.
  by rewrite linearZ /= -H1.
rewrite scalerN.
rewrite (_ : _ *v _ = v1 *: k); last first.
  by rewrite linearZ /= crossmulC -crossmulNv -e3e1e2.
rewrite scalerN.
rewrite (_ : _ *v _ = 0); last first.
  by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 addr0.
rewrite (_ : _ *v _ = - v3 *: i); last first.
  by rewrite linearZ /= crossmulC -H2 scalerN scaleNr.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = - v1 *: j); last first.
  by rewrite linearZ /= crossmulC -H1 scalerN scaleNr.
rewrite scaleNr opprK.
rewrite (_ : _ *v _ = v2 *: i); last first.
  by rewrite linearZ /= -H2.
rewrite scalerN.
rewrite (_ : _ *v _ = 0); last first.
  by rewrite linearZ /= crossmulvv scaler0.
rewrite oppr0 scaler0 addr0.
rewrite (oframe_neg f e3e1e2).
rewrite -![in LHS]addrA addrC -addrA.
rewrite addrCA -addrA addrC ![in LHS]addrA -addrA; congr (_ + _); last first.
  by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w2).
rewrite -addrA addrACA; congr (_ + _).
  by rewrite !scalerA -scalerBl mulrN1 opprB mulrC (mulrC w3).
by rewrite !scalerA -scalerBl scalerN mulrN1 scaleNr opprK mulrC (mulrC w1).
Qed.

End non_oriented_frame.

Record pframe i j k := mkPFrame {
  oframe_of_pframe :> oframe i j k ;
  pframeP : frame_sgn oframe_of_pframe = 1}.

Definition matrix_of_pframe i j k (f : pframe i j k) := triple_prod_mat i j k.

Lemma icrossj i j k (f : pframe i j k) : k = i *v j.
Proof. exact: (frame_pos_crossmul (pframeP f)). Qed.

Lemma icrossk i j k (f : pframe i j k) : i *v k = - j.
Proof. by rewrite (proj1 (oframe_posP f (icrossj f))) crossmulC. Qed.

Lemma pframe_swap01 i j k : pframe i j k -> pframe j (- i) k.
Proof.
case => -[] i1 j1 k1 ij jk ik Hsgn.
apply: mkPFrame.
  apply: mkOFrame => //.
  by rewrite normN.
  by rewrite dotmulvN dotmulC ij oppr0.
  by rewrite dotmulNv ik oppr0.
move=> f.
rewrite /frame_sgn dotmul_crossmulA linearN /= crossmulC -(icrossj (mkPFrame Hsgn)).
by rewrite opprK dotmulvv k1 expr1n.
Qed.

Lemma pframe_is_rot i j k (f : pframe i j k) : triple_prod_mat i j k \in 'SO_3[R]. 
Proof.
move: (icrossj f) => Hk.
case: f => -[? ? ? ? ? ?] sgn.
by apply matrix_is_rotation; rewrite !rowK.
Qed.

Record frame := mkFrame {
  framei : vector ;
  framej : vector ;
  framek : vector ;
  frameP :> pframe framei framej framek }.

Coercion matrix_of_frame (f : frame) := triple_prod_mat (framei f) (framej f) (framek f).

Lemma row0_frame (f : frame) : row 0 f = framei f.
Proof. case: f => x y z xyz /=; apply/rowP => i; by rewrite 2!mxE. Qed.
Lemma row1_frame (f : frame) : row 1 f = framej f.
Proof. case: f => x y z xyz /=; apply/rowP => i; by rewrite 2!mxE. Qed.
Lemma row2_frame (f : frame) : row 2%:R f = framek f.
Proof. case: f => x y z xyz /=; apply/rowP => i; by rewrite !mxE. Qed.

Lemma norm_row (f : frame) (i : 'I_3) : norm (row i f) = 1.
Proof.
case: f => a b c [] [] a1 b1 c1 H1 H2 H3 Hsgn.
case/boolP : (i == 0) => [/eqP ->|]; first by rewrite row0_frame /=.
rewrite ifnot0 => /orP [] /eqP ->; by [rewrite row1_frame | rewrite row2_frame].
Qed.

Lemma frame_is_rot (f : frame) : matrix_of_frame f \in 'SO_3[R]. 
Proof. apply pframe_is_rot; by case: f. Qed.

(* frame with an origin (tangent frame ?) *)
CoInductive tframe (p : coordinate) (i j k : vector) :=
  TFrame : oframe i j k -> tframe p i j k.
Definition oframe_of_tframe p i j k (f : tframe p i j k) :=
  let: TFrame f := f in f.

Lemma tframe_trans p i j k (f : tframe p i j k) t : tframe (p + t) i j k.
Proof. by case: f => -[] x1 y1 z1 xy yz xz. Qed.

End orthonormal_frame.

Module canonical_frame.
Section canonical_frame.
Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.
Implicit Type p : coordinate.
Definition i : vector := row3 1 0 0.
Definition j : vector := row3 0 1 0.
Definition k : vector := row3 0 0 1.

Lemma normi : norm i = 1.
Proof. by rewrite /norm dotmulE sum3E !mxE /=; simp; rewrite sqrtr1. Qed.
Lemma normj : norm j = 1.
Proof. by rewrite /norm dotmulE sum3E !mxE /=; simp; rewrite sqrtr1. Qed.
Lemma normk : norm k = 1.
Proof. by rewrite /norm dotmulE sum3E !mxE /=; simp; rewrite sqrtr1. Qed.

Lemma idotj : i *d j = 0. Proof. by rewrite dotmulE sum3E !mxE /=; simp. Qed.
Lemma jdotk : j *d k = 0. Proof. by rewrite dotmulE sum3E !mxE /=; simp. Qed.
Lemma idotk : i *d k = 0. Proof. by rewrite dotmulE sum3E !mxE /=; simp. Qed.

Lemma jcrossk : j *v k = i.
Proof. rewrite crossmulE; apply/rowP => i /=; rewrite !mxE /=; by simp. Qed.

Lemma icoor p : p 0 0 = p *d i.
Proof. by rewrite /dotmul mxE sum3E !mxE /=; simp. Qed.
Lemma jcoor p : p 0 1 = p *d j.
Proof. by rewrite /dotmul mxE sum3E !mxE /=; simp. Qed.
Lemma kcoor p : p 0 2%:R = p *d k.
Proof. by rewrite /dotmul mxE sum3E !mxE /=; simp. Qed.

Definition oframe := mkOFrame normi normj normk idotj jdotk idotk.
Lemma pframeP : frame_sgn oframe = 1.
Proof. by rewrite /frame_sgn jcrossk dotmulvv normi expr1n. Qed.
Definition pframe := mkPFrame pframeP.
Definition frame := mkFrame pframe.

(* TODO: usefull aliases? *)
Lemma icrossj : i *v j = k.
Proof. by rewrite -(icrossj pframe). Qed.
Lemma icrossk : i *v k = - j.
Proof. by rewrite -(icrossk pframe). Qed.

Lemma framei a : frame 0 a = i 0 a.
Proof. by rewrite /frame /= /matrix_of_frame mxE. Qed.
Lemma framej a : frame 1 a = j 0 a.
Proof. by rewrite /frame /matrix_of_frame mxE. Qed.
Lemma framek a : frame 2%:R a = k 0 a.
Proof. by rewrite /frame /matrix_of_frame mxE. Qed.

End canonical_frame.
End canonical_frame. 

Module V := canonical_frame.
Arguments V.i [_].
Arguments V.j [_].
Arguments V.k [_].

Section frame_of_vector.

Variable R : rcfType.
Variable i : 'rV[R]_3.
Hypothesis i0 : i != 0.

(* TODO: rename *)
Lemma j_of_i_colinear (iVi : colinear i V.i) :
  normalcomp V.j (normalize i) = V.j.
Proof.
rewrite ortho_normalcomp // dotmulvZ.
case/colinearP : iVi => [|[_ [k [Hk iki]]]].
  by rewrite -norm_eq0 V.normi (negbTE (@oner_neq0 _)).
by rewrite {2}iki dotmulvZ dotmulC V.idotj 2!mulr0.
Qed.

Definition j_of_i :=
  if colinear i V.i then V.j else normalize (normalcomp V.i (normalize i)).

Lemma norm_j_of_i : norm j_of_i = 1.
Proof.
rewrite /j_of_i; case: ifPn => iVi; first by rewrite V.normj.
rewrite norm_normalize //.
apply: contra iVi => /eqP/normalcomp_colinear.
rewrite /normalize colinear_sym => /colinearZ2; apply.
by rewrite div1r invr_eq0 norm_eq0 i0.
Qed.

Lemma i_dot_j_of_i : i *d j_of_i = 0.
Proof.
rewrite /j_of_i; case: ifPn => iVi.
  case/colinearP : iVi => [| [_ [k [Hk ->]]]].
    by rewrite -norm_eq0 V.normi (negbTE (oner_neq0 _)).
  by rewrite dotmulZv V.idotj mulr0.
by rewrite dotmulvZ normalcompP mulr0.
Qed.

Definition k_of_i := normalize i *v j_of_i.

Lemma norm_k_of_i : norm k_of_i = 1.
Proof.
rewrite /k_of_i norm_crossmul_normal // ?norm_normalize // ?norm_j_of_i //.
by rewrite /normalize dotmulZv i_dot_j_of_i // mulr0.
Qed.

Definition pframe_of_i : pframe (normalize i) j_of_i k_of_i.
apply: mkPFrame.
  apply: mkOFrame.
  by rewrite norm_normalize.
  by rewrite norm_j_of_i.
  by rewrite norm_k_of_i.
  by rewrite /normalize dotmulZv i_dot_j_of_i mulr0.
  by rewrite dotmul_crossmulCA crossmulvv dotmulv0.
  by rewrite dotmul_crossmulA crossmulvv dotmul0v.
case => /= ? ? H ? ? ?.
by rewrite /frame_sgn /= dotmul_crossmulA dotmulvv H expr1n.
Qed.

End frame_of_vector.

Lemma j_of_iZ {R : rcfType} (i : 'rV[R]_3) (i0 : i != 0) k (k0 : 0 < k) :
  j_of_i (k *: i) = j_of_i i.
Proof.
rewrite /j_of_i; case: ifPn => H.
  case: ifPn => //.
  move/colinearZ2 : H.
  rewrite (gtr_eqF k0) => /(_ isT) -> ?; exfalso; by done.
case: ifPn; last by rewrite normalizeZ.
move/(colinearZ1 k).
rewrite (negbTE H) => ?; exfalso; by done.
Qed.

Lemma k_of_iZ {R : rcfType} (i : 'rV[R]_3) (i0 : i != 0) k (k0 : 0 < k) :
  k_of_i (k *: i) = k_of_i i.
Proof. by rewrite /k_of_i j_of_iZ // normalizeZ. Qed.

(*Module Frame.
Section frame_section.
Variable R : rcfType.
Local Notation coordinate := 'rV[R]_3.
Local Notation basisType := 'M[R]_3.
Definition x_ax : basisType -> 'rV[R]_3 := row 0.
Definition y_ax : basisType -> 'rV[R]_3 := row 1%R.
Definition z_ax : basisType -> 'rV[R]_3 := row 2%:R.

Record t := mkT {
  origin : coordinate ;
  basis :> basisType ;
  _ : unitmx basis }.

Lemma unit (f : t) : basis f \in GRing.unit. Proof. by case: f. Qed.
End frame_section.
End Frame.

Coercion Framebasis R (f : Frame.t R) : 'M[R]_3 := Frame.basis f.
*)
(*Hint Immediate Frame.unit.*)

Inductive vec {R} (f : frame R) : Type := Vec of 'rV[R]_3.

Definition vec_of {R} (f : frame R) (x : vec f) := let: Vec v := x in v.

(* consider "frame" to be w.r.t. the canonical frame *)
(* x *m f : rotate a vector in the canonical frame according to the frame
  (we obtain a new vector but still in the canonical frame after rotation)
 *)
Definition rotate_wrt_frame {R} (f : frame R) (x : vec (V.frame R)) : vec (V.frame R) :=
  Vec _ (vec_of x *m f).

(* TODO: move *)
Lemma mulmx_can_frame {R : rcfType} (x : 'rV[R]_3) : x *m V.frame R = x.
Proof.
apply/rowP => i.
case/boolP : (i == 0) => [/eqP -> |].
  rewrite mxE sum3E V.framei V.framej V.framek !mxE /=; by simp.
rewrite ifnot0 => /orP [] /eqP ->;
  rewrite mxE sum3E V.framei V.framej V.framek !mxE /=; by simp.
Qed.

Lemma rotate_wrt_canonical_frame {R} (x : vec (V.frame R)) :
  rotate_wrt_frame (V.frame R) x = x.
Proof. case: x => x; congr Vec => /=; by rewrite mulmx_can_frame. Qed.

(* change of coordinates: same vector but with coord in the canonical frame *)
Definition can_of_rel_coord {R} (f : frame R) (x : vec f) : vec (V.frame R) :=
  Vec _ (vec_of x *m f).

(* change of coordinates: same vector but with coord given in f *)
Definition rel_of_can_coord {R} (f : frame R) (x : vec (V.frame R)) : vec f :=
  Vec _ (vec_of x *m f^T).

Lemma can_of_rel_coordK {R} (f : frame R) (x : vec f) :
  rel_of_can_coord _ (can_of_rel_coord x) = x.
Proof.
rewrite /rel_of_can_coord /can_of_rel_coord /=; case: x => x; congr Vec => /=.
rewrite -mulmxA -(rotation_inv (frame_is_rot f)) mulmxV ?mulmx1 // unitmxE.
by rewrite (rotation_det (frame_is_rot f)) unitr1.
Qed.

Lemma rel_of_can_coordK {R} (f : frame R) (x : vec _) :
  can_of_rel_coord (rel_of_can_coord f x) = x.
Proof.
rewrite /rel_of_can_coord /can_of_rel_coord /=; case: x => x; congr Vec => /=.
rewrite -mulmxA -(rotation_inv (frame_is_rot f)) mulVmx ?mulmx1 // unitmxE.
by rewrite (rotation_det (frame_is_rot f)) unitr1.
Qed.

(*Section about_frame.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := Frame.t R.

(* coordinate in frame f *)
Inductive coor (f : frame) : Type := Coor of 'rV[R]_3.

Definition absolute_coor (f : frame) (x : coor f) : 'rV[R]_3 :=
  match x with Coor v => Frame.origin f + v *m Frame.basis f end.

Definition relative_coor f (x : coordinate) : coor f :=
  Coor _ ((x - Frame.origin f) *m (Frame.basis f)^-1).

Lemma absolute_coorK f (x : coor f) : relative_coor f (absolute_coor x) = x.
Proof.
case: x => /= v.
by rewrite /relative_coor addrC addKr -mulmxA mulmxV // ?mulmx1 // Frame.unit.
Qed.

Lemma relative_coorK f (x : coordinate) : absolute_coor (relative_coor f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // ?Frame.unit // mulmx1 addrC addrNK. Qed.

(* vector in frame f *)
Inductive vec (f : frame) : Type := Vec of 'rV[R]_3.

Definition absolute_vec f (x : vec f) : 'rV[R]_3 :=
  match x with Vec v => v *m Frame.basis f end.

Definition relative_vec f (x : vector) : vec f :=
  Vec _ (x *m (Frame.basis f)^-1).

Lemma absolute_vecK f (x : vec f) : relative_vec f (absolute_vec x) = x.
Proof. case: x => /= v. by rewrite /relative_vec -mulmxA mulmxV // ?Frame.unit // mulmx1. Qed.

Lemma relative_vecK f (x : vector) : absolute_vec (relative_vec f x) = x.
Proof. by rewrite /= -mulmxA mulVmx // ?Frame.unit // mulmx1. Qed.

End about_frame.*)

(* TODO: useful? *)
Lemma abs {R:rcfType} (f : frame R) i j : f i j = row j (V.frame R) *d row i f.
Proof.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite row0_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
    by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
  rewrite ifnot0 => /orP [] /eqP ->.
    rewrite row1_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
    by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
  rewrite row2_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
  by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite row0_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
    by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
  rewrite ifnot0 => /orP [] /eqP ->.
    rewrite row1_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
    by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
  rewrite row2_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
  by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
case/boolP : (j == 0) => [/eqP ->|].
  rewrite row0_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
  by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
rewrite ifnot0 => /orP [] /eqP ->.
  rewrite row1_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
  by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
rewrite row2_frame /= dotmulE sum3E ![(row3 _ _ _) _ _]mxE /=.
by rewrite !(mul1r,mul0r,addr0,add0r) [in RHS]mxE.
Qed.

Module FromTo.
Section tmp.
Variable R : rcfType.
Variables A B : frame R.
Record t := mkT {
  M :> 'M[R]_3 ;
  HM : M == \matrix_(i, j) (row j B^T *d row i A^T)
  (* transpose of def 1.1 of handbook ->
     "orientation of coor frame B related to coor frame A" (A ^R_ B) *)
}.
End tmp.
End FromTo.
Coercion RotM {R} (A B : frame R) := @FromTo.M _ A B.

Notation "A %> B" := (@FromTo.t _ A B) (at level 5).

Lemma FromToE R (A B : frame R) (M : A %> B) :
  M = (matrix_of_frame A)^-1 *m B :> 'M[R]_3.
Proof.
case: M => /= M /eqP ->; apply/matrixP => i j.
rewrite mxE dotmulE /= mxE; apply eq_bigr => /= k _.
by rewrite mxE [row _ _ _ _]mxE mxE (rotation_inv (frame_is_rot A)) mulrC.
Qed.

Lemma FromToCan {R:rcfType} (A : frame R) (M : A %> (V.frame R)) (x : vec A) :
  [fun x : 'rV_3 => x *m M] =1 [fun x => x *m A^T].
Proof.
move=> i /=.
by rewrite (FromToE M) mulmxA mulmx_can_frame (rotation_inv (frame_is_rot A)).
Qed.

Lemma FromToComp_proof {R : rcfType} (A B C : frame R) (M1 : A %> B) (M2 : B %> C) :
  (M1 *m M2) == \matrix_(i, j) (row j C^T *d row i A^T).
Proof.
rewrite (FromToE M1) (FromToE M2) -mulmxA (mulmxA (matrix_of_frame B)).
rewrite mulmxV; last first.
  by rewrite unitmxE (rotation_det (frame_is_rot B)) unitr1.
rewrite mul1mx; apply/eqP/matrixP => i j.
rewrite !mxE dotmulE; apply/eq_bigr => k _.
by rewrite 2![row _ _ _ _]mxE (rotation_inv (frame_is_rot A)) 2![_^T _ _]mxE mulrC.
Qed.

Definition FromToComp {R:rcfType} (A B C: frame R) (M1 : A %> B) (M2 : B %> C) : A %> C :=
  FromTo.mkT (FromToComp_proof M1 M2).

Lemma FromToCompE {R:rcfType} (A B: frame R) (M : A %> B) (u : 'rV[R]_3) :
  u *m M = u *m A^T *m B.
Proof. by rewrite -mulmxA (FromToE M) (rotation_inv (frame_is_rot A)). Qed.

Section triad.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.

Variables a b c : coordinate.
Hypothesis ab : a != b.
Hypothesis abc : ~~ colinear (b - a) (c - a).

Definition xtriad := normalize (b - a).

Definition ytriad := normalize (normalcomp (c - a) xtriad).

Definition triad := (xtriad, ytriad, xtriad *v ytriad).

Let ac : a != c.
Proof. by apply: contra abc => /eqP ->; rewrite subrr /colinear crossmulv0. Qed.

Lemma xtriad_norm : norm xtriad = 1.
Proof. by rewrite /xtriad norm_normalize // subr_eq0 eq_sym. Qed.

Lemma xtriad_neq0 : xtriad != 0.
Proof. by rewrite -norm_eq0 xtriad_norm oner_neq0. Qed.

Lemma ytriad_norm : norm ytriad = 1.
Proof. 
rewrite /ytriad norm_normalize //.
apply/eqP => /normalcomp_colinear; apply/negP; rewrite /xtriad /normalize.
apply: contra (abc).
rewrite colinear_sym.
apply: colinearZ2.
by rewrite div1r invr_eq0 norm_eq0 subr_eq0 eq_sym.
Qed.

Lemma ytriad_neq0 : ytriad != 0.
Proof. by rewrite -norm_eq0 ytriad_norm oner_neq0. Qed.

Lemma xytriad_ortho : xtriad *d ytriad = 0.
Proof. by rewrite /= /xtriad /ytriad dotmulZv dotmulvZ normalcompP 2!mulr0. Qed.

Definition ztriad := xtriad *v ytriad.

Lemma yztriad_ortho : ytriad *d ztriad = 0.
Proof. by rewrite /ztriad dotmul_crossmulCA crossmulvv dotmulv0. Qed.

Lemma xztriad_ortho : xtriad *d ztriad = 0.
Proof. by rewrite /ztriad dotmul_crossmulA crossmulvv dotmul0v. Qed.

Lemma ztriad_norm : norm ztriad = 1.
Proof. by rewrite norm_crossmul_normal // ?xtriad_norm // ?ytriad_norm // xytriad_ortho. Qed.

Lemma ztriad_neq0 : ztriad != 0.
Proof. by rewrite -norm_eq0 ztriad_norm oner_neq0. Qed.

Definition M_triad : oframe _ _ _ := mkOFrame 
  xtriad_norm ytriad_norm ztriad_norm xytriad_ortho yztriad_ortho xztriad_ortho.

Lemma M_triad_is_pos : frame_sgn M_triad = 1.
Proof.
rewrite /frame_sgn /ztriad double_crossmul dotmulvv ytriad_norm expr1n.
rewrite scale1r (dotmulC ytriad) xytriad_ortho scale0r subr0 dotmulvv.
by rewrite xtriad_norm expr1n.
Qed.

Definition pframe_triad : pframe _ _ _ := mkPFrame M_triad_is_pos.
(* therefore, x * frame_triad^T turns a vector x in the canonical frame into the frame_triad *)

Lemma triad_is_SO : triple_prod_mat xtriad ytriad ztriad \is 'SO_3[R].
Proof. exact: (pframe_is_rot pframe_triad). Qed.

End triad.

Section transformation_given_three_points.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Variables l1 l2 l3 r1 r2 r3 : coordinate.
Hypotheses (l12 : l1 != l2) (r12 : r1 != r2).
Hypotheses (l123 : ~~ colinear (l2 - l1) (l3 - l1)) 
           (r123 : ~~ colinear (r2 - r1) (r3 - r1)).

Definition lframe := mkFrame (pframe_triad l12 l123).
Definition rframe := mkFrame (pframe_triad r12 r123).

Definition rot3 := lframe^T *m rframe.

Definition trans3 : vector := r1 - l1 *m rot3.

Lemma ytriad_l_r : ytriad l1 l2 l3 *m rot3 = ytriad r1 r2 r3.
Proof.
rewrite /rot3 /= mulmxA triple_prod_mat_mulmx dotmulC xytriad_ortho.
rewrite dotmulvv ytriad_norm // expr1n dotmul_crossmulCA crossmulvv dotmulv0.
rewrite /matrix_of_frame /=.
rewrite triple_prod_matE row3_row_mx.
rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
rewrite (mul_row_col 1%:M) mul_scalar_mx scale1r.
by rewrite mul_scalar_mx scale0r addr0.
Qed.

Lemma ztriad_l_r : ztriad l1 l2 l3 *m rot3 = ztriad r1 r2 r3.
Proof.
rewrite /rot3 /= mulmxA triple_prod_mat_mulmx.
rewrite {1}/ztriad dotmulC dotmul_crossmulA crossmulvv dotmul0v.
rewrite {1}/ztriad -dotmul_crossmulA crossmulvv dotmulv0.
rewrite /matrix_of_frame /=.
rewrite dotmulvv ztriad_norm // expr1n triple_prod_matE.
rewrite row3_row_mx.
do 2 rewrite (mul_row_col 0%:M) mul_scalar_mx scale0r add0r.
by rewrite mul_scalar_mx scale1r.
Qed.

(* TODO: move? *)
Lemma mul_tr (M1 M2 : 'M[R]_3) : M1^T *m M2 = \matrix_(i < 3, j < 3) (row i M1^T *d row j M2^T).
Proof.
apply/matrixP => i j; rewrite /dotmul !mxE.
apply eq_bigr => /= k _; by rewrite !mxE.
Qed.

Definition FromLeftToRight : lframe %> rframe.
apply FromTo.mkT with (lframe^T *m rframe).
rewrite -(trmxK lframe) mul_tr.
apply/eqP/matrixP => i j; by rewrite [in LHS]mxE [in RHS]mxE dotmulC.
Qed.

Lemma FromLeftToRightE (u : 'rV[R]_3) : u *m FromLeftToRight = u *m rot3.
Proof. by rewrite FromToCompE /rot3 ?trmx_mul mulmxA. Qed.

End transformation_given_three_points.

Section rot_axis_definition.

Variable R : rcfType.

Definition Rx (a : angle R) := triple_prod_mat
  (row3 1 0 0) 
  (row3 0 (cos a) (- sin a))
  (row3 0 (sin a) (cos a)).

Lemma Rx_RO (a : angle R) : Rx a = block_mx (1 : 'M_1) (0 : 'M_(1, 2)) (0 : 'M_(2, 1)) (RO a).
Proof.
rewrite -(@submxK _ 1 2 1 2 (Rx a)).
rewrite (_ : ulsubmx _ = 1); last first.
  apply/rowP => i; by rewrite (ord1 i) !mxE /=.
rewrite (_ : ursubmx _ = 0); last first.
  apply/rowP => i; rewrite !mxE /=; case: ifPn => //; by case: ifPn.
rewrite (_ : dlsubmx _ = 0); last first.
  apply/colP => i; rewrite !mxE /=.
  case: ifPn; first by rewrite !mxE.
  by case: ifPn; rewrite !mxE.
rewrite (_ : drsubmx _ = RO a) //.
apply/matrixP => i j; rewrite !mxE /=.
case/boolP : (i == 0) => [/eqP -> /=|].
  case/boolP : (j == 0) => [/eqP -> /=|]; first by rewrite !mxE.
  rewrite ifnot01 => /eqP ->; by rewrite !mxE.
rewrite ifnot01 => /eqP -> /=; by rewrite !mxE.
Qed.

Lemma Rx_is_SO a : Rx a \is 'SO_3[R].
Proof.
(* TODO: pove using RO_is_SO? *)
apply matrix_is_rotation.
- apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
  rewrite -dotmulvv dotmulE sum3E !mxE /=. by simp.
- apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?norm_ge0 // expr1n.
  by rewrite -dotmulvv dotmulE sum3E !mxE /= mulr0 add0r -2!expr2 sqrrN cos2Dsin2.
- rewrite 2!rowK /= dotmulE sum3E !mxE /=; by simp.
- rewrite 3!rowK /= crossmulE !mxE /=. by simp.
Qed.

Lemma tr_Rx (a : angle R) : \tr (Rx a) = 1 + cos a *+ 2.
Proof. by rewrite /Rx /mxtrace sum3E !mxE /= -addrA -mulr2n. Qed.

Definition Ry R (a : angle R) := triple_prod_mat
  (row3 (cos a) 0 (sin a))
  (row3 0 1 0) 
  (row3 (- sin a) 0 (cos a)).

Definition Rz R (a : angle R) := triple_prod_mat
  (row3 (cos a) (- sin a) 0)
  (row3 (sin a) (cos a) 0)
  (row3 0 0 1).

CoInductive is_around_axis (i : 'rV[R]_3) (a : angle R)
  (f : {linear 'rV[R]_3 -> 'rV[R]_3}) : Prop := mkIsAroundAxis of
  f i = i &
  let: j := j_of_i i in let: k := k_of_i i in
  f j = (cos a) *: j + (-sin a) *: k &
  let: j := j_of_i i in let: k := k_of_i i in
  f k = (sin a) *: j + (cos a) *: k.

Lemma is_around_axisZ u (u0 : u != 0) (a : angle R) f k (k0 : 0 < k):
  is_around_axis (k *: u) a f <-> is_around_axis u a f.
Proof.
split; case; rewrite ?(j_of_iZ u0 k0) ?(k_of_iZ u0 k0) => H1 H2 H3; split;
  rewrite ?(j_of_iZ u0 k0) ?(k_of_iZ u0 k0) //.
- move: H1.
  rewrite linearZ /= => /scalerI -> //; by rewrite gtr_eqF.
- by rewrite linearZ H1.
Qed.

Lemma sim (M : 'M[R]_3) i j k (f : pframe i j k) (A : 'M[R]_3) :
  i *m M = A 0 0 *: i + A 0 1 *: j + A 0 2%:R *: k -> 
  j *m M = A 1 0 *: i + A 1 1 *: j + A 1 2%:R *: k -> 
  k *m M = A 2%:R 0 *: i + A 2%:R 1 *: j + A 2%:R 2%:R *: k -> 
  let P := triple_prod_mat i j k in
  M = P^-1 * A * P.
Proof.
move=> H1 H2 H3 P.
have : P * M = A * P.
  rewrite /P -mulmxE mulmx_triple_prod_mat (triple_prod_mat_rowE A).
  rewrite mulmx_triple_prod_mat H1 H2 H3.
  congr triple_prod_mat; apply/rowP => a; by rewrite !mxE sum3E !mxE.
rewrite -mulrA => <-.
rewrite mulrA mulVr ?mul1r // unitmxE unitfE /P det_triple_prod_mat.
move: (frame_sgn1 f) => /=.
by rewrite /frame_sgn dotmul_crossmulA -normr_gt0 => ->; rewrite ltr01.
Qed.

Lemma is_around_axis_is_SO (u : 'rV[R]_3) (u1 : u != 0) (a : angle R) 
  (f : {linear 'rV[R]_3 -> 'rV[R]_3}) :
  is_around_axis u a f -> lin1_mx f \is 'SO_3[R].
Proof.
case => H1 H2 H3.
move: (@sim (lin1_mx f) _ _ _ (pframe_of_i u1) (Rx a)).
rewrite !mxE /= !scale1r !scale0r !add0r !addr0.
rewrite 3!mul_rV_lin1.
rewrite {1 2}/normalize linearZ H1.
move/(_ erefl H2 H3) => ->.
move=> [:abs].
rewrite rpredM //; last first.
  abstract: abs.
  apply pframe_is_rot.
  exact: pframe_of_i.
by rewrite rpredM // ?Rx_is_SO // rotation_inv // rotationV.
Qed.

Definition lin_of_mat (M : 'M[R]_3) : {linear 'rV[R]_3 -> 'rV[R]_3} := mulmxr_linear 1 M.

Lemma tr_around_axis (u : 'rV[R]_3) (u1 : u != 0) (a : angle R) (f : 'M[R]_3) :
  is_around_axis u a (lin_of_mat f) -> \tr f = 1 + cos a *+ 2.
Proof.
case=> [H1 [H2 H3]].
move: (@sim f _ _ _ (pframe_of_i u1) (Rx a)).
rewrite !mxE /= !scale1r !scale0r !add0r !addr0.
rewrite /= in H1.
rewrite {1 2}/normalize -scalemxAl H1.
move/(_ erefl H2 H3) => ->.
rewrite mxtrace_mulC mulmxA mulmxV; last first.
  rewrite unitmxE unitfE rotation_det ?oner_neq0 //.
  apply pframe_is_rot.
  exact: pframe_of_i.
by rewrite mul1mx tr_Rx. 
Qed.

End rot_axis_definition.

Section homogeneous_transformation.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Record transform : Type := Transform {
  translation : vector;
  rot : 'M[R]_3 ;
  _ : rot \in 'SO_3[R] }.

(* homogeneous transformation *)
Coercion hmx (T : transform) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx (translation T)^T 1).

Definition hrot_of_transform (T : transform) : 'M[R]_4 :=
  row_mx (col_mx (rot T) 0) (col_mx 0 1).

Definition htrans_of_transform (T : transform) : 'M[R]_4 :=
  row_mx (col_mx 1 0) (col_mx (translation T)^T 1).

Lemma hmxE (T : transform) : T = htrans_of_transform T *m hrot_of_transform T :> 'M_4.
Proof.
rewrite /hmx /htrans_of_transform /hrot_of_transform.
rewrite (mul_mx_row (row_mx (col_mx 1 0) (col_mx (translation T)^T 1)) (col_mx (rot T) 0)).
rewrite mul_row_col mulmx0 addr0 mul_row_col mulmx0 add0r mulmx1.
by rewrite mul_col_mx mul1mx mul0mx.
Qed.

Definition inv_htrans (T : transform) := row_mx (col_mx 1 0) (col_mx (- (translation T)^T) 1).

Lemma inv_htransP T : htrans_of_transform T *m inv_htrans T = 1.
Proof.
rewrite /htrans_of_transform /inv_htrans mul_mx_row.
rewrite (mul_row_col (col_mx 1 0) (col_mx (translation T)^T 1)) mulmx0 addr0 mulmx1.
rewrite (mul_row_col (col_mx 1 0) (col_mx (translation T)^T 1)) mulmx1.
rewrite mul_col_mx mul1mx mul0mx add_col_mx addrC subrr add0r.
rewrite -(block_mxEh (1 :'M_3) 0 0 1).
rewrite -[in RHS](@submxK _ 3 1 3 1 (1 : 'M_4)).
congr (@block_mx _ 3 1 3 1); apply/matrixP => i j.
by rewrite !mxE -!val_eqE.
rewrite !mxE -val_eqE /= (ord1 j) addn0.
move: (ltn_ord i); by rewrite ltn_neqAle => /andP [] /negbTE ->.
rewrite !mxE -val_eqE /= (ord1 i) addn0.
by move: (ltn_ord j); rewrite ltn_neqAle eq_sym => /andP [] /negbTE ->.
by rewrite !mxE -!val_eqE.
Qed.

Definition homogeneous := 'rV[R]_4.

(*Definition hvect (x : vector) : homogeneous := row_mx x 0. *)
Inductive hvect := HVec of vector.
Coercion homogeneous_of_hvect (hv : hvect) : 'rV[R]_4 :=
  let: HVec x := hv in row_mx x 0.

(*Definition hcoor (x : coordinate) : homogeneous := row_mx x 1.*)
Inductive hcoor := HCor of coordinate.
Coercion homogeneous_of_hcoor (hc : hcoor) : 'rV[R]_4 :=
  let: HCor x := hc in row_mx x 1.

Definition coord_of_h (x : homogeneous) : coordinate := 
  lsubmx (castmx (erefl, esym (addn1 3)) x).

Lemma coord_of_hB a b : coord_of_h (a - b) = coord_of_h a - coord_of_h b.
Proof. apply/rowP => i; by rewrite !mxE !castmxE /= esymK !cast_ord_id !mxE. Qed.

Lemma coord_of_hE (x : homogeneous) : coord_of_h x = \row_(i < 3) x 0 (inord i).
Proof.
apply/rowP => i; rewrite !mxE castmxE /= esymK !cast_ord_id; congr (x 0 _).
apply val_inj => /=; by rewrite inordK // (ltn_trans (ltn_ord i)).
Qed.

Definition htrans_of_vector (x : vector) (T : transform) : homogeneous :=
  (T *m (HVec x)^T)^T.

Lemma htrans_of_vectorE a T : htrans_of_vector a T = a *m row_mx (rot T)^T 0.
Proof.
rewrite /htrans_of_vector /hmx /hvect.
rewrite (tr_row_mx a) (mul_row_col (col_mx (rot T) 0)) linearD /= trmx_mul.
by rewrite (tr_col_mx (rot T)) trmx_mul !trmx0 !trmxK mul0mx addr0.
Qed.

Lemma linear_htrans_of_vector T : linear (htrans_of_vector^~ T).
Proof. move=> ? ? ?; by rewrite 3!htrans_of_vectorE mulmxDl -scalemxAl. Qed.

Definition htrans_of_coordinate (x : coordinate) (T : transform) : homogeneous :=
  (T *m (HCor x)^T)^T.

Lemma htrans_of_coordinateB a b T :
  htrans_of_coordinate a T - htrans_of_coordinate b T = htrans_of_vector (a - b) T.
Proof.
rewrite {1}/htrans_of_coordinate {1}/hmx.
rewrite (tr_row_mx a) trmx1 (mul_row_col (col_mx (rot T) 0)) linearD /=.
rewrite mulmx1 trmx_mul trmxK (tr_col_mx (rot T)) trmx0.
rewrite (tr_col_mx (translation T)^T) trmxK trmx1.
rewrite {1}/htrans_of_coordinate {1}/hmx.
rewrite trmx_mul trmxK.
rewrite (tr_row_mx (col_mx (rot T) 0)) (tr_col_mx (translation T)^T) trmxK trmx1.
rewrite (tr_col_mx (rot T)) trmx0 (mul_row_col b) mul1mx.
rewrite addrAC opprD -!addrA [in X in _ + (_ + X) = _]addrC subrr addr0.
rewrite /htrans_of_vector /hmx /hvect.
rewrite (tr_row_mx (a - b)) trmx0 trmx_mul.
rewrite (tr_col_mx (a - b)^T) trmx0.
rewrite (tr_row_mx (col_mx (rot T) 0)) trmxK.
rewrite (mul_row_col (a - b)) mul0mx addr0.
rewrite (tr_col_mx (rot T)) trmx0.
by rewrite mulmxBl.
Qed.

Definition homogeneous_ap (x : coordinate) (T : transform) : coordinate :=
  (*\row_(i < 3) (homogeneous_mx T *m col_mx  x^T 1 (* 0 for vectors? *) )^T 0 (inord i).*)
  coord_of_h (htrans_of_coordinate x T).

Lemma homogeneous_apE x T : homogeneous_ap x T = 
  lsubmx (castmx (erefl, esym (addn1 3)) (htrans_of_coordinate x T)).
Proof.
rewrite /homogeneous_ap.
apply/rowP => i; rewrite !mxE.
by rewrite castmxE /= esymK cast_ord_id /htrans_of_coordinate !mxE.
Qed.

Lemma htrans_of_vector_preserves_norm a T :
  norm (coord_of_h (htrans_of_vector a T)) = norm a.
Proof.
rewrite htrans_of_vectorE /coord_of_h mul_mx_row mulmx0.
rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
rewrite (cast_row_mx _ (a *m (rot T)^T)) row_mxKl castmx_id.
rewrite orth_preserves_norm // orthogonalV rotation_sub //; by case: T.
Qed.

Lemma coord_of_ht_htrans_of_vectorE u T :
  coord_of_h (htrans_of_vector u T) = u *m (rot T)^T.
Proof.
rewrite htrans_of_vectorE; apply/rowP => i.
rewrite mxE castmxE /= esymK cast_ord_id mul_mx_row mulmx0.
rewrite (_ : cast_ord (addn1 3) _ = lshift 1 i); last by apply val_inj.
by rewrite (row_mxEl (u *m (rot T)^T)).
Qed.

Lemma hcoor_inv_htrans a t r (Hr : r \is 'SO_3[R]) :
  (HCor a) *m (inv_htrans (Transform t Hr))^T = HCor (a - t) :> homogeneous.
Proof.
rewrite /inv_htrans /= tr_row_mx 2!tr_col_mx !trmx1 trmx0.
rewrite (mul_row_col a) mul1mx mul_mx_row mulmx1 mulmx0 add_row_mx add0r.
by rewrite linearN /= trmxK.
Qed.

Lemma hcoor_hrot_of_transform a t r (Hr : r \is 'SO_3[R]) :
  (HCor a) *m (hrot_of_transform (Transform t Hr))^T = HCor (a *m r^T) :> homogeneous.
Proof.
rewrite /hrot_of_transform /= (tr_row_mx (col_mx r 0)) !tr_col_mx !trmx0 trmx1.
rewrite (mul_row_col a) mul1mx (mul_mx_row a r^T) mulmx0 (add_row_mx (a *m r^T)).
by rewrite addr0 add0r.
Qed.

End homogeneous_transformation.

Section isometry_def.

Variable (R : rcfType) (n : nat).
Let coordinate := 'rV[R]_n.

Definition preserves_length (f : coordinate -> coordinate) :=
  forall i j, norm (i - j) = norm (f i - f j).

Record isometry := mkIsometry {
  iso :> coordinate -> coordinate ;
  isoP : preserves_length iso}.

Definition matrix_of_iso (f : isometry) : linear f ->
  {M : {linear 'rV[R]_n -> 'rV[R]_n} & forall x, f x = M x}.
Proof.
move=> H.
have @g : {linear 'rV[R]_n -> 'rV[R]_n}.
  exists f; exact: (GRing.Linear.class_of_axiom H).
by exists g.
Defined.

Record central_isometry := mkCentralIsometry {
   ciso :> isometry ;
   cisoP : ciso 0 = 0}.

Lemma central_isometry_preserves_norm (f : central_isometry) : preserves_norm f.
Proof. case: f => f f0 p; by rewrite -(subr0 (f p)) -f0 -(isoP f) subr0. Qed.

Lemma central_isometry_preserves_dotmul (f : central_isometry) : preserves_dotmul f.
Proof.
case: f => f f0 a b.
have : norm (f a - f b) = norm (a - b) by rewrite -(isoP f).
rewrite /norm => /eqP.
rewrite eqr_sqrt ?le0dotmul // !dotmulDl !dotmulDr !dotmulvv !normN.
rewrite !(central_isometry_preserves_norm (mkCentralIsometry f0)) !addrA 2!(addrC _ (norm b ^+ 2)).
move/eqP/addrI.
rewrite -2!addrA => /addrI.
rewrite -(dotmulC (f a)) dotmulvN -(dotmulC a) dotmulvN -2!mulr2n.
move/eqP.
rewrite -mulr_natr -[in X in _ == X -> _]mulr_natr 2!mulNr eqr_opp.
by move/eqP/mulIr => -> //; rewrite unitfE pnatr_eq0.
Qed.

End isometry_def.

Notation "''Iso_' n [ R ]" := (isometry R n)
  (at level 8, n at level 2, format "''Iso_' n [ R ]").

Notation "''CIso_' n [ R ]" := (central_isometry R n)
  (at level 8, n at level 2, format "''CIso_' n [ R ]").

Section sign_of_isometry.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Lemma frame_central_iso (f : 'CIso_3[R]) i j k :
  oframe i j k -> oframe (f i) (f j) (f k).
Proof.
case => *; apply mkOFrame; by
  rewrite /= central_isometry_preserves_norm ||
  rewrite /= central_isometry_preserves_dotmul.
Qed.

Lemma central_isometry_is_linear (f : 'CIso_3[R]) : linear f.
Proof.
move=> k /= a b.
have Hp : forall p, f p = p 0 0 *: f V.i + p 0 1 *: f V.j + p 0 2%:R *: f V.k.
  move=> p.
  have -> : f p = f p *d f V.i *: f V.i + f p *d f V.j *: f V.j + f p *d f V.k *: f V.k.
    rewrite -orthogonal_expansion //.
    apply frame_central_iso => //; exact: V.oframe.
  by rewrite 3!central_isometry_preserves_dotmul // -V.icoor -V.jcoor -V.kcoor.
rewrite Hp (Hp a) (Hp b) !mxE /= !(scalerDl, scalerDr).
rewrite !scalerA -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite addrC -!addrA.
Qed.

Lemma trans_ortho_of_iso (f : 'Iso_3[R]) :
  { trans : 'rV[R]_3 & { rot : 'M[R]_3 |
    (forall x : 'rV[R]_3, f x == x *m rot + trans) /\
    rot \is 'O_3[R] /\
    trans = f 0 } }.
Proof.
set T := f 0.
set Tm1f := fun x => f x - T. 
have Tm1f_is_iso : preserves_length Tm1f.
  rewrite /preserves_length => i j.
  by rewrite /Tm1f -addrA opprB 2!addrA subrK -(isoP f).
have Tm1f0 : Tm1f 0 = 0 by rewrite /Tm1f subrr.
have linearTm1f : linear (@mkCentralIsometry _ _ (mkIsometry Tm1f_is_iso) Tm1f0).
  by apply: central_isometry_is_linear.
have orthogonalTm1f : preserves_dotmul Tm1f.
  move=> x y /=.
  by rewrite (central_isometry_preserves_dotmul
    (@mkCentralIsometry _ _ (mkIsometry Tm1f_is_iso) Tm1f0)).
exists T.
case: (@matrix_of_iso _ _ (mkIsometry Tm1f_is_iso) linearTm1f) => g Hg.
exists (lin1_mx g); split; last first.
  split; last by done.
  apply orth_preserves_dotmul.
  move=> x y /=.
  move: (orthogonalTm1f x y).
  move: (Hg x) => /= ->.
  move: (Hg y) => /= -> <-.
  by rewrite 2!mul_rV_lin1.
move=> x.
have <- : Tm1f x = x *m lin1_mx g by rewrite mul_rV_lin1.
by rewrite subrK.
Qed.

Definition ortho_of_iso (f : 'Iso_3[R]) : 'M[R]_3 := projT1 (projT2 (trans_ortho_of_iso f)).

Definition trans_of_iso (f : 'Iso_3[R]) : 'rV[R]_3 := projT1 (trans_ortho_of_iso f).

Lemma trans_of_isoE (f : 'Iso_3[R]) : trans_of_iso f = f 0.
Proof.
rewrite /trans_of_iso; by case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
Qed.

Lemma ortho_of_iso_is_O f : ortho_of_iso f \is 'O_3[R].
Proof.
rewrite /ortho_of_iso; by case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
Qed.

Lemma ortho_of_iso_is_rot f u : u *m ortho_of_iso f = f u - trans_of_iso f.
Proof.
rewrite /ortho_of_iso /trans_of_iso.
case: (trans_ortho_of_iso _) => T [C [H1 [H2 H3]]] /=.
move: (H1 u) => /eqP ->; by rewrite addrK.
Qed.

Lemma img_vec_iso (f : 'Iso_3[R]) (a b : coordinate) :
  f b - f a = (b - a) *m (ortho_of_iso f).
Proof.
move/esym/eqP: (ortho_of_iso_is_rot f a).
move/esym/eqP: (ortho_of_iso_is_rot f b).
rewrite mulmxBl => /eqP <- /eqP <-; by rewrite opprB addrA subrK.
Qed.

Lemma ortho_of_iso_eq (f1 f2 : 'Iso_3[R]) :
  (forall i, iso f1 i = iso f2 i) ->
  ortho_of_iso f1 = ortho_of_iso f2.
Proof.
case: f1 f2 => [f1 Hf1] [f2 Hf2] /= f12.
rewrite /ortho_of_iso /= /trans_of_iso.
case: (trans_ortho_of_iso _) => x [x' /= [H1 [_ H2]]] /=.
case: (trans_ortho_of_iso _) => y [y' /= [K1 [_ K2]]] /=.
apply/eqP/mulmxP => u.
move: (H1 u); rewrite -subr_eq => /eqP <-.
move: (K1 u); rewrite -subr_eq => /eqP <-.
by rewrite H2 K2 2!f12.
Qed.

Definition iso_sgn (f : 'Iso_3[R]) : R := \det (ortho_of_iso f).

Record direct_isometry := mkDirectIsometry {
  diso :> 'Iso_3[R] ;
  disoP : iso_sgn diso == 1}.

End sign_of_isometry.

Notation "''SE_3' [ R ]" := (direct_isometry R)
  (at level 8, format "''SE_3' [ R ]").

Section tangent_vectors_and_frames.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

(* tangent vector *)
Record tvec (p : coordinate) := TVec {tvec_field :> vector}.
Definition vtvec p (v : tvec p) := let: TVec v := v in v.

Local Notation "p .-vec" := (tvec p) (at level 5).

Definition tframe_i p u1 u2 u3 (f : tframe p u1 u2 u3) : p.-vec := TVec p u1.
Definition tframe_j p u1 u2 u3 (f : tframe p u1 u2 u3) : p.-vec := TVec p u2.
Definition tframe_k p u1 u2 u3 (f : tframe p u1 u2 u3) : p.-vec := TVec p u3.

End tangent_vectors_and_frames.

Coercion vtvec_field_coercion := vtvec.
Notation "p .-vec" := (tvec p) (at level 5).

Section derivative_map.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

(* theorem 2.1, p. 104, o'neill *)
Definition dmap (f : 'Iso_3[R]) p (v : p.-vec) : (f p).-vec :=
  let C := ortho_of_iso f in
  TVec _ (v *m C).

Local Notation "f '`*'" := (@dmap f _) (at level 5, format "f `*").

Lemma dmap0 (f : 'Iso_3[R]) p : f `* (TVec p 0) = TVec (f p) 0.
Proof. by rewrite /dmap /= mul0mx. Qed.

Lemma derivative_map_preserves_length (f : 'Iso_3[R]) p (u v : p.-vec) :
  norm (vtvec (f`* u) - vtvec (f`* v)) = norm (vtvec u - vtvec v).
Proof.
rewrite /dmap /= -(mulmxBl (vtvec u) (vtvec v) (ortho_of_iso f) ).
by rewrite orth_preserves_norm // ortho_of_iso_is_O.
Qed.

Lemma dmap_iso_sgnP p e1 e2 e3 (tf : tframe p e1 e2 e3) (f : 'Iso_3[R]) :
  f`* (TVec p e1) *d (f `* (TVec p e2) *v f`* (TVec p e3)) = 
  iso_sgn f * (e1 *d (e2 *v e3)).
Proof.
case: tf => fo.
move: (orthogonal_expansion e1 (V.oframe R)).
set a11 := _ *d V.i. set a12 := _ *d V.j. set a13 := _ *d V.k => He1.
move: (orthogonal_expansion e2 (V.oframe R)).
set a21 := _ *d V.i. set a22 := _ *d V.j. set a23 := _ *d V.k => He2.
move: (orthogonal_expansion e3 (V.oframe R)).
set a31 := _ *d V.i. set a32 := _ *d V.j. set a33 := _ *d V.k => He3.
have e1a : e1 = row3 a11 a12 a13.
  apply/rowP => i; rewrite !mxE /=.
  case: ifPn => [/eqP ->|]; first by rewrite /a11 V.icoor.
  rewrite ifnot0 => /orP [] /eqP -> /=; by [rewrite /a12 V.jcoor | rewrite /a13 V.kcoor].
have e2a : e2 = row3 a21 a22 a23.
  apply/rowP => i; rewrite !mxE /=.
  case: ifPn => [/eqP ->|]; first by rewrite /a21 V.icoor.
  rewrite ifnot0 => /orP [] /eqP -> /=; by [rewrite /a22 V.jcoor | rewrite /a23 V.kcoor].
have e3a : e3 = row3 a31 a32 a33.
  apply/rowP => i; rewrite !mxE /=.
  case: ifPn => [/eqP ->|]; first by rewrite /a31 V.icoor.
  rewrite ifnot0 => /orP [] /eqP -> /=; by [rewrite /a32 V.jcoor | rewrite /a33 V.kcoor].
transitivity (\det ((ortho_of_iso f)^T *m 
  (triple_prod_mat (row3 a11 a12 a13) (row3 a21 a22 a23) (row3 a31 a32 a33))^T)).
  rewrite /= -det_tr trmx_mul trmxK mulmx_triple_prod_mat.
  by rewrite -crossmul_triple -e1a -e2a -e3a trmxK.
rewrite det_mulmx det_tr; congr (_ * _).
rewrite det_tr -crossmul_triple; by congr (_ *d (_ *v _)).
Qed.

Lemma dmap_preserves_crossmul p (u v : p.-vec) (f : 'Iso_3[R]) :
  f`* (TVec p (u *v v)) = 
    iso_sgn f *: vtvec (TVec (f p) ((f`* u) *v (f`* v))) :> vector.
Proof.
set tf : tframe _ _ _ _ := tframe_trans (TFrame 0 (V.oframe R)) p.
set u1p := tframe_i tf. set u2p := tframe_j tf. set u3p := tframe_k tf.
move: (orthogonal_expansion u (oframe_of_tframe tf)).
set u1 := _ *d V.i. set u2 := _ *d V.j. set u3 := _ *d V.k => Hu.
move: (orthogonal_expansion v (oframe_of_tframe tf)).
set v1 := _ *d V.i. set v2 := _ *d V.j. set v3 := _ *d V.k => Hv.
set e1 := f`* (TVec p u1p). set e2 := f`* (TVec p u2p). set e3 := f`* (TVec p u3p).
have Ku : f`* u = u1 *: vtvec e1 + u2 *: vtvec e2 + u3 *: vtvec e3 :> vector.
  by rewrite /= Hu 2!mulmxDl !scalemxAl.
have Kv : f`* v = v1 *: vtvec e1 + v2 *: vtvec e2 + v3 *: vtvec e3 :> vector.
  by rewrite /= Hv 2!mulmxDl !scalemxAl.
have f' : oframe e1 e2 e3.
  split => //.
  by rewrite orth_preserves_norm ?ortho_of_iso_is_O // V.normi.
  by rewrite orth_preserves_norm ?ortho_of_iso_is_O // V.normj.
  by rewrite orth_preserves_norm ?ortho_of_iso_is_O // V.normk.
  rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_O //.
  by case: (V.oframe R).
  rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_O //.
  by case: (V.oframe R).
  rewrite (proj2 (orth_preserves_dotmul (ortho_of_iso f)) _) ?ortho_of_iso_is_O //.
  by case: (V.oframe R).
have -> : iso_sgn f = frame_sgn f'.
  rewrite /frame_sgn dmap_iso_sgnP /=.
    by rewrite V.jcrossk dotmulvv V.normi expr1n mulr1.
  by apply (TFrame _ (V.oframe R)).
have : vtvec (TVec (f p) ((f`* u) *v (f`* v))) = 
         frame_sgn f' *: vtvec (f`* (TVec p (u *v v))) :> vector.
  rewrite /=.
  rewrite (@crossmul_oframe_sgn _ e1 e2 e3 _ (f`* u) u1 u2 u3 (f`* v) v1 v2 v3) //.
  rewrite /=.
  congr (_ *: _).
  have -> : V.i *m ortho_of_iso f = vtvec e1 by done.
  have -> : V.j *m ortho_of_iso f = vtvec e2 by done.
  have -> : V.k *m ortho_of_iso f = vtvec e3 by done.
  rewrite Hu Hv.
  do 2 rewrite linearD [in RHS]/=.
  rewrite 2!mulmxDl.
  (* on fait les remplacement veci *v vecj -> veck, veci *v veci -> 0, etc. *)
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite [in RHS]linearZ [in RHS]/=.
  rewrite crossmulC scalerN.
  rewrite linearD [in RHS]/=.
  rewrite [in X in _ = - (_ *: X) *m _ + _ + _]linearD.
  rewrite [in RHS]/=.
  rewrite (_ : V.i *v (u1 *: _) = 0); last by rewrite linearZ /= crossmulvv scaler0.
  rewrite (_ : V.i *v (u2 *: _) = u2 *: V.k); last by rewrite linearZ /= V.icrossj.
  rewrite (_ : V.i *v (u3 *: _) = - u3 *: V.j); last first.
    by rewrite linearZ /= V.icrossk scalerN scaleNr.
  rewrite add0r.
  rewrite mulNmx -[in RHS]scalemxAl [in RHS]mulmxDl.
  rewrite -![in RHS]scalemxAl.
  have -> : V.k *m ortho_of_iso f = vtvec e3 by done.
  have -> : V.j *m ortho_of_iso f = vtvec e2 by done.
  rewrite [in RHS]scalerDr.
  rewrite opprD.
  rewrite crossmulC [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + X + _]linearD [in X in _ = _ + X + _]/=.
  rewrite scaleNr scalerN opprK.
  rewrite (_ : _ *v _ = - u1 *: V.k); last first.
    by rewrite linearZ /= crossmulC V.icrossj scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite addr0.
  rewrite (_ : _ *v _ = u3 *: V.i); last by rewrite linearZ /= V.jcrossk.
  rewrite scaleNr opprK mulmxBl.
  rewrite -![in RHS]scalemxAl.
  have -> : V.i *m ortho_of_iso f = vtvec e1 by done.
  have -> : V.k *m ortho_of_iso f = vtvec e3 by done.
  rewrite scalerDr scalerN.
  rewrite crossmulC [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite [in X in _ = _ + _ + X]linearD [in X in _ = _ + _ + X]/=.
  rewrite opprD.
  rewrite (_ : _ *v _ = u1 *: V.j); last first.
    by rewrite linearZ /= crossmulC V.icrossk opprK.
  rewrite (_ : _ *v _ = - u2 *: V.i); last first.
    by rewrite linearZ /= crossmulC V.jcrossk scalerN scaleNr.
  rewrite (_ : _ *v _ = 0); last first.
    by rewrite linearZ /= crossmulvv scaler0.
  rewrite subr0 scaleNr opprK mulmxDl mulNmx.
  rewrite -![in RHS]scalemxAl.
  have -> : V.i *m ortho_of_iso f = vtvec e1 by done.
  have -> : V.j *m ortho_of_iso f = vtvec e2 by done.
  (* on a une expression uniquement avec des vtvec e1, etc. -> on identifie rhs et lhs *)
  rewrite -![in RHS]addrA [in RHS]addrC -[in RHS]addrA [in RHS]addrCA -[in RHS]addrA [in RHS]addrC.
  rewrite ![in RHS]addrA -[in RHS]addrA.
  congr (_ + _); last first.
    by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u1).
  rewrite scalerDr.
  rewrite -![in RHS]addrA [in RHS]addrCA [in RHS]addrC ![in RHS]addrA -addrA; congr (_ + _).
  by rewrite !scalerA -scaleNr -scalerDl addrC mulrC (mulrC u2).
  by rewrite scalerN !scalerA -scalerBl -scaleNr opprB mulrC (mulrC u1).
move=> ->; by rewrite scalerA -expr2 /iso_sgn -norm2 frame_sgn1 expr1n scale1r.
Qed.

Definition preserves_orientation (f : 'Iso_3[R]) := forall p (u v : p.-vec),
  f`* (TVec p (u *v v)) = TVec (f p) ((f`* u) *v (f`* v)) :> vector.

Lemma direct_iso_preserves_crossmul (f : 'SE_3[R]) : preserves_orientation f.
Proof. move=> p u v; by rewrite dmap_preserves_crossmul (eqP (disoP f)) scale1r. Qed.

Lemma preserves_crossmul_is_direct_iso p (u v : p.-vec) (f : 'Iso_3[R]) : 
  ~~ colinear u v ->
  f`* (TVec p (u *v v)) = TVec (f p) ((f`* u) *v (f`* v)) :> vector -> 
  iso_sgn f == 1.
Proof.
move=> uv0.
rewrite dmap_preserves_crossmul /iso_sgn => H.
apply/eqP.
move: (orthogonal_det (ortho_of_iso_is_O f)).
case: (lerP 0 (\det (ortho_of_iso f))) => K; first by rewrite ger0_norm.
rewrite ltr0_norm // => /eqP.
rewrite eqr_oppLR => /eqP K1.
rewrite K1 scaleN1r /= in H.
move/esym/opp_self : H.
move: (mulmxr_crossmulr (vtvec u) (vtvec v) (ortho_of_iso_is_O f)).
rewrite K1 scaleN1r.
move/esym/eqP.
rewrite eqr_oppLR => /eqP -> /eqP.
rewrite oppr_eq0 mul_mx_rowfree_eq0; last first.
  apply/row_freeP.
  exists (ortho_of_iso f)^T.
  apply/eqP.
  by rewrite -orthogonalE ortho_of_iso_is_O.
move: uv0.
rewrite /colinear.
by move/negbTE => ->.
Qed.

End derivative_map.

Notation "f '`*'" := (@dmap _ f _) (at level 5, format "f '`*'").

Section rigid_transformation_is_homogenous_transformation.

(*
Record object (A : frame) := {
  object_size : nat ;
  body : (coor A ^ object_size)%type }.
*)

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Lemma direct_iso_is_htrans (to : 'SE_3[R]) : 
  (exists T : transform R, forall i, to i = homogeneous_ap (i) T).
Proof.
case: to => /= to.
rewrite /iso_sgn /ortho_of_iso.
case: (trans_ortho_of_iso to) => t [r [rt0 - rt1]] /= r1.
have Hr : r^T \is 'SO_3[R].
  by rewrite rotationV rotationE (proj1 rt1).
set T := Transform t Hr.
exists T => i.
(* goal at this point: to i = homogeneous_ap (from i) T *)
rewrite homogeneous_apE /htrans_of_coordinate trmx_mul trmxK.
rewrite hmxE trmx_mul mulmxA.
set fromi' := (HCor (i)) *m _.
suff <- : HCor (to i) = fromi' *m (htrans_of_transform T)^T :> homogeneous R.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  by rewrite (cast_row_mx _ (to i)) row_mxKl castmx_id.
rewrite -[LHS]mulmx1 -trmx1.
move: (inv_htransP T) => /(congr1 trmx) => <-.
rewrite trmx_mul mulmxA; congr (_ *m _).
rewrite {}/fromi'.
suff : to i - t = i *m r.
  rewrite hcoor_inv_htrans => ->.
  by rewrite hcoor_hrot_of_transform trmxK.
move/eqP: (rt0 i) => ->.
by rewrite addrK.
Qed.

Lemma htrans_preserves_length (to : coordinate -> coordinate) :
  (exists T : transform R, forall i, to i = homogeneous_ap i T) ->
  preserves_length to.
Proof.
case=> [T /= HT] => /= m0 m1.
rewrite 2!HT -(htrans_of_vector_preserves_norm (m0 - m1) T).
by rewrite -htrans_of_coordinateB coord_of_hB.
Qed.

Definition preserves_angle (to : coordinate -> coordinate) :=
  forall i j k, vec_angle (j - i) (k - i) =
                vec_angle (to j - to i) (to k - to i).

Lemma htrans_preserves_angle to :
  (exists T : transform R, forall i, to i = homogeneous_ap (i) T) ->
  preserves_angle to.
Proof.
case=> [T /= HT] => /= m0 m1 k.
rewrite 3!HT /homogeneous_ap -2!coord_of_hB 2!htrans_of_coordinateB.
rewrite 2!coord_of_ht_htrans_of_vectorE -orth_preserves_vec_angle //.
rewrite orthogonalV; apply rotation_sub; by case: T HT.
Qed.

Lemma det_ortho_htrans (to : coordinate -> coordinate) (T : transform R) 
  (HT : (forall i, to i = homogeneous_ap i T)) :
  ortho_of_iso (mkIsometry (htrans_preserves_length (ex_intro _ _ HT))) =
  (rot T)^T.
Proof.
case: T HT => /= t r Hr HT.
have H : preserves_length (fun x => homogeneous_ap x (Transform t Hr)).
  move=> u v.
  by rewrite /homogeneous_ap -coord_of_hB htrans_of_coordinateB htrans_of_vector_preserves_norm.
set f1 := mkIsometry _.
suff : forall x : 'rV[R]_3, x *m (ortho_of_iso (mkIsometry H)) = x *m r^T.
  move=> Hx.
  apply/eqP/mulmxP.
  move=> u.
  rewrite -Hx /f1 /=.
  congr (_ *m _).
  apply ortho_of_iso_eq => /= x.
  by rewrite HT.
move=> x.
rewrite ortho_of_iso_is_rot /=.
rewrite trans_of_isoE /=.
rewrite /homogeneous_ap.
rewrite -coord_of_hB.
rewrite htrans_of_coordinateB subr0.
by rewrite coord_of_ht_htrans_of_vectorE /=.
Qed.

Lemma htrans_preserves_orientation (to : coordinate -> coordinate) (T : transform R) 
  (HT : (forall i, to i = homogeneous_ap i T)) :
  preserves_orientation (mkIsometry (htrans_preserves_length (ex_intro _ _ HT))).
Proof.
move=> p u v.
rewrite /= mulmxr_crossmulr /= ?ortho_of_iso_is_O //.
rewrite (_ : \det (ortho_of_iso _) = 1).
  by rewrite scale1r.
case: T HT => trans rot Hrot HT.
by rewrite det_ortho_htrans /= rotation_det // rotationV.
Qed.

End rigid_transformation_is_homogenous_transformation.

Section chains.

Variable R : rcfType.
Let coordinate := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := frame R.

Record joint := mkJoint {
  offset : R ;
  joint_angle : angle R }.

Record link := mkLink {
  length : R ;
  link_angle : angle R }.

Variable n' : nat.
Let n := n'.+1.
Variables chain : {ffun 'I_n -> frame * link * joint}.
Definition frames := fun i => (chain (insubd ord0 i)).1.1.
Definition links := fun i => (chain (insubd ord0 i)).1.2.
Definition joints := fun i => (chain (insubd ord0 i)).2.

(* by definition, zi = axis of joint i *)

Local Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Local Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Definition common_normal_xz (i : 'I_n) :=
  (framej (frames i.-1)) _|_ (framek (frames i)), (framei (frames i.-1)).

End chains.

Section anti_sym_def.

Variables (n : nat) (R : rcfType).

Definition anti := [qualify M : 'M[R]_n | M == - M^T].
Fact anti_key : pred_key anti. Proof. by []. Qed.
Canonical anti_keyed := KeyedQualifier anti_key.

Definition sym := [qualify M : 'M[R]_n | M == M^T].
Fact sym_key : pred_key sym. Proof. by []. Qed.
Canonical sym_keyed := KeyedQualifier sym_key.

End anti_sym_def.

Local Notation "''so_' n [ R ]" := (anti n R)
  (at level 8, n at level 2, format "''so_' n [ R ]").

Section skew.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Lemma antiE {n} M : (M \is 'so_n[R]) = (M == - M^T). Proof. by []. Qed.

Lemma symE {n} M : (M \is sym n R) = (M == M^T). Proof. by []. Qed.

Lemma anti_diag {n} M (i : 'I_n) : M \is 'so_n[R] -> M i i = 0.
Proof.
rewrite antiE -addr_eq0 => /eqP/matrixP/(_ i i); rewrite !mxE.
by rewrite -mulr2n -mulr_natr => /eqP; rewrite mulf_eq0 pnatr_eq0 orbF => /eqP.
Qed.

Lemma antiP {n} (A B : 'M[R]_n) : A \is 'so_n[R] -> B \is 'so_n[R] -> 
  (forall i j : 'I_n, (i < j)%N -> A i j = - B j i) -> A = B.
Proof.
move=> soA soB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by do 2 rewrite anti_diag //.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (soA); by rewrite antiE => /eqP ->; rewrite 2!mxE AB // opprK.
move=> {ij}ij; rewrite AB //.
move: (soB); rewrite antiE -eqr_oppLR => /eqP/matrixP/(_ i j).
rewrite !mxE => <-; by rewrite opprK.
Qed.

Lemma symP {n} (A B : 'M[R]_n) : A \in sym n R -> B \in sym n R -> 
  (forall i j : 'I_n, (i <= j)%N -> A i j = B i j) -> A = B.
Proof.
move=> symA symB AB; apply/matrixP => i j.
case/boolP : (i == j) => [/eqP ->|ij]; first by rewrite AB.
wlog : i j ij / (i < j)%N.
  move=> wlo; move: ij; rewrite neq_ltn => /orP [] ij.
    rewrite wlo //; by apply: contraL ij => /eqP ->; by rewrite ltnn.
  move: (symA) (symB) => /eqP -> /eqP ->; by rewrite 2!mxE AB // leq_eqVlt ij orbC.
by move=> {ij}ij; rewrite AB // leq_eqVlt ij orbC.
Qed.

(* (anti)symmetric parts of a matrix *)
Definition symp {n} (A : 'M[R]_n) := 1/2%:R *: (A + A^T).
Definition antip {n} (A : 'M[R]_n) := 1/2%:R *: (A - A^T).

Lemma symp_antip {n} (A : 'M[R]_n) : A = symp A + antip A.
Proof.
rewrite /symp /antip -scalerDr addrCA addrK -mulr2n- scaler_nat.
by rewrite scalerA div1r mulVr ?pnatr_is_a_unit // scale1r.
Qed.

Lemma antip_is_so {n} (M : 'M[R]_n) : antip M \is 'so_n[R].
Proof.
rewrite antiE /antip; apply/eqP; rewrite [in RHS]linearZ -scalerN /=.
by rewrite [in RHS]linearD /= opprD linearN /= opprK trmxK addrC.
Qed.

Lemma antip_scaler_closed {n} : GRing.scaler_closed 'so_n[R].
Proof.
move=> ? ?; rewrite antiE => /eqP H; by rewrite antiE linearZ /= -scalerN -H.
Qed.

Lemma sym_symp {n} (M : 'M[R]_n) : symp M \in sym n R.
Proof.
by apply/eqP; rewrite /symp linearZ /= [in RHS]linearD /= trmxK addrC.
Qed.

Lemma sym_oppr_closed {n} : oppr_closed (sym n R).
Proof. move=> /= M /eqP HM; apply/eqP; by rewrite linearN /= -HM. Qed.

Lemma sym_addr_closed {n} : addr_closed (sym n R).
Proof.
split; first by rewrite symE trmx0.
move=> /= A B; rewrite 2!symE => /eqP sA /eqP sB.
by rewrite symE linearD /= -sA -sB.
Qed.

Canonical SymOpprPred n := OpprPred (@sym_oppr_closed n).
Canonical SymAddrPred n := AddrPred (@sym_addr_closed n).

Lemma sym_scaler_closed {n} : GRing.scaler_closed (sym n R).
Proof. move=> ? ?; rewrite 2!symE => /eqP H; by rewrite linearZ /= -H. Qed.

Lemma sym1 {n} : 1%:M \is sym n R.
Proof. by rewrite symE trmx1. Qed.

Lemma mul_tr_vec_sym n (u : 'rV[R]_n) : u^T *m u \is sym n R.
Proof. apply/eqP; by rewrite trmx_mul trmxK. Qed.

(* TODO: Canonical? *)

Lemma trace_anti {n} (M : 'M[R]_n) : M \is 'so_n[R] -> \tr M = 0.
Proof.
move/anti_diag => m; by rewrite /mxtrace (eq_bigr (fun=> 0)) // sumr_const mul0rn.
Qed.

Definition skew_mx (w : vector) : 'M[R]_3 := - \matrix_i (w *v delta_mx 0 i).

Lemma skew_mx0 : skew_mx 0 = 0.
Proof.
by apply/matrixP => i j; rewrite !mxE -crossmul_triple crossmul0v dotmulv0 oppr0.
Qed.

Lemma skew_mxZ k (u : vector) : skew_mx (k *: u) = k *: skew_mx u.
Proof.
rewrite /skew_mx scalerN; congr (- _); apply/matrixP => i j.
by rewrite mxE crossmulC linearZ /= -scalerN crossmulC opprK mxE 2![in RHS]mxE.
Qed.

Lemma opp_skew_mx (u : vector) : - skew_mx u = skew_mx (- u).
Proof. by rewrite -scaleN1r -skew_mxZ scaleN1r. Qed.

Lemma anti_skew u : skew_mx u \is 'so_3[R].
Proof.
rewrite antiE; apply/eqP/matrixP => i j; rewrite !mxE -triple_prod_mat_perm_02.
by rewrite xrowE det_mulmx det_perm odd_tperm /= expr1 mulN1r.
Qed.

Lemma skew01 u : skew_mx u 0 1 = - u 0 2%:R.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, addr0, subr0). Qed.

Lemma skew02 u : skew_mx u 0 2%:R = u 0 1%:R.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, add0r, opprK). Qed.

Lemma skew10 u : skew_mx u 1 0 = u 0 2%:R.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew01 opprK. Qed.

Lemma skew12 u : skew_mx u 1 2%:R = - u 0 0.
Proof. by rewrite /skew_mx 2!mxE crossmulE !mxE /= !(mulr0, mulr1, subr0). Qed.

Lemma skew20 u : skew_mx u 2%:R 0 = - u 0 1%:R.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew02. Qed.

Lemma skew21 u : skew_mx u 2%:R 1 = u 0 0.
Proof. move/eqP: (anti_skew u) => ->; by rewrite 2!mxE skew12 opprK. Qed.

Lemma skewii u i : skew_mx u i i = 0.
Proof. by rewrite anti_diag // anti_skew. Qed.

Definition skewij := (skew01, skew10, skew02, skew20, skew21, skew12, skewii).

Lemma skew_mxE (u w : vector) : u *m skew_mx w = u *v w.
Proof.
rewrite [RHS]crossmulC -crossmulvN [u]row_sum_delta -/(mulmxr _ _) !linear_sum.
apply: eq_bigr=> i _; by rewrite !linearZ /= -rowE linearN /= rowK crossmulvN.
Qed.

Lemma skew_mxT (w : vector) : skew_mx w *m w^T = 0.
Proof.
rewrite -(trmxK (skew_mx w)) -trmx_mul.
move: (anti_skew w); rewrite antiE -eqr_oppLR => /eqP <-.
by rewrite mulmxN skew_mxE crossmulvv oppr0 trmx0.
Qed.

(* more general result for antisymmetric matrices? *)
Lemma det_skew_mx (u : vector) : \det (skew_mx u) = 0.
Proof.
case/boolP : (u == 0) => [/eqP ->|u0]; first by rewrite skew_mx0 det0.
apply/eqP/det0P; exists u => //; by rewrite skew_mxE crossmulvv.
Qed.

Lemma sqr_antip (M : 'M[R]_3) : M \is 'so_3[R] ->
  M ^+ 2 = triple_prod_mat
  (row3 (- M 0 1 ^+ 2 - M 0 2%:R ^+ 2) (- M 1 2%:R * M 0 2%:R) (M 0 1 * M 1 2%:R))
  (row3 (- M 1 2%:R * M 0 2%:R) (- M 0 1 ^+ 2 - M 1 2%:R ^+ 2) (- M 0 1 * M 0 2%:R)) 
  (row3 (M 1 2%:R * M 0 1) (- M 0 2%:R * M 0 1) (- M 0 2%:R ^+ 2 - M 1 2%:R ^+ 2)).
Proof.
move=> a; apply/matrixP => i j.
rewrite !mxE /= sum3E /a.
case: ifPn => [/eqP ->|]; first rewrite [in RHS]mxE /=.
  case: ifPn => [/eqP -> |].
    rewrite anti_diag // mulr0 add0r {2}(eqP a) 2!mxE mulrN -expr2; congr (_ + _).
    by rewrite {2}(eqP a) !mxE mulrN -expr2.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !anti_diag //; simp => //=.
  by rewrite {2}(eqP a) 2!mxE mulrN mulrC.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !mxE /=.
  case: ifPn => [/eqP ->|].
    rewrite !anti_diag //; simp => /=; by rewrite {2}(eqP a) 2!mxE mulrN.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !anti_diag //; simp => //=.
    rewrite {1}(eqP a) 2!mxE mulNr -expr2; congr (_ + _).
    by rewrite {2}(eqP a) 2!mxE mulrN -expr2.
    by rewrite {1}(eqP a) 2!mxE mulNr.
case: ifPn => [/eqP ->|].
  rewrite !anti_diag //; simp => /=.
  by rewrite {1}(eqP a) 2!mxE {2}(eqP a) 2!mxE mulrN mulNr opprK.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !anti_diag //; simp => //=.
  by rewrite {1}(eqP a) 2!mxE mulNr.
rewrite {1}(eqP a) 2!mxE mulNr -expr2; congr (_ + _).
by rewrite {1}(eqP a) 2!mxE mulNr -expr2.
Qed.

Lemma sqr_skewE (u : 'rV[R]_3) : let a := skew_mx u in 
  a ^+ 2 = triple_prod_mat
    (row3 (- u 0 2%:R ^+ 2 - u 0 1 ^+ 2) (u 0 0 * u 0 1) (u 0 0 * u 0 2%:R))
    (row3 (u 0 0 * u 0 1) (- u 0 2%:R ^+ 2 - u 0 0 ^+ 2) (u 0 1 * u 0 2%:R))
    (row3 (u 0 0 * u 0 2%:R) (u 0 1 * u 0 2%:R) (- u 0 1%:R ^+ 2 - u 0 0 ^+ 2)).
Proof.
move=> a; rewrite (sqr_antip (anti_skew u)); congr triple_prod_mat.
by rewrite !skewij sqrrN; simp; rewrite (mulrC (u 0 2%:R)).
by rewrite !skewij 2!sqrrN; simp; rewrite (mulrC (u 0 2%:R)).
by rewrite !skewij sqrrN; simp.
Qed.

Lemma sym_sqr_skew u : skew_mx u ^+ 2 \is sym 3 R.
Proof.
rewrite symE sqr_skewE.
apply/eqP/matrixP => i j; rewrite !mxE /=.
case: ifPn => [i0|].
  rewrite !mxE /=.
  case: ifPn => [j0|]; first by rewrite !mxE /= i0.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE /= i0.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite !mxE /=.
  case: ifPn => [j0|]; first by rewrite !mxE.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE.
rewrite !mxE /=.
  case: ifPn => [j0|]; first by rewrite !mxE.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite mxE.
Qed.

(* TODO: move?*)
Lemma mul_tr_vecij (u : 'rV[R]_3) i j : (u^T *m u) i j = u 0 i * u 0 j.
Proof.
by rewrite mxE (bigD1 ord0) //= big1 ?mxE ?addr0 // => i0; rewrite (ord1 i0).
Qed.

Lemma skew_mx2 u : skew_mx u ^+ 2 = u^T *m u - (norm u ^+ 2)%:A.
Proof.
apply (symP (sym_sqr_skew u)); last move=> i j.
  rewrite rpredD //; last by rewrite rpredN sym_scaler_closed // sym1.
  by rewrite mul_tr_vec_sym.
rewrite [in X in _ -> _ = X]mxE mul_tr_vecij.
case/boolP : (i == 0) => [/eqP -> _|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite sqr_skewE 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE 
      sum3E -!expr2 -addrA addrCA addrAC -addrA.
  rewrite ifnot0 => /orP [] /eqP ->; by rewrite sqr_skewE 5!mxE /= mulr0 subr0.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP -> //|].
  rewrite ifnot0 => /orP [] /eqP -> _.
    rewrite sqr_skewE 5!mxE /= -expr2 mulr1; apply/eqP.
    by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE 
      sum3E -!expr2 addrAC.
    by rewrite sqr_skewE 5!mxE /= mulr0 subr0.
case/boolP : (j == 0) => [/eqP -> //|].
rewrite ifnot0 => /orP [] /eqP -> // _.
rewrite sqr_skewE 5!mxE /= -expr2 mulr1; apply/eqP.
by rewrite -eqr_opp 2!opprB opprK eq_sym subr_eq -dotmulvv dotmulE sum3E -!expr2.
Qed.

Lemma skew_mx3 (u : 'rV[R]_3) : let a := skew_mx u in a ^+ 3 = - (norm u) ^+ 2 *: a.
Proof.
move=> a.
rewrite exprS sqr_skewE.
apply/matrixP => i j.
rewrite mxE /= sum3E.
do 3 rewrite [triple_prod_mat _ _ _ _ _]mxE /=.
do 3 rewrite [row3 _ _ _ _ _]mxE /=.
move: (dotmulvv u).
rewrite dotmulE sum3E => /eqP H.
rewrite -{1}eqr_opp 2!opprD -!expr2 in H.
move: (H); rewrite subr_eq addrC => /eqP ->.
move: (H); rewrite addrAC subr_eq addrC => /eqP ->.
move: (H); rewrite -addrA addrC subr_eq addrC => /eqP ->.
rewrite [in RHS]mxE.
case/boolP : (i == 0) => [/eqP -> |].
  case: ifPn => [/eqP ->|].
    rewrite /a !skewij; simp => /=.
    by rewrite addrC !mulNr mulrAC -mulrA mulrC subrr.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a !skewij; simp => /=.
    rewrite -expr2 -mulrN mulrC -mulrDl; congr (_ * _).
    by rewrite opprD opprK subrK.
  rewrite -(mulrC (u 0 1)) -mulrA -mulrDr -mulNr mulrC; congr (_ * _).
  by rewrite addrC mulNr addrK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case: ifPn => [/eqP ->|].
    rewrite /a !skewij; simp => /=.
    rewrite mulrC -mulrDl -[in RHS]mulNr; congr (_ * _).
    by rewrite mulNr -expr2 addrK.
  rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a !skewij; simp => /=.
    by rewrite -mulrA mulrC 2!mulNr -mulrBl subrr mul0r.
  rewrite -mulrA mulrC -mulrA -mulrBr mulrC; congr (_ * _).
  by rewrite opprD opprK addrCA -expr2 subrr addr0.
case: ifPn => [/eqP ->|].
  rewrite /a !skewij; simp => /=.
  rewrite -mulrN mulrC -mulrDl; congr (_ * _).
  by rewrite opprD opprK -expr2 subrK.
rewrite ifnot0 => /orP [] /eqP -> /=; rewrite /a !skewij; simp => /=.
  rewrite -mulrA mulrCA -mulrDr -[in RHS]mulNr [in RHS]mulrC; congr (_ * _).
  by rewrite addrC mulNr -expr2 addrK.
by rewrite -mulrA mulrCA -mulrA -mulrDr addrC mulNr subrr mulr0.
Qed.

Lemma skew_mx4 w : norm w = 1 -> skew_mx w ^+ 4 = - skew_mx w ^+ 2.
Proof. move=> w1; by rewrite exprS skew_mx3 // w1 expr1n scaleN1r mulrN -expr2. Qed.

Lemma mxtrace_sqr_skew_mx u : \tr ((skew_mx u) ^+ 2) = - (2%:R * (norm u) ^+ 2).
Proof.
rewrite /mxtrace sum3E sqr_skewE.
do 6 rewrite mxE /=.
rewrite -opprB opprK !addrA addrC !addrA -2!addrA.
rewrite [in RHS]mulr2n [in RHS]mulrDl [in RHS]opprD mul1r; congr (_ + _).
  rewrite -opprB opprK; congr (- _).
  by rewrite addrC addrA -dotmulvv dotmulE sum3E -!expr2.
rewrite -opprB -opprD opprK; congr (- _).
by rewrite addrC -addrA addrCA addrA  -dotmulvv dotmulE sum3E -!expr2.
Qed.

(* TODO: move? *)
Lemma row'0_triple_prod_mat tmp (XM : 'M[{poly R}]_3) :
  row' ord0 (triple_prod_mat tmp (row 1 XM) (row 2%:R XM)) = row' ord0 XM.
Proof.
rewrite row'_triple_prod_mat /=.
apply/matrixP => i j; rewrite !mxE.
case: ifPn => [/eqP ->|].
  by rewrite !mxE; simp_ord.
case: i => [] [] // [] // i _ /=.
by rewrite !mxE; simp_ord.
Qed.

(* TODO: move? *)
Lemma diag_sqr {n} (M : 'M[R]_n) (i : 'I_n) : (M *m M) i i = (row i M) *d (col i M)^T.
Proof.
rewrite mxE dotmulE; apply/eq_bigr => /= j _; by rewrite 3!mxE.
Qed.

Lemma tr_sqr (M : 'M[R]_3) : \tr (M^+2) = \sum_(i < 3) (row i M) *d (col i M)^T.
Proof. apply/eq_bigr => i _; by rewrite diag_sqr. Qed.

Lemma tr_sqr3 (M : 'M[R]_3) : \tr (M *m M) =
  \sum_i (M i i ^+2) + M 0 1 * M 1 0 *+ 2 + M 0 2%:R * M 2%:R 0 *+ 2 +
  M 1 2%:R * M 2%:R 1 *+ 2.
Proof.
rewrite sum3E tr_sqr sum3E !dotmulE !sum3E !mxE -!expr2 -!addrA; congr (_ + _).
do 3 rewrite addrC -!addrA; congr (_ + _).
do 3 rewrite addrC -!addrA; congr (_ + _).
congr (_ + _).
rewrite addrC -!addrA mulrC; congr (_ + _).
rewrite addrC -!addrA mulrC; congr (_ + _).
rewrite addrC -!addrA; congr (_ + _).
by rewrite mulrC.
Qed.

Lemma sqr_tr3 (M : 'M[R]_3) : (\tr M) ^+ 2 =
  \sum_i (M i i ^+2) + M 0 0 * M 1 1 *+ 2 + (M 0 0 + M 1 1) * M 2%:R 2%:R *+ 2.  
Proof.
rewrite /mxtrace sum3E 2!sqrrD sum3E .
rewrite -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA; congr (_ + _).
Qed.

(* TODO: move? *)
Lemma char_poly3_coef1 (M : 'M[R]_3) :
  let Z := 1 / 2%:R * (\tr M ^+ 2 - \tr (M ^+ 2)) in
  (char_poly M)`_1 = Z.
Proof.
move=> Z.
rewrite /char_poly /char_poly_mx det_mx33 !mxE mulr1n mulr0n !add0r.
rewrite !mulNr !mulrN !opprK.
rewrite !coefD.
(* 1 *)
rewrite [X in X + _ + _](_ : _ = M 0 0 * (M 2%:R 2%:R + M 1 1) +
   (M 1 1 * M 2%:R 2%:R - M 2%:R 1 * M 1 2%:R)); last first.
  rewrite coefM sum2E coefD coefX add0r coefN coefC [- _]/=.
  rewrite subn0 coefD.
  rewrite coefM sum2E subn0 coefD coefX add0r coefN (_ : _`_0 = M 1 1); last by rewrite coefC.
  rewrite coefD coefX coefN coefC subr0 mulr1.
  rewrite coefD coefN coefX coefN coefC subr0 mul1r.
  rewrite subnn coefD coefX add0r coefN coefC [in X in - M 1 1 - X]/=.
  rewrite coefM sum2E coefC coefC mulr0 add0r coefC mul0r subr0.
  rewrite coefD coefX coefN coefC subr0 mul1r.
  rewrite coefD coefM sum1E coefD coefX add0r coefN coefC [in X in - X * _`_ _]/=.
  rewrite coefD coefX add0r coefN coefC mulrN !mulNr opprK.
  rewrite coefN coefM sum1E coefC coefC [in X in M 1 1 * _ - X]/=.
  by rewrite -opprB mulrN 2!opprK.
rewrite [X in _ + X + _](_ : _ = - M 0 1 * M 1 0); last first.
  rewrite coefN coefM sum2E coefC [in X in X * _]/= subnn.
  rewrite coefD subn0 coefM sum2E.
  rewrite subn0 subnn coefC coefC mulr0 add0r.
  rewrite coefC mul0r add0r.
  rewrite coefM sum2E subn0 subnn coefC coefD coefX coefN coefC subr0 mulr1.
  rewrite coefC mul0r addr0 coefC mul0r addr0.
  by rewrite mulNr.
rewrite [X in _ + _ + X](_ : _ = - M 0 2%:R * M 2%:R 0); last first.
  rewrite coefN coefM sum2E subn0 subnn coefC.
  rewrite [in X in X * _]/=.
  rewrite coefD coefM sum2E subn0 coefC coefC mulr0 add0r.
  rewrite coefC mul0r add0r coefM sum2E subn0 subnn coefC [in X in X * _`_1]/=.
  by rewrite coefD coefX coefN coefC subr0 mulr1 coefC mul0r addr0 coefC mul0r addr0 mulNr.
rewrite /Z.
apply/(@mulrI _ 2%:R); first exact: pnatr_is_a_unit.
rewrite mulrA div1r divrr ?pnatr_is_a_unit // mul1r.
rewrite sqr_tr3.
rewrite tr_sqr3.
rewrite 3!opprD -[in RHS]addrAC [in RHS](addrC (\sum_ _ _)) 3![in RHS]addrA addrK.

rewrite mulrDr addrC mulNr mulrN (mulrC 2%:R) mulr_natr.
rewrite -2![in RHS]addrA [in RHS]addrC -[in RHS]addrA; congr (_ + _).
rewrite mulrDr addrC mulNr mulrN (mulrC 2%:R) mulr_natr.
rewrite [in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite addrA mulrDr addrC mulrN (mulrC 2%:R) mulr_natr mulrC -addrA; congr (_ + _).
rewrite (mulrC 2%:R) mulr_natr.
rewrite mulrDr.
rewrite mulrDl.
rewrite mulr2n.
rewrite [in RHS]mulr2n.
rewrite [in X in _ = _ + X]mulr2n.
rewrite -!addrA; congr (_ + _).
rewrite addrC -!addrA; congr (_ + (_ + _)).
by rewrite addrCA.
Qed.

Lemma char_poly3 (M : 'M[R]_3) :
  let Z := 1 / 2%:R * ((\tr M) ^+ 2 - \tr (M ^+ 2)) in
  char_poly M = 'X^3 - (\tr M) *: 'X^2 + Z *: 'X - (\det M)%:P.
Proof.
move=> Z.
rewrite -(coefK (char_poly M)) (size_char_poly M).
apply/polyP.
case. (* coef0 *)
  rewrite coef_poly char_poly_det !coef_add_poly !coef_opp_poly !coefZ.
  rewrite !coefX !coefXn add0r mulr0 oppr0 mulr0 add0r add0r coefC /=.
  by rewrite exprS sqrrN expr1n mulr1 mulN1r.
case; last first.
  case. (* coef2 *)
    rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
    by rewrite add0r mulr0 mulr1 addr0 coefC subr0 char_poly_trace.
  case; last first. (* coef n >= 4 *)
    move=> n.
    rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
    by rewrite add0r mulr0 mulr0 coefC subr0 addr0 oppr0.
  (* coef3 *)
  rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
  rewrite mulr0 subr0 mulr0 addr0 coefC subr0; apply/eqP.
  rewrite (_ : _`_3 = lead_coef (char_poly M)); last first.
    by rewrite lead_coefE size_char_poly.
  by rewrite -monicE char_poly_monic.
(* coef1 *)
rewrite coef_poly !coef_add_poly !coef_opp_poly !coefZ !coefX !coefXn.
rewrite add0r mulr1 mulr0 oppr0 add0r coefC subr0.
suff : (char_poly M)`_1 = Z by move=> ->.
by rewrite char_poly3_coef1.
Qed.

Lemma char_poly_skew_mx (u : 'rV[R]_3) : norm u = 1 -> 
  char_poly (skew_mx u) = 'X^3 + 'X.
Proof.
move=> u1.
rewrite char_poly3 det_skew_mx subr0 trace_anti ?anti_skew //.
rewrite scale0r subr0 expr0n add0r mulrN mxtrace_sqr_skew_mx mulrN opprK.
by rewrite u1 expr1n mulr1 div1r mulVr ?unitfE ?pnatr_eq0 // scale1r.
Qed.

Definition skew_mx_eigenvalues : seq R[i] := [:: 0; 'i; 0 -i* 1].

Ltac eigenvalue_skew_mx_eval_poly := 
  rewrite /map_poly horner_poly size_addl; [ |by rewrite size_polyXn size_polyX] ;
  rewrite size_polyXn sum4E !coefD !coefXn !coefX !add0r !mul0r !mul1r !add0r !addr0 mul1r.

Lemma eigenvalue_skew_mx (u : 'rV[R]_3) : norm u = 1 -> 
  eigenvalue (map_mx (fun x => x%:C) (skew_mx u)) =1 [pred k | k \in skew_mx_eigenvalues].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly (char_poly_skew_mx u1).
apply/rootP.
case: ifPn => [|Hk].
  rewrite inE => /orP [/eqP ->|]; first by rewrite /= horner_map !hornerE.
  rewrite inE => /orP [/eqP ->|].
    eigenvalue_skew_mx_eval_poly.
    by rewrite expr1 exprS sqr_i mulrN1 subrr.
  rewrite inE => /eqP ->.
  eigenvalue_skew_mx_eval_poly.
  apply/eqP. simpc. by rewrite addrC subrr eq_complex /= eqxx.
apply/eqP; apply: contra Hk.
eigenvalue_skew_mx_eval_poly.
rewrite (exprS _ 2) -{1}(mulr1 k) -mulrDr mulf_eq0 => /orP [/eqP ->|].
  by rewrite inE eqxx.
rewrite eq_sym addrC -subr_eq add0r -sqr_i eqf_sqr => /orP [/eqP <-|].
  by rewrite !inE eqxx orbC.
rewrite -eqr_oppLR => /eqP <-.
rewrite !inE orbA; apply/orP; right.
by rewrite eq_complex /= oppr0 !eqxx.
Qed.

Lemma skew_mxC (u : vector) : let a := skew_mx u in
  (1 + a) * (1 - a) = (1 - a) * (1 + a).
Proof.
move=> a.
rewrite mulrDl mul1r mulrDr mulr1 mulrN addrA subrK.
by rewrite mulrDr mulr1 mulrBl mul1r addrA subrK.
Qed.

Lemma det_skew_mx1 (u : vector) : \det (1 - skew_mx u) = 1 + norm u ^+ 2.
Proof.
set a := skew_mx u.
rewrite det_mx33 [a]lock !mxE /=. simp.
rewrite -lock /a !skewij subr0. simp.
rewrite mulrDr mulrBr opprB.
rewrite addrAC !addrA mulrCA subrK.
rewrite -!addrA addrC !addrA.
by rewrite -sqr_norm addrC.
Qed.

Lemma skew_mx_inv (u : vector) : 1 - skew_mx u \is a GRing.unit.
Proof.
set a := skew_mx u.
by rewrite unitmxE unitfE det_skew_mx1 paddr_eq0 // ?ler01 // ?sqr_ge0 // negb_and oner_neq0.
Qed.

Definition cayley_of_skew (u : vector) := (1 - skew_mx u)^-1 * (1 + skew_mx u).

Lemma cayley_of_skew_is_O u : cayley_of_skew u \is 'O_3[R].
Proof.
rewrite orthogonalE /cayley_of_skew.
set a := skew_mx u.
rewrite trmx_mul trmxV.
do 2 rewrite linearD /= trmx1.
rewrite [in X in _ * _ * (_ * X) == _]linearN /=.
move: (anti_skew u); rewrite antiE eq_sym eqr_oppLR => /eqP ->.
rewrite (opprK (skew_mx u)) -/a -mulrA (mulrA (1 + a)) skew_mxC -/a.
rewrite !mulrA mulVr ?skew_mx_inv // mul1r divrr //.
by rewrite -(opprK a) opp_skew_mx skew_mx_inv.
Qed.

Lemma det_caley u : \det (cayley_of_skew u) = 1.
Proof.
rewrite /cayley_of_skew det_mulmx det_inv det_skew_mx1.
rewrite -(opprK (skew_mx u)) opp_skew_mx det_skew_mx1 normN.
by rewrite mulVr // unitfE paddr_eq0 ?ler01 // ?sqr_ge0 // oner_eq0.
Qed.

Lemma cayley_of_skew_is_SO u : cayley_of_skew u \is 'SO_3[R].
Proof. by rewrite rotationE cayley_of_skew_is_O det_caley eqxx. Qed.

Definition skew_of_ortho (Q : 'M[R]_3) := (Q - 1) * (Q + 1)^-1.

Lemma skew_of_ortho_is_skew Q : Q \is 'O_3[R] -> skew_of_ortho Q \is 'so_3[R].
Proof.
move=> HQ.
rewrite antiE /skew_of_ortho.
rewrite trmx_mul trmxV.
rewrite linearD /= trmx1.
rewrite linearD /= linearN /= trmx1.
move: (HQ).
rewrite orthogonalEinv => /andP[Qinv] /eqP <-.
rewrite mulmxE -mulrN opprB idmxE; apply/eqP.
rewrite -[in RHS](mul1r (1 - Q^-1)).
rewrite -unitrV in Qinv.
rewrite -{4}(divrr Qinv).
rewrite -mulrA invrK (mulrBr Q) mulr1 divrr; last by rewrite -unitrV.
rewrite mulrA.
Abort.

Definition unskew (M : 'M[R]_3) := row3 (- M 1 2%:R) (M 0 2%:R) (- M 0 1).

Lemma skew_mxK w : unskew (skew_mx w) = w.
Proof.
apply/rowP => i; rewrite 3!mxE /=.
case: ifPn => [/eqP ->|]; first by rewrite crossmulE /= !mxE /=; simp.
by rewrite ifnot0 => /orP [] /eqP -> /=; rewrite !skewij // opprK.
Qed.

Lemma unskewK (M : 'M[R]_3) : M \is 'so_3[R] -> skew_mx (unskew M) = M.
Proof.
move=> soM.
rewrite /unskew.
apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite skewij anti_diag.
  rewrite ifnot0 => /orP [] /eqP -> /=; by rewrite skewij mxE //= opprK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  case/boolP : (j == 0) => [/eqP ->|].
    by rewrite skewij mxE //= {1}(eqP soM) 2!mxE opprK.
  rewrite ifnot0 => /orP [] /eqP -> /=.
    by rewrite skewij anti_diag.
  by rewrite skewij mxE //= opprK.
case/boolP : (j == 0) => [/eqP ->|].
  by rewrite skewij mxE /= {1}(eqP soM) !mxE opprK.
rewrite ifnot0 => /orP [] /eqP -> /=.
  by rewrite skewij !mxE /= {1}(eqP soM) !mxE opprK.
by rewrite skewij anti_diag.
Qed.

Lemma unskew_mxZ k (M : 'M[R]_3) : unskew (k *: M) = k *: unskew M.
Proof.
apply/rowP => i; rewrite !mxE /=.
case: ifPn => [_|]; first by rewrite mulrN.
rewrite ifnot0 => /orP [] /eqP -> //=; by rewrite mulrN.
Qed.

Lemma skew_inj (u v : 'rV[R]_3) : skew_mx u = skew_mx v -> u = v.
Proof. move=> H; by rewrite -(skew_mxK u) H skew_mxK. Qed.

Section axial_vector.

Definition axial_vec (M : 'M[R]_3) : 'rV[R]_3 :=
  (*(1 / 2%:R) *:*) row3 (M 2%:R 1 - M 1 2%:R) (M 0 2%:R - M 2%:R 0) (M 1 0 - M 0 1).

Lemma skew_axial_vec r : skew_mx (axial_vec r) = r - r^T.
Proof.
apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|]; first by rewrite skewii ![in RHS]mxE subrr.
  rewrite ifnot0 => /orP [] /eqP ->; by rewrite skewij !mxE /= ?opprB.
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP ->|]; first by rewrite skewij !mxE.
  rewrite ifnot0 => /orP [] /eqP ->.
    by rewrite skewii !mxE subrr.
  by rewrite skewij !mxE /= opprB.
case/boolP : (j == 0) => [/eqP ->|]; first by rewrite skewij !mxE /= opprB.
rewrite ifnot0 => /orP [] /eqP ->; by rewrite skewij !mxE ?subrr.
Qed.

Lemma axial_vecE r : axial_vec r = unskew (r - r^T).
Proof.
apply/skew_inj; rewrite skew_axial_vec unskewK //.
by rewrite antiE linearD /= linearN /= trmxK opprB.
Qed.

Lemma axial_vecP (M : 'M[R]_3) u : u *v axial_vec M = u *m antip M.
Proof.
rewrite axial_vecE /antip -skew_mxE unskewK.
Abort.

Lemma is_eigenvector1_colinear r (Hr : r \is 'SO_3[R]) n :
  (n <= eigenspace r 1)%MS -> colinear n (axial_vec r).
Proof.
move=> Hn.
have HnT : n *m r^T = n.
  move/eigenspace_trmx : Hn => /(_ (rotation_sub Hr))/eigenspaceP.
  by rewrite scale1r.
set Q := r^T - r.
have nrrT : n *m Q = 0.
 rewrite mulmxDr [in LHS]mulmxN HnT.
 move/eigenspaceP : Hn; rewrite scale1r => ->.
 by rewrite subrr.
have skewrrT : skew_mx (- axial_vec r) = Q.
  rewrite axial_vecE // -scaleN1r skew_mxZ scaleN1r unskewK ?opprB //.
  by rewrite antiE linearD /= linearN /= trmxK opprB.
move/eqP: nrrT.
by rewrite -skewrrT skew_mxE crossmulvN oppr_eq0.
Qed.

Lemma axial_vec_vec_eigenspace r (Hr : r \is 'SO_3[R]) :
  (axial_vec r <= eigenspace r 1)%MS.
Proof.
apply/eigenspaceP.
rewrite scale1r.
case: (euler Hr) => inv /andP[inv0 /eqP Hinv].
have : (inv <= eigenspace r 1)%MS by apply/eigenspaceP; rewrite scale1r.
move/is_eigenvector1_colinear.
move/(_ Hr) => Hcol.
have [k Hk] : exists k, axial_vec r = k *: inv.
  case/colinearP : Hcol => [/eqP ->| [_ [k [Hk ukv]]]].
    exists 0; by rewrite scale0r.
  exists (1 / k).
  rewrite ukv scalerA div1r mulVr ?scale1r // unitfE.
  apply: contra inv0; rewrite ukv => /eqP ->; by rewrite scale0r.
by rewrite Hk -scalemxAl Hinv.
Qed.

End axial_vector.

End skew.

Section exponential_map_rot.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Implicit Type u v : vector.
Implicit Type a b : angle R.

Definition exp_rot a (M : 'M[R]_3) : 'M_3 :=
  1 + sin a *: M + (1 - cos a) *: M ^+ 2.

Local Notation "'`e^(' a ',' M ')'" := (exp_rot a M) (format "'`e^(' a ','  M ')'").

Lemma mul_exp_rot a b M : M ^+ 3 = - M -> `e^(a, M) * `e^(b, M) = `e^(a + b, M).
Proof.
move=> cube_u.
rewrite /exp_rot sinD cosD !mulrDr !mulrDl.
simp => /=.
rewrite -scalerCA -2!scalerAl -expr2.
rewrite -scalerAl -scalerAr -exprSr cube_u (scalerN (sin b) M) (scalerN (1 - cos a)).
rewrite -(scalerAl (sin a)) -(scalerCA (1 - cos b) M) -(scalerAl (1 - cos b)) -exprS.
rewrite cube_u (scalerN _ M) (scalerN (sin a) (_ *: _)).
rewrite -!addrA; congr (_ + _).
do 2 rewrite addrC -!addrA. 
rewrite addrC scalerA (mulrC (sin b)) -!addrA.
rewrite [in RHS]addrC [in RHS]scalerBl [in RHS]scalerBl [in RHS]opprB [in RHS]addrCA -![in RHS]addrA; congr (_ + _).
rewrite scalerBl scale1r opprB (scalerA (cos a)) -!addrA.
rewrite [in RHS]scalerDl ![in RHS]addrA [in RHS]addrC -[in RHS]addrA; congr (_ + _).
rewrite addrC ![in LHS]addrA addrK.
rewrite -![in LHS]addrA addrC scalerBl scale1r scalerBr opprB scalerA -![in LHS]addrA.
rewrite [in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite addrCA ![in LHS]addrA subrK -scalerCA -2!scalerAl -exprD.
rewrite (_ : M ^+ 4 = - M ^+ 2); last by rewrite exprS cube_u mulrN -expr2.
rewrite 2!scalerN scalerA.
rewrite addrC -scaleNr -2!scalerDl -scalerBl; congr (_ *: _).
rewrite -!addrA; congr (_ + _).
rewrite mulrBr mulr1 mulrBl mul1r opprB opprB !addrA subrK addrC.
rewrite -(addrC (cos a)) !addrA -(addrC (cos a)) subrr add0r.
by rewrite addrC addrA subrr add0r mulrC.
Qed.

Lemma tr_exp_rot a M : `e^(a, M)^T = `e^(a, M^T).
Proof.
by rewrite /exp_rot !linearD /= !linearZ /= trmx1 expr2 trmx_mul expr2.
Qed.

Lemma inv_exp_rot a M : M ^+ 4 = - M ^+ 2 -> `e^(a, M) * `e^(a, -M) = 1.
Proof.
move=> aM.
case/boolP : (cos a == 1) => [/eqP cphi|cphi].
  by rewrite /exp_rot cphi subrr 2!scale0r !addr0 scalerN (cos1sin0 cphi) scale0r addr0 subr0 mulr1.
rewrite /exp_rot !mulrDr !mulrDl !mulr1 !mul1r -[RHS]addr0 -!addrA; congr (_ + _).
rewrite !addrA (_ : (- M) ^+ 2 = M ^+ 2); last by rewrite expr2 mulNr mulrN opprK -expr2.
rewrite -!addrA (addrCA (_ *: M ^+ 2)) !addrA scalerN subrr add0r.
rewrite (_ : (1 - _) *: _ * _ = - (sin a *: M * ((1 - cos a) *: M ^+ 2))); last first.
  rewrite mulrN; congr (- _).
  rewrite -2!scalerAr -!scalerAl -exprS -exprSr 2!scalerA; congr (_ *: _).
  by rewrite mulrC.
rewrite -!addrA (addrCA (- (sin a *: _ * _))) !addrA subrK.
rewrite mulrN -scalerAr -scalerAl -expr2 scalerA -expr2.
rewrite -[in X in _ - _ + _ + X = _]scalerAr -scalerAl -exprD scalerA -expr2.
rewrite -scalerBl -scalerDl sin2cos2.
rewrite -{2}(expr1n _ 2) subr_sqr -{1 3}(mulr1 (1 - cos a)) -mulrBr -mulrDr.
rewrite opprD addrA subrr add0r -(addrC 1) -expr2 -scalerDr.
apply/eqP; rewrite scaler_eq0 sqrf_eq0 subr_eq0 eq_sym (negbTE cphi) /=.
by rewrite aM subrr.
Qed.

Lemma trace_exp_rot_skew_mx a u : norm u = 1 ->
  \tr `e^(a, skew_mx u) = 1 + 2%:R * cos a.
Proof.
move=> w1.
rewrite 2!mxtraceD !mxtraceZ /= mxtrace1.
rewrite (trace_anti (anti_skew _)) mulr0 addr0 mxtrace_sqr_skew_mx w1.
rewrite (_ : - _ = - 2%:R); last by rewrite expr1n mulr1.
by rewrite mulrDl addrA mul1r -natrB // mulrC mulrN -mulNr opprK.
Qed.

(* see table 1.1 of handbook of robotics *)
Lemma exp_rot_skew_mxE a u : norm u = 1 ->
  let va := 1 - cos a in let ca := cos a in let sa := sin a in
  `e^(a, skew_mx u) = triple_prod_mat
  (row3 (u 0 0 ^+2 * va + ca)
        (u 0 0 * u 0 1 * va - u 0 2%:R * sa)
        (u 0 0 * u 0 2%:R * va + u 0 1 * sa))
  (row3 (u 0 0 * u 0 1 * va + u 0 2%:R * sa)
        (u 0 1 ^+2 * va + ca)
        (u 0 1 * u 0 2%:R * va - u 0 0 * sa))
  (row3 (u 0 0 * u 0 2%:R * va - u 0 1 * sa)
        (u 0 1 * u 0 2%:R * va + u 0 0 * sa)
        (u 0 2%:R ^+2 * va + ca)).
Proof.
move=> w1 va ca sa.
apply/matrixP => i j.
case/boolP : (i == 0) => [/eqP ->|].
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    rewrite sqr_skewE !mxE /=.
    rewrite (_ : - _ - _ = u 0 0 ^+ 2 - 1); last first.
      rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
      by rewrite !opprD !addrA subrr add0r addrC.
    rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
    by rewrite /va opprB addrC subrK.
  rewrite ifnot0 => /orP [] /eqP ->.
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
rewrite ifnot0 => /orP [] /eqP ->.
  case/boolP : (j == 0) => [/eqP ->|].
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
  rewrite ifnot0 => /orP [] /eqP ->.
    rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
    rewrite sqr_skewE !mxE /=.
    rewrite (_ : - _ - _ = u 0 1 ^+ 2 - 1); last first.
      rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
      by rewrite 2!opprD addrCA addrA subrK addrC.
    rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
    by rewrite /va opprB addrC subrK.
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
case/boolP : (j == 0) => [/eqP ->|].
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
rewrite ifnot0 => /orP [] /eqP ->.
  rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
  by rewrite sqr_skewE !mxE /= addrC mulrC (mulrC sa).
rewrite 2![in RHS]mxE /= [in LHS]mxE -/sa -/va 3!mxE /= !skewij; simp => /=.
rewrite sqr_skewE !mxE /=.
rewrite (_ : - _ - _ = u 0 2%:R ^+ 2 - 1); last first.
  rewrite -[in X in _ = _ - X](expr1n _ 2%N) -w1 -dotmulvv dotmulE sum3E -3!expr2.
  by rewrite 2!opprD [in RHS]addrC subrK addrC.
rewrite mulrBr mulr1 addrCA mulrC; congr (_ + _).
by rewrite /va opprB addrC subrK.
Qed.

Lemma exp_rot_is_ortho a u : norm u = 1 -> `e^(a, skew_mx u) \is 'O_3[R].
Proof.
move=> w1.
rewrite orthogonalE tr_exp_rot.
move: (anti_skew u); rewrite antiE -eqr_oppLR => /eqP <-.
by rewrite inv_exp_rot // skew_mx4. 
Qed.

Lemma rank_exp_rot a v : norm v = 1 -> \rank `e^(a, skew_mx v) = 3.
Proof.
move=> w1; by rewrite mxrank_unit // orthogonal_unit // exp_rot_is_ortho.
Qed.

Lemma det_exp_rot0 w : norm w = 1 -> \det `e^(0, skew_mx w) = 1.
Proof. move=> w1; by rewrite /exp_rot sin0 cos0 subrr 2!scale0r 2!addr0 det1. Qed.

Lemma det_exp_rot a w : norm w = 1 -> \det `e^(a, skew_mx w) = 1.
Proof.
move=> w1.
move: (exp_rot_is_ortho (half_angle a) w1).
move/orthogonal_det/eqP.
rewrite -(@eqr_expn2 _ 2%N) // expr1n norm2 expr2 -det_mulmx.
rewrite mulmxE mul_exp_rot; last by rewrite skew_mx3 w1 expr1n scaleN1r.
move/eqP; by rewrite halfP.
Qed.

Definition exp_rot_skew_mx_eigenvalues a : seq R[i] := [:: 1; expi a; expi (- a)].

Lemma eigenvalue_exp_rot a w : norm w = 1 ->
  eigenvalue (map_mx (fun x => x%:C) `e^(a, skew_mx w)) =1
    [pred k | k \in exp_rot_skew_mx_eigenvalues a].
Proof.
move=> u1 /= k.
rewrite inE eigenvalue_root_char -map_char_poly.
Abort.

(*Lemma trace_sqr_exp_rot_skew_mx (phi : angle R) w : norm w = 1 ->
  \tr `e^(phi, (skew_mx w) ^+ 2) = - (1 + 2%:R * cos phi) ^+ 2(*?*).
Proof.
move=> w1.
Abort.*)

Lemma Rz_exp_rot a : Rz a = `e^(a, skew_mx V.k).
Proof.
rewrite /Rz exp_rot_skew_mxE ?V.normk //.
rewrite !mxE /= expr0n /=. simp. by rewrite expr1n mul1r subrK.
Qed.

(* the w vector of e(phi,w) is an axis *)
Lemma axial_vec_exp_rot a w : norm w = 1 -> axial_vec (`e^(a, skew_mx w)) = sin a *+ 2 *: w.
Proof.
move=> w1.
rewrite /axial_vec.
apply/rowP => i.
rewrite 2!mxE /=.
case: ifPn => [/eqP ->|].
  rewrite /exp_rot.
  rewrite 2!mxE 1![in RHS]mxE /= add0r mxE skewij.
  rewrite mxE {1}skew_mx2 mxE w1 expr1n mul_tr_vecij 3!mxE /= mulr0 subr0.
  rewrite 3!mxE /= add0r mxE skewij.
  rewrite mulrN opprD opprK.
  rewrite mxE skew_mx2 w1 expr1n mxE mul_tr_vecij 3!mxE /= mulr0 subr0.
  rewrite addrACA (mulrC (w 0 1)) subrr addr0 -mulr2n.
  by rewrite mulrnAl.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite /exp_rot.
  rewrite 3!mxE /= add0r mxE skewij.
  rewrite mxE {1}skew_mx2 mxE w1 expr1n mul_tr_vecij 3!mxE /= mulr0 subr0.
  rewrite 3!mxE /= add0r mxE skewij.
  rewrite mulrN opprD opprK.
  rewrite mxE skew_mx2 w1 expr1n mxE mul_tr_vecij 3!mxE /= mulr0 subr0.
  by rewrite addrACA (mulrC (w 0 0)) subrr addr0 mxE -[in LHS]mulr2n mulrnAl.
rewrite /exp_rot.
rewrite 3!mxE /= add0r mxE skewij.
rewrite mxE {1}skew_mx2 mxE w1 expr1n mul_tr_vecij 3!mxE /= mulr0 subr0.
rewrite 3!mxE /= add0r mxE skewij.
rewrite mulrN opprD opprK.
rewrite mxE skew_mx2 w1 expr1n mxE mul_tr_vecij 3!mxE /= mulr0 subr0.
by rewrite addrACA (mulrC (w 0 0)) subrr addr0 mxE -[in LHS]mulr2n mulrnAl.
Qed.  

Definition rodrigues (v : 'rV[R]_3) a w :=
  cos a *: v + (1 - cos a) * (v *d w) *: w + sin a *: (v *v w).

Lemma rodriguesP u a w : norm w = 1 ->
  rodrigues u a w = u *m `e^(a, skew_mx w).
Proof.
move=> w1.
rewrite /rodrigues.
rewrite addrAC !mulmxDr mulmx1 -!scalemxAr mulmxA !skew_mxE.
rewrite [in X in _ = _ + _ + X]crossmulC scalerN.
rewrite double_crossmul dotmulvv w1 [_ ^+ _]expr1n scale1r.
rewrite [in X in _ = _ + _ + X]dotmulC scalerBr opprB.
rewrite scalerA [in RHS](addrC (_ *: w)) [in RHS]addrA; congr (_ + _).
rewrite scalerDl opprD scaleNr opprK addrC addrA scale1r; congr (_ + _).
by rewrite addrAC subrr add0r.
Qed.

(* TODO: move? *)
Lemma norm1_neq0 (u : vector) : norm u = 1 -> u != 0.
Proof. rewrite -norm_eq0 => ->; exact: oner_neq0. Qed.

Lemma is_around_axis_exp_rot a u (u1 : norm u = 1) :
  is_around_axis u a (lin_of_mat (`e^(a, skew_mx u))).
Proof.
pose f := pframe_of_i (norm1_neq0 u1).
split => /=.
- rewrite -rodriguesP // /rodrigues dotmulvv u1 expr1n mulr1 scalerBl.
  by rewrite scale1r addrCA subrr addr0 crossmulvv scaler0 addr0.
- rewrite -rodriguesP // /rodrigues dotmulC.
  move: (idotj f).
  rewrite {1}(normalizeI u1) => ->.
  rewrite mulr0 scale0r addr0 crossmulC.
  move: (icrossj f).
  rewrite {1}(normalizeI u1) => ->.
  by rewrite scalerN scaleNr.
- rewrite -rodriguesP // /rodrigues dotmulC.
  move: (idotk f).
  rewrite {1}(normalizeI u1) => ->.
  rewrite mulr0 scale0r addr0.
  move: (proj1 (oframe_posP f (frame_pos_crossmul (pframeP f)))) => /esym.
  rewrite (normalizeI u1) => ->; by rewrite addrC.
Qed.

(* expression alternative de exp_rot *)
Definition Rot (e : vector) (a : angle R) :=
 e^T *m e + (cos a) *: (1 - e^T *m e) + (sin a) *: skew_mx e.

Lemma Rot_is_exp_rot (e : vector) (a : angle R) : norm e = 1 ->
  Rot e a = `e^(a, skew_mx e).
Proof.
move=> e1.
rewrite /Rot /exp_rot addrAC skew_mx2 e1 expr1n.
rewrite -addrA addrCA -[in RHS]addrA [in RHS]addrCA; congr (_ + _).
rewrite scalerBr scalemx1 scalemx1 scalerBl scale1r.
rewrite -[in RHS](addrA (e^T *m e)) [in RHS](addrCA 1); congr (_ + _).
by rewrite scalerDr addrC addrA subrr add0r opprD scalerN opprK scalemx1.
Qed.

Lemma Rot_is_around_axis e (e1 : e != 0) (a : angle R) :
  is_around_axis e a (lin_of_mat (Rot (normalize e) a)).
Proof.
move: (is_around_axis_exp_rot a (norm_normalize e1)).
rewrite Rot_is_exp_rot ?norm_normalize //.
by apply is_around_axisZ => //; rewrite divr_gt0 // ?ltr01 // ltr_neqAle norm_ge0 eq_sym norm_eq0 e1.
Qed.

End exponential_map_rot.

Notation "'`e^(' a ',' w ')'" := (exp_rot a w).

Section exponential_coordinates_rotation.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Record angle_axis := AngleAxis {
  angle_axis_val : angle R * vector ;
  _ : norm (angle_axis_val.2) == 1
 }.

Canonical angle_axis_subType := [subType for angle_axis_val].

Definition aangle (a : angle_axis) := (val a).1.
Definition aaxis (a : angle_axis) := (val a).2.

Lemma norm_axis a : norm (aaxis a) = 1.
Proof. by case: a => *; apply/eqP. Qed.

Fact norm_e1_subproof : norm (@delta_mx R _ 3 0 0) == 1.
Proof. by rewrite norm_delta_mx. Qed.

Definition angle_axis_of (a : angle R) (v : vector) :=
  insubd (@AngleAxis (a,_) norm_e1_subproof) (a, (norm v)^-1 *: v).

Lemma aaxis_of (a : angle R) (v : vector) : v != 0 ->
  aaxis (angle_axis_of a v) = (norm v)^-1 *: v.
Proof.
move=> v_neq0 /=; rewrite /angle_axis_of /aaxis val_insubd /=.
by rewrite normZ normfV normr_norm mulVf ?norm_eq0 // eqxx.
Qed.

Lemma aaxis_of1 (a : angle R) (v : vector) : norm v = 1 ->
  aaxis (angle_axis_of a v) = v.
Proof.
move=> v1; rewrite aaxis_of; last by rewrite -norm_eq0 v1 oner_neq0.
by rewrite v1 invr1 scale1r.
Qed.

Lemma aangle_of (a : angle R) (v : vector) : aangle (angle_axis_of a v) = a.
Proof. by rewrite /angle_axis_of /aangle val_insubd /= fun_if if_same. Qed.

(* see table 1.2 of handbook of robotics *)
Definition angle_of_rotation (M : 'M[R]_3) := acos ((\tr M - 1) / 2%:R).
Definition axis_of_rotation (M : 'M[R]_3) : 'rV[R]_3 := 
  let phi := angle_of_rotation M in 1 / (2%:R * sin phi) *: axial_vec M.

Lemma angle_of_rotation_Rx (a : angle R) :
  (a \in Opi_closed R -> angle_of_rotation (Rx a) = a) /\
  (a \in piO_closed R -> angle_of_rotation (Rx a) = - a).
Proof.
split.
  move=> Ha. rewrite /angle_of_rotation tr_Rx addrAC subrr add0r.
  by rewrite -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1 cosK.
move=> Ha. rewrite /angle_of_rotation tr_Rx addrAC subrr add0r.
rewrite -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1.
by rewrite cosKN.
Qed.

Lemma SO_is_around_axis_angle (M : 'M[R]_3) : M \is 'SO_3[R] ->
  forall u a, u != 0 -> a \in Opi_closed R ->
  is_around_axis u a (lin_of_mat M) -> a = angle_of_rotation M.
Proof.
move=> Hf u a u0 Ha.
move/(tr_around_axis u0); rewrite /angle_of_rotation => ->.
rewrite addrAC subrr add0r -(mulr_natr (cos a)) -mulrA divrr.
  by rewrite mulr1 cosK.
by rewrite unitfE pnatr_eq0.
Qed.

Lemma SO_is_around_axis_axis (M : 'M[R]_3) : M \is 'SO_3[R] ->
  forall u (a : angle R), a \in Opi_closed R ->
  is_around_axis u a (lin_of_mat M) -> colinear u (axial_vec M).
Proof.
move=> Hf u a Ha [/= H1 H2 H3]; apply is_eigenvector1_colinear => //.
apply/eigenspaceP; by rewrite H1 scale1r.
Qed.

Lemma j_of_i_Vi : j_of_i (@V.i R) = V.j.
Proof. by rewrite /j_of_i colinear_refl. Qed.

Lemma k_of_i_Vi : k_of_i (@V.i R) = V.k.
Proof. by rewrite /k_of_i (normalizeI (V.normi _)) j_of_i_Vi V.icrossj. Qed.

Lemma angle_of_rotation_SO_RO (M : 'M[R]_3) a :
  M = block_mx (1 : 'M_1) 0 0 (RO a) ->
  (a \in Opi_closed R -> angle_of_rotation M = a) /\
  (a \in piO_closed R -> angle_of_rotation M = - a).
Proof.
move=> Ma.
rewrite /angle_of_rotation Ma (mxtrace_block (1 : 'M_1)) tr_RO mxtrace1 addrAC.
rewrite subrr add0r -(mulr_natr (cos a)) -mulrA divrr ?unitfE ?pnatr_eq0 // mulr1.
split => Ha.
  by rewrite cosK.
by rewrite cosKN.
Qed.

Lemma rotation_is_Rx (M : 'M[R]_3) k (k0 : 0 < k ) : M \is 'SO_3[R] ->
  axial_vec M = k *: V.i ->
  angle_of_rotation M \in Opi_closed R /\ (
(M = block_mx (1 : 'M_1) 0 0 (RO (- angle_of_rotation M)) /\ M = Rx (- angle_of_rotation M)) \/
(M = block_mx (1 : 'M_1) 0 0 (RO (angle_of_rotation M)) /\ M = Rx (angle_of_rotation M))).
Proof.
move=> MSO axialVi.
have [M02 M01] : M 0 2%:R = M 2%:R 0 /\ M 0 1 = M 1 0.
  move/matrixP/(_ 0 1) : (axialVi).
  rewrite !mxE /= mulr0 => /eqP; rewrite subr_eq add0r => /eqP ->.
  move/matrixP/(_ 0 2%:R) : (axialVi).
  by rewrite !mxE /= mulr0 => /eqP; rewrite subr_eq add0r => /eqP ->.
have axial_eigen : axial_vec M *m M = axial_vec M.
  move: (axial_vec_vec_eigenspace MSO) => /eigenspaceP; by rewrite scale1r.
have [M010 [M020 M001]] : M 0 1 = 0 /\ M 0 2%:R = 0 /\ M 0 0 = 1.
  move: axial_eigen.
  rewrite axialVi -scalemxAl => /scalerI.
  rewrite gtr_eqF // => /(_ isT) ViM.
  have : V.i *m M = row 0 M.
    rewrite rowE; congr (_ *m _); apply/rowP => i.
    rewrite !mxE /=; case: ifPn => //. by rewrite ifnot0 => /orP [] /eqP ->.
  rewrite {}ViM => ViM.
  move/matrixP : (ViM) => /(_ 0 1); rewrite !mxE /= => <-.
  move/matrixP : (ViM) => /(_ 0 2%:R); rewrite !mxE /= => <-.
  by move/matrixP : (ViM) => /(_ 0 0); rewrite !mxE /= => <-.
have [P MP] : exists P : 'M[R]_2, M = block_mx (1 : 'M_1) 0 0 P.
  exists (@drsubmx _ 1 2 1 2 M).
  rewrite -{1}(@submxK _ 1 2 1 2 M).
  rewrite (_ : ulsubmx _ = 1); last first.
    apply/matrixP => i j.
    rewrite (ord1 i) (ord1 j) !mxE /= -M001 mulr1n; congr (M _ _); by apply val_inj.
  rewrite (_ : ursubmx _ = 0); last first.
    apply/rowP => i.
    case/boolP : (i == 0) => [/eqP ->|].
      rewrite !mxE -[RHS]M010; congr (M _ _); by apply val_inj.
    rewrite ifnot01 => /eqP ->; rewrite !mxE -[RHS]M020; congr (M _ _); by apply val_inj.
  rewrite (_ : dlsubmx _ = 0) //.
  apply/colP => i.
  case/boolP : (i == 0) => [/eqP ->|].
    rewrite !mxE -[RHS]M010 M01; congr (M _ _); by apply val_inj.
  rewrite ifnot01 => /eqP ->; rewrite !mxE -[RHS]M020 M02; congr (M _ _); by apply val_inj.
have PSO : P \is 'SO_2[R] by rewrite -(SO_RO MP).
move=> [: Hangle].
split.
  abstract: Hangle.
  rewrite inE /angle_of_rotation MP (mxtrace_block (1 : 'M_1)) mxtrace1 addrAC.
  rewrite subrr add0r sin_acos.
    by rewrite sqrtr_ge0.
  rewrite normrM normrV ?unitfE ?pnatr_eq0 // normr_nat ler_pdivr_mulr // mul1r.
  exact: tr_SO2.
case/rot2d : PSO => a [PRO [Ha|Ha]]; rewrite {}PRO in MP.
  (* a \in piO_closed R *)
  move: (proj2 (angle_of_rotation_SO_RO MP) Ha) => MHa.
  left.
  by rewrite MHa opprK MP Rx_RO.
move: (proj1 (angle_of_rotation_SO_RO MP) Ha) => MHa.
right.
by rewrite MHa MP Rx_RO.
Qed.

Lemma SO_is_around_axis (M : 'M[R]_3) : M \is 'SO_3[R] ->
  exists u a, is_around_axis u a (lin_of_mat M).
Proof.
move=> MSO.
exists (axial_vec M).
exists (angle_of_rotation M).
split => /=.
- move/axial_vec_vec_eigenspace : MSO => /eigenspaceP ->; by rewrite scale1r.
- rewrite /j_of_i.
  case: ifPn => axialVi.
    (* axial vector colinear with j *)
    case/colinearP : axialVi => [|[_ [k [Hk axialVi]]]].
      by rewrite -norm_eq0 V.normi (negbTE (oner_neq0 _)).
    case: (ltrP 0 k) => k0.
      case: (rotation_is_Rx k0 MSO axialVi) => Hangle [[HM1 HM2]|[HM1 HM2]].
        admit.
      rewrite {1}HM2.
      transitivity (row 1 (Rx (angle_of_rotation M))).
        admit.
      rewrite rowK /=.
      admit.
    admit.
  (* axial vector not colinear with j *)
  admit.
- admit.
Abort.

Coercion rodrigues_mx r := 
  let (a, w) := (aangle r, aaxis r) in `e^(a, skew_mx w).

(*Definition rodrigues (x : vector) r :=
  let (a, w) := (aangle r, aaxis r) in
  cos a *: x + (1 - cos a) * (x *d w) *: w + sin a *: (x *v w).

(* Rodrigues formula *)
Lemma rodriguesP u r : rodrigues u r = u *m r.
Proof.
...
Qed.*)

Lemma trace_rodrigues r : \tr (rodrigues_mx r) = 1 + 2%:R * cos (aangle r).
Proof. by rewrite trace_exp_rot_skew_mx // norm_axis. Qed.

Lemma rodrigues_mx_is_O r : norm (aaxis r) = 1 -> rodrigues_mx r \in 'O_3[R].
Proof.
move=> axis1.
rewrite /rodrigues_mx orthogonalE tr_exp_rot {2}(eqP (anti_skew _)) linearN /= trmxK.
by rewrite inv_exp_rot // skew_mx4.
Qed.

Lemma det_rodrigues_mx r : norm (aaxis r) = 1 -> \det (rodrigues_mx r) = 1.
Proof. move=> ?; by rewrite /rodrigues_mx det_exp_rot. Qed.

Definition angle_axis_of_rotation (M : 'M[R]_3) :=
  angle_axis_of (angle_of_rotation M) (axis_of_rotation M).

Definition log_rot (M : 'M[R]_3) : angle R * 'rV[R]_3 :=
  (angle_of_rotation M, axis_of_rotation M).

Lemma log_exp_rot (a : angle R) (w : 'rV[R]_3) :
  sin a != 0 -> a \in Opi_closed R -> norm w = 1 ->
  log_rot `e^(a, skew_mx w) = (a, w).
Proof.
move=> sphi phiOpi w1 [:Hphi].
congr pair.
  abstract: Hphi.
  rewrite /angle_of_rotation trace_exp_rot_skew_mx // addrAC subrr add0r.
  by rewrite mulrC mulrA mulVr ?mul1r ?cosK // unitfE pnatr_eq0.
apply/rowP => i.
rewrite 2!mxE /= Hphi => [:twosphi].
case: ifPn => [/eqP ->|].
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r.
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r opprD addrAC addrA subrK.
  rewrite mulrN opprK -mulr2n -(mulr_natl (_ * _) 2).
  rewrite (mulrA 2%:R) div1r mulrCA mulrA divrr ?mul1r ?mxE //.
  abstract: twosphi.
  by rewrite unitfE mulf_neq0 // ?pnatr_eq0.
rewrite ifnot0 => /orP [] /eqP -> /=.
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r.
  rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r opprD addrAC addrA subrK.
  rewrite mulrN opprK -mulr2n -(mulr_natl (_ * _) 2).
  by rewrite (mulrA 2%:R) div1r mulrCA mulrA divrr ?mul1r ?mxE.
rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r.
rewrite 4!mxE /= skewij mxE sqr_skewE 2!mxE /= add0r opprD addrAC addrA subrK.
rewrite mulrN opprK -mulr2n -(mulr_natl (_ * _) 2).
by rewrite (mulrA 2%:R) div1r mulrCA mulrA divrr ?mul1r ?mxE.
Qed.

Lemma rodriguesE M u (HM : M^T \in 'SO_3[R]) :
  norm (axis_of_rotation M) = 1 ->
  sin (angle_of_rotation M) != 0 (* to avoid singularity *) ->
  rodrigues u (aangle (angle_axis_of_rotation M)) (aaxis (angle_axis_of_rotation M)) =
  homogeneous_ap u (Transform 0 HM).
Proof.
move=> norm1 sin0.
transitivity (u *m M); last first.
  (* TODO: lemma? *)
  rewrite homogeneous_apE /htrans_of_coordinate trmx_mul trmxK.
  rewrite (_ : (Transform 0 HM)^T = (hrot_of_transform (Transform 0 HM))^T); last first.
    by rewrite /hrot_of_transform /= /hmx /= trmx0.
  rewrite hcoor_hrot_of_transform /=.
  rewrite (_ : esym (addn1 3) = erefl (3 + 1)%N); last by apply eq_irrelevance.
  rewrite trmxK (@cast_row_mx _ _ _ _ _ _ (u *m M)) //.
  by rewrite row_mxKl /= castmx_id.
rewrite rodriguesP; last by rewrite aaxis_of1.
congr (_ *m _).
(*rewrite aaxis_of1 //.
rewrite aangle_of //.
rewrite /axis_of_rotation.*)
rewrite /rodrigues_mx. set phi := aangle _. set w := aaxis _.
have antiM : antip M = sin phi *: skew_mx w.
  rewrite /w aaxis_of1 // /axis_of_rotation skew_mxZ axial_vecE unskewK; last first.
    by rewrite antiE linearD linearN /= trmxK opprB.
  rewrite scalerA /phi aangle_of mulrCA mul1r mulrC invrM ?unitfE ?pnatr_eq0 //.
  by rewrite mulrAC mulVr ?unitfE.
suff symM : symp M = 1 + (1 - cos phi) *: skew_mx w ^+ 2.
  rewrite exp_rot_skew_mxE; last by rewrite /w aaxis_of1.
  rewrite (symp_antip M) antiM symM -exp_rot_skew_mxE; last by rewrite /w aaxis_of1.
  by rewrite /exp_rot addrAC.
rewrite /w aaxis_of1 // /axis_of_rotation skew_mxZ skew_axial_vec.
rewrite exprZn scalerA.
rewrite (_ : (1 - cos phi) * _ = (1 / (1 + cos phi)) * (1 / 4%:R)); last first.
  admit.
rewrite -scalerA.
rewrite (_ : (1 / 4%:R) *: _ = (antip M) ^+ 2); last first.
  admit.
Abort.

End exponential_coordinates_rotation.

(* more generic definition of the exponential map, in progress *)
Section exponential_map.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition expmx n (M : 'M[R]_n.+1) k := \sum_(i < k) (i`!%:R)^-1 *: (M ^+ i).

Lemma expmx0 n (M : 'M[R]_n.+1) : expmx M 0 = 0.
Proof. by rewrite /expmx big_ord0. Qed.

Lemma expmxS n (M : 'M[R]_n.+1) k : expmx M k.+1 = expmx M k + k`!%:R^-1 *: M ^+ k.
Proof. by rewrite /expmx big_ord_recr. Qed.

Lemma expmx1 n (M : 'M[R]_n.+1) : expmx M 1 = 1.
Proof. by rewrite expmxS expmx0 expr0 add0r fact0 invr1 scale1r. Qed.

Lemma expmx2 n (M : 'M[R]_n.+1) : expmx M 2 = 1 + M. 
Proof. by rewrite expmxS expmx1 invr1 expr1 scale1r. Qed.

Lemma expr_mulmulV n (M : 'M[R]_n.+1) i (g : 'M[R]_n.+1) : g \in unitmx ->
  (g * M * g^-1)^+i = g * M ^+i  *g^-1.
Proof.
move=> Hg; elim: i => [|i ih]; first by rewrite 2!expr0 mulr1 divrr.
rewrite exprS ih -!mulrA exprS -mulrA; congr (_ * (_ * _)).
by rewrite mulrA mulVr // mul1r.
Qed.

Lemma expmx_mulmulV n (M : 'M[R]_n.+1) k (g : 'M[R]_n.+1) : g \in unitmx ->
  expmx (g * M * g^-1) k = g * expmx M k * g^-1.
Proof.
move=> Hg.
rewrite /expmx big_distrr /= big_distrl /=; apply/eq_bigr => i _.
by rewrite expr_mulmulV // 2!scalerAl scalerCA.
Qed.

End exponential_map.

Section screw.

Variable R : rcfType.
Let vector := 'rV[R]_3.
Let coordinate := 'rV[R]_3.

Variable f : 'SE_3[R].
Let Q : 'M[R]_3 := ortho_of_iso f.
Let T : vector := trans_of_iso f.
Variable e : vector.
Hypothesis ne : norm e = 1.
Variable phi : angle R.
Hypothesis Maxis : is_around_axis e phi (lin_of_mat Q).

Lemma is_around_axis_axis : e *m Q = e.
Proof. by case: Maxis. Qed.

(* p.91 *)
(* the displacements of all the points of B have the same component along e *)
Lemma thm321 (a p : coordinate) :
  let da := f a - a in let dp := f p - p in
  da *d e = dp *d e.
Proof.
move=> da dp.
have eq34 : dp = da + (p - a) *m (Q - 1).
  rewrite /da mulmxBr mulmx1 opprB addrA -(addrC a) 2!addrA subrK.
  rewrite /dp; congr (_ - _).
  apply/eqP; rewrite addrC -subr_eq.
  by rewrite img_vec_iso.
have : dp *m e^T = da *m e^T + (p - a) *m (Q - 1) *m e^T.
  by rewrite -mulmxDl -eq34.
rewrite -mulmxA (mulmxBl Q 1 e^T) mul1mx.
have -> : Q *m e^T = e^T.
  rewrite -{1}(is_around_axis_axis) trmx_mul mulmxA mulmxE.
  have : Q \is 'O_3[R] by rewrite /Q ortho_of_iso_is_O.
  rewrite orthogonalE => /eqP ->; by rewrite mul1mx.
rewrite subrr mulmx0 addr0 /dotmul; by move=> ->.
Qed.

Definition d0 := (f 0 - 0) *d e.

Lemma d0_is_a_lb_of_a_displacement p : (d0 ^+ 2 <= norm (f p - p) ^+ 2).
Proof.
set dp := f p - p.
rewrite /d0 (thm321 0 p) -/dp.
move: (pframe_of_i (norm1_neq0 ne)) => F.
have -> : norm dp = norm (dp *m (triple_prod_mat (normalize e) (j_of_i e) (k_of_i e))^T).
  rewrite orth_preserves_norm // orthogonalV.
  move: (pframe_is_rot F).
  by rewrite rotationE => /andP [].
rewrite triple_prod_mat_mulmx sqr_norm !mxE /= -[X in X <= _]addr0 -addrA ler_add //.
  by rewrite normalizeI.
by rewrite addr_ge0 // sqr_ge0.
Qed.

Definition parpart (p : coordinate) :=  axialcomp (f p - p) e.

Lemma parpartP (p : vector) : parpart p = d0 *: e.
Proof.
rewrite /parpart; set dp := f p - p.
rewrite /d0 -mul_scalar_mx /axialcomp mulmxA; congr (_ *m _).
by rewrite -(thm321 p 0) /dotmul -mx11_scalar.
Qed.

Definition perppart (p : coordinate) := normalcomp (f p - p) e.

Lemma perpart_colinear (p : coordinate) :
  let dp := f p - p in
  (perppart p == 0) = (colinear dp e).
Proof.
move=> dp.
apply/idP/idP => [/eqP|/colinearP].
  rewrite /perppart.
  by apply normalcomp_colinear.
rewrite -norm_eq0 ne -(negbK (1 == 0)) oner_neq0 => -[] // [] _ [k [Hk1 Hk2]].
by rewrite /perppart /normalcomp -/dp Hk2 -scalemxAl mulmxBr mulmx1 mulmxA dotmul1 // mul1mx subrr scaler0.
Qed.

(* d0 is the minimal norm of a displacement, all such points are along a line parallel
   to e *)
Lemma MozziChasles1 p : let dp := f p - p in
  norm dp = d0 -> colinear dp e.
Proof.
move=> dp H.
have Hp : forall p : coordinate, let dp := f p - p in
    norm dp ^+ 2 = norm (d0 *: e) ^+2 + norm (perppart p) ^+ 2.
  move=> p' dp'.
  rewrite /dp' (decomp (f p' - p') e).
  rewrite normD -dotmul_cos.
  rewrite axialnormal // mul0rn addr0 sqr_sqrtr; last first.
    by rewrite addr_ge0 // ?sqr_ge0.
  by rewrite /perppart -/(parpart p') parpartP.
move: {Hp}(Hp p) => Hp.
rewrite -perpart_colinear.
rewrite -norm_eq0.
suff : norm dp ^+2 <= norm (d0 *: e) ^+ 2.
  by rewrite Hp addrC -ler_subr_addr subrr exprn_even_le0 //= norm_eq0.
rewrite 2!expr2.
by rewrite ler_pmul // ?norm_ge0 // H normZ ne mulr1 ler_norm.
Qed.

Definition p0 (a : coordinate) := 
  let a':= f a in 
  1 / (2%:R * (1 - cos phi)) *: (a *m Q - a') *m (Q - 1)^T.

(* TODO *)

End screw.

Section exponential_coordinates_rigid.

Variable R : rcfType.
Let vector := 'rV[R]_3.

Definition twist (w v : vector) : 'M[R]_4 :=
  row_mx (col_mx (skew_mx w) 0) (col_mx v^T 0).

(* TODO: notation 'se_3[R] for the set of twists *)

Lemma expr_twist0v (v : vector) n : (twist 0 v) ^+ n.+2 = 0.
Proof.
elim: n => [|n ih]; last by rewrite exprS ih mulr0.
apply/eqP; rewrite expr2 /twist.
set a := col_mx (skew_mx _) _. rewrite -mulmxE (mul_mx_row (row_mx a _) a) {}/a.
set b := _ *m _. rewrite (row_mx_eq0 b) {}/b. apply/andP; split;
  by rewrite mul_row_col mulmx0 addr0 mul_col_mx skew_mx0 !(mul0mx,mulmx0) col_mx0.
Qed.

Definition exp_twist0 (* w = 0 *) (v : vector) (a : angle R) : 'M_4 :=
  row_mx (col_mx 1 0) (col_mx v^T 1).

(* closed expression for the exponential of a twist with w = 0 *)
Lemma expmx_exp_twist0 (v : vector) (a : angle R) k :
  expmx (twist 0 v) k.+2 = exp_twist0 v a.
Proof.
rewrite /expmx 2!big_ord_recl big1 ?addr0; last first.
  move=> /= i _; by rewrite expr_twist0v scaler0.
rewrite liftE0 eqxx factS fact0 expr0 expr1 invr1 2!scale1r /twist skew_mx0.
rewrite /exp_twist0 (_ : 1 = row_mx (@col_mx _ 3 1 _ 1 0) (col_mx 0 1)); last first.
  by rewrite -block_mxEh -idmxE (@scalar_mx_block _ 3 1 1).
set x1 := col_mx _ _.
by rewrite (add_row_mx x1) col_mx0 addr0 add_col_mx add0r addr0.
Qed.

Definition rigid_trans (w v : vector) : 'M_4 := 
  row_mx (col_mx 1 0) (col_mx (w *v v)^T 1).

Definition inv_rigid_trans (w v : vector) := row_mx (col_mx 1 0) (col_mx (- w *v v)^T 1).

Lemma Vrigid_trans w v : inv_rigid_trans w v * rigid_trans w v = 1.
Proof.
rewrite /inv_rigid_trans /rigid_trans.
rewrite -[in X in _ * X = _]block_mxEh.
rewrite -mulmxE (mul_row_block (col_mx 1 0) (col_mx (- w *v v)^T 1) 1).
rewrite 2!mulmx1 mulmx0 addr0 mul_col_mx mul0mx mul1mx.
by rewrite add_col_mx crossmulNv linearN subrr add0r -block_mxEh -scalar_mx_block.
Qed.

Lemma rigid_trans_unitmx w v : rigid_trans w v \in unitmx.
Proof.
by rewrite unitmxE /rigid_trans -block_mxEh (det_ublock 1 (w *v v)^T) 2!det1 mulr1 unitr1.
Qed.

Lemma inv_rigid_transE w v : (rigid_trans w v)^-1 = inv_rigid_trans w v.
Proof.
rewrite -[LHS]mul1mx -[X in X *m _ = _](Vrigid_trans w v) -mulmxA.
by rewrite mulmxV ?rigid_trans_unitmx // mulmx1.
Qed.

(* 2.34, p.41 *)
Lemma Vmulmul w v : norm w = 1 ->
  let e' := (rigid_trans w v)^-1 *m twist w v *m rigid_trans w v in
  let h := w *d v in
  e' = col_mx (row_mx (skew_mx w) (h *: w^T)) 0.
Proof.
move=> w1 e'; rewrite /e'.
rewrite inv_rigid_transE /inv_rigid_trans /rigid_trans /twist.
rewrite -[in X in _ *m X *m _ = _]block_mxEh.
rewrite (mul_row_block (col_mx 1 0) (col_mx (- w *v v)^T 1) (skew_mx w)) 2!mulmx0 2!addr0.
rewrite mul_col_mx mul1mx mul0mx mul_col_mx mul0mx mul1mx.
rewrite -[in X in _ *m X = _]block_mxEh.
rewrite (mul_row_col (col_mx (skew_mx w) 0) (col_mx v^T 0)).
rewrite mul_col_mx mul0mx mul_col_mx mul0mx add_col_mx addr0.
rewrite (mul_mx_row (skew_mx w) 1) mulmx1.
rewrite (@mul_mx_row _ _ _ 3 1 v^T 0 1) mulmx0 mulmx1.
rewrite (add_row_mx (skew_mx w)) addr0.
rewrite -{2}(trmxK (skew_mx w)) -trmx_mul.
move: (anti_skew w); rewrite antiE -eqr_oppLR => /eqP <-.
rewrite mulmxN skew_mxE crossmulC opprK double_crossmul.
by rewrite dotmulvv w1 expr1n scale1r linearD /= linearN /= subrK linearZ /=.
Qed.

(* p.42 *)
Lemma exr_Vmulmul w v : norm w = 1 ->
  let e' := (rigid_trans w v)^-1 *m twist w v *m rigid_trans w v in
  forall k, e'^+k.+2 = col_mx (row_mx ((skew_mx w)^+k.+2) 0) (0 : 'rV_4).
Proof.
move=> w1 e' k.
rewrite /e' (Vmulmul _ w1).
set h := w *d v.
elim: k => [|k ih].
  rewrite (@expr2 _ (col_mx (row_mx (skew_mx w) _) 0)).
  rewrite -{1}row_mx0 -block_mxEv -mulmxE (mul_block_col (skew_mx w)).
  rewrite 2!mulmx0 mul0mx 2!addr0 (mul_mx_row (skew_mx w) (skew_mx w)).
  by rewrite mulmxE -expr2 /h -scalemxAr skew_mxT scaler0.
rewrite exprS ih -{1}row_mx0 -block_mxEv -mulmxE (mul_block_col (skew_mx w)).
rewrite 2!mul0mx mulmx0 2!addr0 (mul_mx_row (skew_mx w) ((skew_mx w)^+k.+2)).
by rewrite mulmx0 mulmxE -exprS.
Qed.

Lemma expmx2_twist (w v : vector) : norm w = 1 ->
  let g := rigid_trans w v in
  let h := w *d v in   
  expmx (twist w v) 2 = 
  g *m row_mx (col_mx (expmx (skew_mx w) 2) 0) (col_mx (h *: w^T) 1) *m g^-1.
Proof.
move=> w1 g h.
rewrite {1}/expmx 2!big_ord_recl big_ord0 addr0 liftE0 eqxx factS fact0 invr1 2!scale1r.
rewrite expr0 expr1 /twist.
rewrite (_ : 1 = row_mx (@col_mx _ 3 1 _ 1 0) (col_mx 0 1)); last first.
  by rewrite -block_mxEh -idmxE (@scalar_mx_block _ 3 1 1).
rewrite (add_row_mx (col_mx 1 0) (col_mx 0 1) (col_mx (skew_mx w) 0)).
rewrite 2!add_col_mx 2!addr0 add0r.
rewrite mul_mx_row.
rewrite {1}/g {1}/rigid_trans.
rewrite (mul_row_col (col_mx 1 0) (col_mx _ 1) (expmx (skew_mx w) 2)) mulmx0 addr0.
rewrite mul_col_mx mul1mx mul0mx.
rewrite {1}/g {1}/rigid_trans.
rewrite (mul_row_col (col_mx 1 0) (col_mx _ 1) (h *: w^T)) mulmx1.
rewrite mul_col_mx mul1mx mul0mx add_col_mx add0r.
rewrite inv_rigid_transE /inv_rigid_trans.
rewrite (mul_mx_row _ (col_mx 1 0)).
f_equal.
  by rewrite mul_row_col mulmx1 mulmx0 addr0 expmx2.
rewrite mul_row_col mulmx1.
rewrite (mul_col_mx (expmx (skew_mx w) 2) 0 (- w *v v)^T) mul0mx.
rewrite (add_col_mx (expmx (skew_mx w) 2 *m (- w *v v)^T) 0 _ 1) add0r.
f_equal.
rewrite crossmulNv linearN /= mulmxN -mulNmx addrA addrAC. 
rewrite -{2}(mul1mx (_ *v _)^T) -mulmxDl expmx2 (addrC _ 1%:M) opprD addrA subrr add0r.
rewrite crossmulC [in X in _ = _ *m X + _]linearN /= mulmxN mulNmx opprK.
rewrite -(trmxK (skew_mx w)) -trmx_mul.
move: (anti_skew w); rewrite antiE -eqr_oppLR => /eqP <-.
rewrite mulmxN linearN /= skew_mxE (crossmulC (_ *v _)) linearN /= opprK.
rewrite double_crossmul dotmulvv w1 expr2 mulr1 scale1r linearD /=.
by rewrite linearN /= linearZ /= subrK.
Qed.

(* see p.42 on math. foundations, p.17 of springer's handbook *)
(* closed expression for the exponential of a twist with w != 0 *)
Definition exp_twist (w v : vector) (a : angle R) : 'M_4 :=
  row_mx 
  (col_mx `e^(a, skew_mx w) 0)
  (col_mx ((w *v v) *m (1 - `e^(a, (skew_mx w)^T)) + v *m (w^T *m w))^T 1).

(*
Lemma expmx_exp_twist (w v : vector) (a : angle R) k : norm w = 1 ->
  expmx (twist w v) k.+2 = exp_twist w v a.
Proof.
move=> w1.
pose g := rigid_trans w v.
pose e' := g^-1 *m twist w v *m g.
pose h := w *d v.
transitivity (g *m row_mx (col_mx `e^( a, skew_mx w) 0) (col_mx (h *: w^T) 1) *m g^-1); last first.
  rewrite (mul_mx_row g (col_mx `e^( a, skew_mx w) 0)).
  rewrite inv_rigid_transE /inv_rigid_trans.
  rewrite -[in X in _ *m X = _]block_mxEh.
  rewrite (mul_row_block (g *m col_mx `e^( a, skew_mx w) 0) (g *m col_mx (h *: w^T) 1) 1).
  rewrite 2!mulmx1 mulmx0 addr0.
  rewrite /g /rigid_trans.
  rewrite (mul_row_col (col_mx 1 0) (col_mx (w *v v)^T 1)) mulmx0 addr0.
  rewrite mul_col_mx mul1mx mul0mx.
  rewrite /exp_twist.
  f_equal.
  rewrite (mul_row_col (col_mx 1 0) (col_mx (w *v v)^T 1)) mulmx1.
  rewrite (mul_col_mx _ _ (h *: w^T)) mul1mx mul0mx.
  rewrite add_col_mx add0r.
  rewrite (mul_col_mx (`e^(a, skew_mx w))) mul0mx.
  rewrite (add_col_mx (`e^( a, skew_mx w) *m (- w *v v)^T) 0 _ 1) add0r.
  f_equal.
  rewrite addrCA addrC linearD /=; congr (_ + _).
    rewrite mulmxBr mulmx1 linearD /= addrC; congr (_ + _).
    rewrite linearN /= trmx_mul -mulmxN; congr (_ *m _); last by rewrite crossmulNv linearN.
    by rewrite tr_exp_rot trmxK.
  rewrite 2!trmx_mul trmxK -mulmxA (_ : w *m v^T = (w *d v)%:M); last first.
    by rewrite /dotmul -mx11_scalar.
  by rewrite -/h -mul_scalar_mx scalar_mxC.
transitivity (g *m row_mx (col_mx (expmx (skew_mx w) k.+2) 0) (col_mx (h *: w^T) 1) *m g^-1).
  elim: k => [|k ih].
    by rewrite expmx2_twist.
  rewrite expmxS ih [in RHS]expmxS.
  rewrite -[in RHS](addr0 0) -add_col_mx.
  rewrite -[in RHS](addr0 (col_mx _ 1)) -add_row_mx mulmxDr mulmxDl.
  congr (_ + _).
  rewrite -(scaler0 _ (k.+2)`!%:R^-1) -scale_col_mx.

Lemma beuh w v k : norm w = 1 ->
   twist w v ^+ k.+2 =
   row_mx (col_mx (skew_mx w ^+ k.+2) 0)
     (col_mx (skew_mx w ^+ k.+2 *m - (w *v v)^T) 0).
Proof.
move=> w1.
elim: k => [|k ih].
  rewrite expr2 /twist.
  rewrite -mulmxE.
  rewrite (mul_mx_row _ (col_mx (skew_mx w) 0)) mul_row_col mulmx0 addr0.
  rewrite (mul_col_mx (skew_mx w)) mul0mx mulmxE -expr2.
  f_equal.
  rewrite mul_row_col mulmx0 addr0 skew_mx2 w1 expr1n.
  rewrite (mul_col_mx (skew_mx w)) mul0mx; f_equal.
  rewrite -(trmxK (skew_mx w)) -trmx_mul.
  rewrite mulmxN mulmxBl scale1r mul1mx.
  move: (anti_skew w); rewrite antiE -eqr_oppLR => /eqP <-.
  rewrite mulmxN skew_mxE crossmulC opprK.
  rewrite -{1 3}(mul1mx (_ *v v)^T).
  rewrite opprB -mulmxBl; congr (_ *m _).
  admit.
admit.  
(*rewrite {2}(exprSr (skew_mx w)) mulmxN -mulmxE.
rewrite -{3}(trmxK (skew_mx w)) -mulmxA -trmx_mul.
move: (anti_skew w); rewrite antiE -eqr_oppLR => /eqP <-.
rewrite mulmxN skew_mxE.
rewrite (crossmulC (_ *v _)) opprK double_crossmul dotmulvv w1 expr1n scale1r.*)
Admitted.
  
Lemma coucou w v k cst : norm w = 1 ->
   let g := rigid_trans w v in
   cst *: twist w v ^+ k.+2 =
   g *m row_mx (col_mx (cst *: skew_mx w ^+ k.+2) 0) 0 *m g^-1.
Proof.
move=> w1 g.
rewrite {1}/g /rigid_trans.
rewrite mul_mx_row mulmx0.
rewrite (mul_row_col (col_mx 1 0) (col_mx (w *v v)^T 1)) mulmx0 addr0.
rewrite inv_rigid_transE /inv_rigid_trans.
rewrite (mul_mx_row _ (col_mx 1 0)) mul_row_col mulmx0 addr0 mulmx1.
rewrite mul_row_col mul0mx addr0.
rewrite -scalemxAr -scalemxAl -scale_row_mx; congr (_ *: _).
rewrite mul_col_mx mul0mx mul1mx.
rewrite (mul_col_mx (skew_mx w ^+ k.+2) 0) mul0mx.
rewrite crossmulNv linearN /=.

by rewrite beuh.
Qed.

  admit.
    (* TODO: lemma? *)




  admit.
(*have : expmx e' k.+2 = row_mx (col_mx `e^(a, skew_mx w) 0) (col_mx (h *: w^T) 1).
  admit.
rewrite /e'.
rewrite -{2}(invrK g).
rewrite expmx_mulmulV; last by rewrite unitrV rigid_trans_unitmx.
move/(congr1 (fun x => g *m x)).
rewrite !mulmxA mulmxV ?mul1mx ?rigid_trans_unitmx // invrK.
move/(congr1 (fun x => x *m g^-1)).
rewrite -mulmxA mulmxV ?mulmx1 ?rigid_trans_unitmx //.
move=> ->.*)
Abort.
*)

End exponential_coordinates_rigid.

Section quaternion.

Variable R : rcfType.

Record quat := mkQuat {quatl : R ; quatr : 'rV[R]_3 }.

(* NB: notation %:Q already defined *)
Notation "x %:q" := (mkQuat x 0) (at level 2, format "x %:q").
Notation "x %:v" := (mkQuat 0 x) (at level 2, format "x %:v").
Notation "Q '`0'" := (quatl Q) (at level 1, format "Q '`0'").
Notation "Q '`1'" := (quatr Q) (at level 1, format "Q '`1'").
Notation "Q '_i'" := ((quatr Q) 0 0) (at level 1, format "Q '_i'").
Notation "Q '_j'" := ((quatr Q) 0 1) (at level 1, format "Q '_j'").
Notation "Q '_k'" := ((quatr Q) 0 (2%:R : 'I_3)) (at level 1, format "Q '_k'").

Notation "'`i'" := (@V.i R)%:v.
Notation "'`j'" := (@V.j R)%:v.
Notation "'`k'" := (@V.k R)%:v.

Local Notation "a *`i" := (mkQuat 0 (row3 a 0 0)) (at level 3).
Local Notation "a *`j" := (mkQuat 0 (row3 0 a 0)) (at level 3).
Local Notation "a *`k" := (mkQuat 0 (row3 0 0 a)) (at level 3).

Definition pair_of_quat a := let: mkQuat a0 a1 := a in (a0, a1).
Definition quat_of_pair (x : R * 'rV[R]_3) := let: (x0, x1) := x in mkQuat x0 x1.

Lemma quat_of_pairK : cancel pair_of_quat quat_of_pair.
Proof. by case. Qed.

Definition quat_eqMixin := CanEqMixin quat_of_pairK.
Canonical Structure quat_eqType := EqType quat quat_eqMixin.
Definition quat_choiceMixin := CanChoiceMixin quat_of_pairK.
Canonical Structure quat_choiceType := ChoiceType quat quat_choiceMixin.

Lemma eq_quat a b : (a == b) = (a`0 == b`0) && (a`1 == b`1).
Proof.
case: a b => [a0 a1] [b0 b1] /=.
apply/idP/idP => [/eqP [ -> ->]|/andP[/eqP -> /eqP -> //]]; by rewrite !eqxx.
Qed.

Definition addq a b := mkQuat (a`0 + b`0) (a`1 + b`1).

Lemma addqC : commutative addq.
Proof. move=> *; congr mkQuat; by rewrite addrC. Qed. 

Lemma addqA : associative addq.
Proof. move=> *; congr mkQuat; by rewrite addrA. Qed.

Lemma add0q : left_id 0%:q addq.
Proof. case=> *; by rewrite /addq /= 2!add0r. Qed.

Definition oppq a := mkQuat (- a`0) (- a`1).

Lemma addNq : left_inverse 0%:q oppq addq.
Proof. move=> *; congr mkQuat; by rewrite addNr. Qed.

Definition quat_ZmodMixin := ZmodMixin addqA addqC add0q addNq.
Canonical quat_ZmodType := ZmodType quat quat_ZmodMixin.

Lemma addqE a b : a + b = addq a b. Proof. done. Qed.

Lemma oppqE a : - a = oppq a. Proof. done. Qed.

Lemma quatE a : a = (a`0)%:q + a _i *`i + a _j *`j + a _k *`k.
Proof.
apply/eqP; rewrite eq_quat /= !addr0 eqxx /= add0r.
case: a => /= _ a; by rewrite {1}(row3E a).
Qed.

Lemma quat_scalarE a b : (a%:q == b%:q) = (a == b).
Proof. by apply/idP/idP => [/eqP[] ->|/eqP -> //]. Qed.

Lemma quat_realD (x y : R) : (x + y)%:q = x%:q + y%:q.
Proof. by rewrite addqE /addq /= addr0. Qed.

Lemma quat_vectD (x y : 'rV[R]_3) : (x + y)%:v = x%:v + y%:v.
Proof. by rewrite addqE /addq /= addr0. Qed.

Definition mulq a b :=
  mkQuat (a`0 * b`0 - a`1 *d b`1) (a`0 *: b`1 + b`0 *: a`1 + a`1 *v b`1).

Lemma mulqA : associative mulq.
Proof.
move=> [a a'] [b b'] [c c']; congr mkQuat => /=.
- rewrite mulrDr mulrDl mulrA -!addrA; congr (_ + _).
  rewrite mulrN !dotmulDr !dotmulDl !opprD !addrA dotmul_crossmulA; congr (_ + _).
  rewrite addrC addrA; congr (_ + _ + _).
  by rewrite mulrC dotmulvZ mulrN.
  by rewrite dotmulZv.
  by rewrite dotmulvZ dotmulZv.
- rewrite 2![in LHS]scalerDr 1![in RHS]scalerDl scalerA.
  rewrite -4![in LHS]addrA -3![in RHS]addrA; congr (_ + _).
  rewrite [in RHS]scalerDr [in RHS]addrCA -[in RHS]addrA -[in LHS]addrA; congr (_ + _).
    by rewrite scalerA mulrC -scalerA.
  rewrite [in RHS]scalerDr [in LHS]scalerDl [in LHS]addrCA -[in RHS]addrA -addrA; congr (_ + _).
    by rewrite scalerA mulrC.
  rewrite (addrC (a *: _)) linearD /= (addrC (a' *v _)) linearD /=.
  rewrite -![in LHS]addrA ![in LHS]addrA (addrC (- _ *: a')) -![in LHS]addrA; congr (_ + _).
    by rewrite linearZ.
  rewrite [in RHS]crossmulC linearD /= opprD [in RHS]addrCA ![in LHS]addrA addrC -[in LHS]addrA.
  congr (_ + _); first by rewrite linearZ /= crossmulC scalerN.
  rewrite addrA addrC linearD /= opprD [in RHS]addrCA; congr (_ + _).
    by rewrite !linearZ /= crossmulC.
  rewrite 2!double_crossmul opprD opprK [in RHS]addrC addrA; congr (_ + _); last first.
    by rewrite scaleNr.
  by rewrite dotmulC scaleNr; congr (_ + _); rewrite dotmulC.
Qed.

Lemma mul1q : left_id 1%:q mulq.
Proof.
case=> a a'; rewrite /mulq /=; congr mkQuat; simp => /=.
  by rewrite dotmul0v subr0.
by rewrite crossmul0v scaler0 scale1r 2!addr0.
Qed.

Lemma mulq1 : right_id 1%:q mulq.
Proof.
case=> a a'; rewrite /mulq /=; congr mkQuat; simp => /=.
  by rewrite dotmulv0 subr0.
by rewrite scaler0 scale1r crossmulv0 add0r addr0.
Qed.

Lemma mulqDl : left_distributive mulq addq.
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulq /=; congr mkQuat => /=.
  by rewrite [in RHS]addrCA 2!addrA -mulrDl (addrC a) dotmulDl opprD addrA.
rewrite scalerDl -!addrA; congr (_ + _).
rewrite (addrCA (a' *v c')) [in RHS]addrCA; congr (_ + _).
rewrite scalerDr -addrA; congr (_ + _).
rewrite addrCA; congr (_ + _).
by rewrite crossmulC linearD /= crossmulC opprD opprK (crossmulC b').
Qed.

Lemma mulqDr : right_distributive mulq addq.
Proof.
move=> [a a'] [b b'] [c c']; rewrite /mulq /=; congr mkQuat => /=.
  rewrite mulrDr -!addrA; congr (_ + _).
  rewrite addrCA; congr (_ + _).
  by rewrite dotmulDr opprD.
rewrite scalerDr -!addrA; congr (_ + _).
rewrite (addrCA (a' *v b')) [in RHS]addrCA; congr (_ + _).
rewrite scalerDl -addrA; congr (_ + _).
by rewrite addrCA linearD.
Qed.

Lemma oneq_neq0 : 1%:q != 0 :> quat.
Proof. apply/eqP => -[]; apply/eqP. exact: oner_neq0. Qed.

Definition quat_RingMixin := RingMixin mulqA mul1q mulq1 mulqDl mulqDr oneq_neq0.
Canonical Structure quat_Ring := Eval hnf in RingType quat quat_RingMixin.

Lemma mulqE a b : a * b = mulq a b. Proof. done. Qed.

Lemma quat_realM (x y : R) : (x * y)%:q = x%:q * y%:q.
Proof.
by rewrite mulqE /mulq /= dotmul0v subr0 scaler0 add0r scaler0 crossmulv0 addr0.
Qed.

Lemma iiN1 : `i * `i = -1.
Proof.
rewrite mulqE /mulq /= scale0r crossmulvv dotmulE sum3E !mxE /=; simp => /=; congr mkQuat.
by rewrite /= oppr0.
Qed.

Lemma ijk : `i * `j = `k.
Proof.
rewrite mulqE /mulq /= 2!scale0r dotmulE sum3E !mxE /= crossmulE !mxE /=; by simp. 
Qed.

Lemma ikNj : `i * `k = - `j.
Proof.
rewrite mulqE /mulq /= 2!scale0r dotmulE sum3E !mxE /= crossmulE !mxE /=. simp.
congr mkQuat.
by simp.
apply/rowP => i; rewrite !mxE /=.
case : ifP; first by simp.
by do 2 case: ifP => //; simp.
Qed.

Definition sqrq a := a`0 ^+ 2 + norm (a`1) ^+ 2.

Lemma sqrq_eq0 a : (sqrq a == 0) = (a == 0).
Proof.
case: a => a a' /=; apply/idP/idP.
  by rewrite /sqrq /= paddr_eq0 ?sqr_ge0 // ?norm_ge0 // 2!sqrf_eq0 norm_eq0 => /andP[/eqP -> /eqP ->].
by case/eqP => -> ->; rewrite /sqrq /= norm0 expr0n addr0.
Qed.

Definition scaleq k a := mkQuat (k * a`0) (k *: a`1).

Lemma scaleqA a b w : scaleq a (scaleq b w) = scaleq (a * b) w.
Proof. rewrite /scaleq /=; congr mkQuat; by [rewrite mulrA | rewrite scalerA]. Qed.

Lemma scaleq1 : left_id 1 scaleq.
Proof.
by move=> q; rewrite /scaleq mul1r scale1r; apply/eqP; rewrite eq_quat /= !eqxx.
Qed.

Lemma scaleqDr : @right_distributive R quat scaleq +%R.
Proof. move=> a b c; by rewrite /scaleq /= mulrDr scalerDr. Qed.

Lemma scaleqDl w : {morph (scaleq^~ w : R -> quat) : a b / a + b}.
Proof. move=> m n; rewrite /scaleq mulrDl /= scalerDl; congr mkQuat. Qed.

Definition quat_lmodMixin := LmodMixin scaleqA scaleq1 scaleqDr scaleqDl.
Canonical quat_lmodType := Eval hnf in LmodType R quat quat_lmodMixin.

Lemma scaleqE (k : R) (a : quat) : 
  k *: a = k *: (a `0) %:q + k *: (a _i) *`i + k *: (a _j) *`j + k *: (a _k) *`k.
Proof. apply/eqP; by rewrite eq_quat /= !mulr0 !addr0 eqxx /= -3!scalerDr add0r -row3E. Qed.

Definition conjq (Q : quat) := mkQuat (Q`0) (- Q`1).
Notation "x '^*q'" := (conjq x) (at level 2, format "x '^*q'").

Lemma conjqI a : (a^*q)^*q = a.
Proof. by case: a => a0 a1; rewrite /conjq /= opprK. Qed.

Lemma conjq0 : (0%:v)^*q = 0.
Proof. apply/eqP; by rewrite eq_quat /= oppr0 !eqxx. Qed.

Lemma conjqP a : a * a^*q = (sqrq a)%:q.
Proof.
rewrite /mulq /=; congr mkQuat.
  by rewrite /= dotmulvN dotmulvv opprK -expr2.
by rewrite scalerN addNr add0r crossmulvN crossmulvv oppr0.
Qed.

Lemma conjqM a b : (a * b)^*q = b^*q * a^*q.
Proof.
case: a b => [a0 a1] [b0 b1].
rewrite /conjq /= mulqE /mulq /= mulrC dotmulC dotmulvN dotmulNv opprK; congr mkQuat.
by rewrite 2!opprD 2!scalerN linearN /= -(crossmulC a1) linearN /= -2!scaleNr -addrA addrCA addrA.
Qed.

Lemma conjqE a : a^*q = - (1 / 2%:R) *: (a + `i * a * `i + `j * a * `j + `k * a * `k).
Proof.
apply/eqP; rewrite eq_quat; apply/andP; split; apply/eqP.
  rewrite [in LHS]/= scaleqE /=.
  rewrite !(mul0r,mulr0,addr0) scale0r !add0r !dotmulDl.
  rewrite dotmulZv dotmulvv V.normi expr1n mulr1 dotmulC dotmul_crossmulA crossmulvv dotmul0v addr0.
  rewrite subrr add0r dotmulZv dotmulvv V.normj expr1n mulr1 dotmulC dotmul_crossmulA crossmulvv.
  rewrite dotmul0v addr0 dotmulZv dotmulvv V.normk expr1n mulr1 opprD addrA dotmulC dotmul_crossmulA.
  rewrite crossmulvv dotmul0v subr0 -opprD mulrN mulNr opprK -mulr2n -(mulr_natl (a`0)) mulrA.
  by rewrite div1r mulVr ?mul1r // unitfE pnatr_eq0.
rewrite /=.
rewrite !(mul0r,scale0r,add0r,addr0).
rewrite [_ *v V.i]crossmulC [V.i *v _]linearD /= [V.i *v _]linearZ /= crossmulvv.
rewrite scaler0 add0r double_crossmul dotmulvv V.normi expr1n scale1r.
rewrite [_ *v V.j]crossmulC [V.j *v _]linearD /= [V.j *v _]linearZ /= crossmulvv.
rewrite scaler0 add0r double_crossmul dotmulvv V.normj expr1n scale1r.
rewrite [_ *v V.k]crossmulC [V.k *v _]linearD /= [V.k *v _]linearZ /= crossmulvv.
rewrite scaler0 add0r double_crossmul dotmulvv V.normk expr1n scale1r.
rewrite [X in _ = - _ *: X](_ : _ = 2%:R *:a`1).
  by rewrite scalerA mulNr div1r mulVr ?unitfE ?pnatr_eq0 // scaleN1r.
rewrite !opprB (addrCA _ a`1) addrA -mulr2n scaler_nat -[RHS]addr0 -3!addrA; congr (_ + _).
do 3 rewrite (addrCA _ a`1).
do 2 rewrite addrC -!addrA.
rewrite -opprB (scaleNr _ V.i) opprK -mulr2n addrA -mulr2n.
rewrite addrC addrA -opprB scaleNr opprK -mulr2n.
rewrite -2!addrA addrC 2!addrA -(opprB (_ *: V.k)) scaleNr opprK -mulr2n.
rewrite -!mulNrn -3!mulrnDl -scaler_nat.
apply/eqP; rewrite scalemx_eq0 pnatr_eq0 /=.
rewrite addrAC eq_sym -subr_eq add0r -opprB eqr_opp.
rewrite opprB opprK addrA.
rewrite {1}(orthogonal_expansion a`1 (V.frame R)) /=.
by rewrite 3!(dotmulC a`1) -[in X in _ == X]addrA addrCA addrA.
Qed.

Lemma conjq_scalar a : (a`0)%:q = (1 / 2%:R) *: (a + a^*q).
Proof.
case: a => a0 a1.
rewrite /conjq /= addqE /addq /= subrr quat_realD scalerDr -scalerDl.
by rewrite -mulr2n -mulr_natr div1r mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Lemma conjq_vector a : (a`1)%:v = (1 / 2%:R) *: (a - a^*q).
Proof.
case: a => a0 a1.
rewrite /conjq /= addqE /addq /= subrr opprK quat_vectD scalerDr -scalerDl.
by rewrite -mulr2n -mulr_natr div1r mulVr ?scale1r // unitfE pnatr_eq0.
Qed.

Definition invq a := (1 / sqrq a) *: (a ^*q).

Definition unitq : pred quat := [pred a | a != 0%:q].

Lemma mulVq : {in unitq, left_inverse 1 invq mulq}.
Proof.
move=> a; rewrite inE /= => a0.
rewrite /invq /mulq /=; congr mkQuat.
  rewrite dotmulZv -mulrA -mulrBr dotmulNv opprK dotmulvv.
  by rewrite div1r mulVr // unitfE sqrq_eq0.
rewrite scalerA scalerN -scalerBl mulrC subrr scale0r.
by rewrite scalerN crossmulNv crossmulZ crossmulvv scaler0 subrr.
Qed.

Lemma mulqV : {in unitq, right_inverse 1 invq mulq}.
Proof.
move=> a; rewrite inE /= => a0.
rewrite /invq /mulq /=; congr mkQuat.
  by rewrite scalerN dotmulvN opprK dotmulvZ mulrCA -mulrDr dotmulvv div1r mulVr // unitfE sqrq_eq0.
by rewrite scalerA scalerN -scaleNr -scalerDl mulrC addNr scale0r linearZ /= crossmulvN crossmulvv scalerN scaler0 subrr.
Qed.

Lemma unitqP a b : b * a = 1 /\ a * b = 1 -> unitq a.
Proof.
move=> [ba1 ab1]; rewrite /unitq inE; apply/eqP => x0.
move/esym: ab1; rewrite x0 mul0r.
apply/eqP; exact: oneq_neq0.
Qed.

Lemma invq0id : {in [predC unitq], invq =1 id}.
Proof.
move=> a; rewrite !inE negbK => /eqP ->.
by rewrite /invq /= conjq0 scaler0.
Qed.

Definition quat_UnitRingMixin := UnitRingMixin mulVq mulqV unitqP invq0id.
Canonical quat_unitRing := UnitRingType quat quat_UnitRingMixin.

Lemma invqE a : a^-1 = invq a. Proof. by done. Qed.

Definition normq (a : quat) : R := Num.sqrt (sqrq a).

Lemma normq0 : normq 0 = 0.
Proof. by rewrite /normq /sqrq expr0n /= norm0 add0r expr0n sqrtr0. Qed.

Lemma normqc a : normq a^*q = normq a.
Proof. by rewrite /normq /sqrq /= normN. Qed.

Lemma normqE a : (normq a ^+ 2)%:q = a^*q * a.
Proof.
rewrite -normqc /normq sqr_sqrtr; last by rewrite /sqrq addr_ge0 // sqr_ge0.
by rewrite -conjqP conjqI.
Qed.

Lemma normq_ge0 a : normq a >= 0.
Proof. by apply sqrtr_ge0. Qed.

Lemma normq_eq0 a : (normq a == 0) = (a == 0).
Proof.
rewrite /normq /sqrq -sqrtr0 eqr_sqrt //; last by rewrite addr_ge0 // sqr_ge0.
by rewrite paddr_eq0 ?sqr_ge0 // 2!sqrf_eq0 norm_eq0 eq_quat.
Qed.

Lemma quatAl k (a b : quat) : k *: (a * b) = k *: a * b.
Proof.
case: a b => [a0 a1] [b0 b1]; apply/eqP.
rewrite !mulqE /mulq /= scaleqE /= eq_quat /=.
apply/andP; split; first by rewrite mulr0 !addr0 mulrBr mulrA dotmulZv.
apply/eqP.
rewrite scaler0 add0r -2!scalerDr -row3E -scalerA (scalerA b0 k) mulrC.
rewrite -scalerA [in RHS]crossmulC [in X in _ = _ + _ + X]linearZ /=.
by rewrite -scalerDr -scalerBr crossmulC.
Qed.

Canonical quat_lAlgType := Eval hnf in LalgType _ quat quatAl.

Lemma quatAr k (a b : quat) : k *: (a * b) = a * (k *: b).
Proof.
case: a b => [a0 a1] [b0 b1]; apply/eqP.
rewrite !mulqE /mulq /= scaleqE /= eq_quat /=.
apply/andP; split; first by rewrite mulr0 !addr0 mulrBr mulrCA dotmulvZ.
apply/eqP.
rewrite scaler0 add0r -2!scalerDr -row3E -scalerA (scalerA a0 k) mulrC.
by rewrite -scalerA [in X in _ = _ + _ + X]linearZ /= -2!scalerDr.
Qed.

Canonical quat_algType := Eval hnf in AlgType _ quat quatAr.

Lemma quat_algE x : x%:q = x%:A.
Proof.
apply/eqP.
rewrite scaleqE !mxE eq_quat /= mulr0 mulr1 !addr0 eqxx /= scaler0 add0r.
by rewrite row30 ?scaler0 ?addr0.
Qed.

Lemma normqM (Q P : quat) : normq (Q * P) = normq Q * normq P.
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) // ?normq_ge0 //; last first.
  by rewrite mulr_ge0 // normq_ge0.
rewrite -quat_scalarE normqE conjqM -mulrA (mulrA (Q^*q)) -normqE.
rewrite quat_algE mulr_algl -scalerAr exprMn quat_realM.
by rewrite (normqE P) -mulr_algl quat_algE.
Qed.

Lemma normqZ (k : R) (q : quat) : normq (k *: q) = `|k| * normq q.
Proof.
by rewrite /normq /sqrq /= normZ 2!exprMn norm2 -mulrDr sqrtrM ?sqr_ge0 // sqrtr_sqr.
Qed.

Lemma normqV (q : quat) : normq (q^-1) = normq q / sqrq q.
Proof.
rewrite invqE /invq normqZ ger0_norm; last first.
  by rewrite divr_ge0 // ?ler01 // /sqrq addr_ge0 // sqr_ge0.
by rewrite normqc mulrC mul1r.
Qed.

Definition normQ Q := (normq Q)%:q. 

Lemma normQ_eq0 x : (normQ x == 0) = (x == 0).
Proof. by rewrite /normQ quat_scalarE normq_eq0. Qed.

Definition normalizeq (q : quat) : quat := 1 / normq q *: q.

Lemma normalizeq1 (q : quat) : q != 0 -> normq (normalizeq q) = 1.
Proof.
move=> q0.
rewrite /normalizeq normqZ normrM normr1 mul1r normrV; last by rewrite unitfE normq_eq0.
by rewrite ger0_norm ?normq_ge0 // mulVr // unitfE normq_eq0.
Qed.

Definition lequat (Q P : quat) := 
  let: mkQuat Q1 Q2 := Q in let: mkQuat P1 P2 := P in
  (Q2 == P2) && (Q1 <= P1).

Lemma lequat_normD x y : lequat (normQ (x + y)) (normQ x + normQ y).
Proof.
Abort.

Definition ltquat (Q P : quat) := 
  let: mkQuat Q1 Q2 := Q in let: mkQuat P1 P2 := P in
  (Q2 == P2) && (Q1 < P1).

Lemma ltquat0_add : forall x y, ltquat 0 x -> ltquat 0 y -> ltquat 0 (x + y).
Abort.

Lemma ge0_lequat_total x y : lequat 0 x -> lequat 0 y -> lequat x y || lequat y x.
Abort.

Lemma normQM x y : normQ (x * y) = normQ x * normQ y.
Proof. by rewrite {1}/normQ normqM quat_realM. Qed.

Lemma lequat_def x y : lequat x y = (normQ (y - x) == y - x).
Abort.

Lemma ltquat_def x y : ltquat x y = (y != x) && lequat x y.
Abort.

Fail Definition quat_POrderedMixin := NumMixin lequat_normD ltquat0_add eq0_normQ
  ge0_lequat_total normQM lequat_def ltquat_def.
Fail Canonical Structure quat_numDomainType :=
  NumDomainType _ quat_POrderedMixin.

Definition uquat := [qualify x : quat | normq x == 1].
Fact uquat_key : pred_key uquat. Proof. by []. Qed.
Canonical uquat_keyed := KeyedQualifier uquat_key.

(*Record uquat := mkUQuat {
  quat_of_uquat :> quat ;
  _ : normq quat_of_uquat == 1 }.

Canonical uquat_subType := [subType for quat_of_uquat].*)

Lemma uquatE a : (a \is uquat) = (normq a == 1).
Proof. done. Qed.

Lemma uquatE' (q : quat) : (q \is uquat) = (sqrq q == 1).
Proof.
apply/idP/idP => [qu|].
  rewrite -eqr_sqrt ?ler01 //.
    rewrite uquatE in qu; by rewrite -/(normq q) (eqP qu) sqrtr1.
  by rewrite /sqrq addr_ge0 // sqr_ge0.
rewrite uquatE /normq => /eqP ->; by rewrite sqrtr1.
Qed.

(*Definition uquat_eqMixin := [eqMixin of uquat by <:].
Canonical uquat_eqType := EqType uquat uquat_eqMixin.
Definition uquat_choiceMixin := [choiceMixin of uquat by <:].
Canonical uquat_choiceType := ChoiceType uquat uquat_choiceMixin.
*)

Lemma muluq_proof a b : a \is uquat -> b \is uquat -> a * b \is uquat.
Proof. rewrite 3!uquatE => /eqP Hq /eqP Hp; by rewrite normqM Hq Hp mulr1. Qed.

Lemma invuq_proof a : a \is uquat -> normq (a^-1) == 1.
Proof.
move=> Hq; rewrite normqV.
move: (Hq); rewrite uquatE => /eqP ->.
move: Hq; rewrite uquatE' => /eqP ->.
by rewrite invr1 mulr1.
Qed.

(*Definition invuq (q : uquat) : uquat := mkUQuat (invuq_proof q).*)

Lemma invq_uquat a : a \is uquat -> a^-1 = a^*q.
Proof. 
rewrite uquatE' => /eqP Hq; by rewrite invqE /invq Hq invr1 mul1r scale1r.
Qed.

Definition polar_of_uquat (a : quat) := (normalize a`1, atan (norm a`1 / a`0)).

Lemma norm_polar_of_uquat q : q \is uquat ->
  let: (u, a) := polar_of_uquat q in
  normq (mkQuat (cos a) (sin a *: u)) = 1.
Proof.
move=> Hq.
case: q Hq => [q0 q1] nq.
case/boolP : (q1 == 0) => [/eqP /= ->|q10].
  by rewrite norm0 mul0r atan0 cos0 sin0 scale0r /normq /sqrq /= norm0 expr0n addr0 expr1n sqrtr1.
by rewrite /= /normq /sqrq /= normZ exprMn norm_normalize // expr1n mulr1 norm2 cos2Dsin2 sqrtr1.
Qed.

Definition quat_of_polar (a : angle R) (w : 'rV[R]_3) : quat :=
  mkQuat (cos (half_angle a)) (sin (half_angle a) *: w).

Lemma uquat_of_polar a w (H : norm w = 1) : quat_of_polar a w \is uquat.
Proof.
by rewrite uquatE /normq /sqrq /= normZ exprMn H expr1n mulr1 norm2 cos2Dsin2 sqrtr1.
Qed.

Let vector := 'rV[R]_3.

Definition quat_rot (a : quat) (v : vector) : quat := (a : quat) * v%:v * a^*q.

Lemma quat_rotE a v : quat_rot a v = 
  ((a`0 ^+ 2 - norm a`1 ^+ 2) *: v +
   ((a`1 *d v) *: a`1) *+ 2 +
   (a`0 *: (a`1 *v v)) *+ 2)%:v.
Proof.
case: a => a0 a1 /=.
rewrite /quat_rot /= /conjq /= mulqE /mulq /=.
rewrite mulr0 scale0r addr0 add0r; congr mkQuat.
  rewrite dotmulvN opprK dotmulDl (dotmulC (_ *v _) a1) dotmul_crossmulA.
  by rewrite crossmulvv dotmul0v addr0 dotmulZv mulrC mulrN dotmulC addrC subrr.
rewrite scalerDr scalerA -expr2 addrCA scalerBl -!addrA; congr (_ + _).
rewrite [in X in _ + X = _]linearN /= (crossmulC _ a1) linearD /= opprK.
rewrite linearZ /= (addrA (a0 *: _ )) -mulr2n.
rewrite [in LHS]addrCA 2![in RHS]addrA [in RHS]addrC; congr (_ + _).
rewrite scalerN scaleNr opprK -addrA addrCA; congr (_ + _).
by rewrite double_crossmul [in RHS]addrC dotmulvv.
Qed.

Definition pureq (q : quat) : bool := q`0 == 0.

Lemma quat_rot_is_vector a v : pureq (quat_rot a v).
Proof. by rewrite quat_rotE /pureq /=. Qed.

Lemma quat_rot_is_linear q : linear (fun v => (quat_rot q v)`1).
Proof.
move=> k a b.
rewrite !quat_rotE /= scalerDr scalerA (mulrC _ k) -scalerA.
rewrite 2![in RHS]scalerDr -2![in LHS]addrA -3![in RHS]addrA; congr (_ + _).
rewrite [in RHS]addrA [in RHS]addrCA -[in RHS]addrA; congr (_ + _).
rewrite dotmulDr scalerDl mulrnDl -addrA addrCA; congr (_ + _).
rewrite dotmulvZ -scalerA scalerMnr -addrA; congr (_ + _).
rewrite linearD /= scalerDr mulrnDl; congr (_ + _).
by rewrite linearZ /= scalerA mulrC -scalerA -scalerMnr.
Qed.

Lemma quat_rot_is_linearE q v : Linear (quat_rot_is_linear q) v = (quat_rot q v)`1.
Proof. done. Qed.

Lemma quat_rot_axis q k : q \is uquat -> quat_rot q (k *: q`1) = (k *: q`1)%:v.
Proof.
rewrite uquatE' /sqrq => /eqP q_is_uquat; rewrite quat_rotE.
rewrite [in X in (_ + _ + X)%:v = _]linearZ /= crossmulvv 2!scaler0 mul0rn addr0.
rewrite dotmulvZ dotmulvv scalerBl !scalerA (mulrC (norm _ ^+ 2)) mulr2n addrA.
by rewrite subrK -scalerDl mulrC -mulrDr q_is_uquat mulr1.
Qed.

Lemma cos_atan_uquat q : q \is uquat -> ~~ pureq q -> 
  let a := atan (norm q`1 / q`0) in
  cos a ^+ 2 = q`0 ^+ 2.
Proof.
move=> nq q00 a.
rewrite /a cos_atan; last by rewrite atan_in // mulf_neq0 // ?invr_eq0.
rewrite exprMn expr1n mul1r.
have /divrr <- : q`0 ^+ 2 \in GRing.unit by rewrite unitfE sqrf_eq0.
rewrite expr_div_n -mulrDl.
rewrite uquatE' /sqrq in nq.
rewrite (eqP nq) sqrtrM ?ler01 // sqrtr1 mul1r -exprVn sqrtr_sqr.
by rewrite normrV ?unitfE // invrK norm2.
Qed.

Lemma sin_atan_uquat q : q \is uquat -> ~~ pureq q ->
  let a := atan (norm q`1 / q`0) in
  sin a ^+ 2 = norm q`1 ^+ 2.
Proof.
move=> nq q00 a.
rewrite /a sin_atan2.
have /divrr <- : q`0 ^+ 2 \in GRing.unit by rewrite unitfE sqrf_eq0.
rewrite expr_div_n -mulrDl.
rewrite uquatE' /sqrq in nq.
by rewrite (eqP nq) mul1r invrK -mulrA mulVr ?mulr1 // unitrX // unitfE.
Qed.

Lemma polar_of_uquat_prop q : q \is uquat -> ~~ pureq q -> 
  let: a := (polar_of_uquat q).2 in
  cos (a *+ 2) = q`0 ^+ 2 - norm q`1 ^+ 2.
Proof.
move=> ? ?; by rewrite mulr2n cosD -2!expr2 cos_atan_uquat // sin_atan_uquat.
Qed.

Lemma polar_of_uquat_prop2 q : q \is uquat -> q`0 != 0 -> 
  let: a := (polar_of_uquat q).2 in
  sin (a *+ 2) = (q`0 * norm q`1) *+ 2.
Proof.
move=> q_is_uquat q00.
rewrite /= sin_mulr2n cos_atan; last by rewrite atan_in.
rewrite sin_atan.
set k := Num.sqrt _; congr (_ *+ 2).
have k0 : k \is a GRing.unit.
  by rewrite unitfE sqrtr_eq0 -ltrNge -(addr0 0) ltr_le_add // ?ltr01 // sqr_ge0.
rewrite div1r mulrCA -invrM // [in RHS]mulrC -mulrA; congr (_ * _).
apply (@mulrI _ q`0); first by rewrite unitfE.
rewrite mulrA divrr ?unitfE // mul1r -2!expr2 sqr_sqrtr; last first.
  by rewrite addr_ge0 // ?ler01 // sqr_ge0.
have /divrr <- : q`0 ^+ 2 \is a GRing.unit by rewrite unitrX // unitfE.
rewrite uquatE' /sqrq in q_is_uquat.
by rewrite exprMn exprVn -mulrDl (eqP q_is_uquat) -exprVn mul1r -exprVn invrK.
Qed.

Lemma quat_rot_is_Rot (q : quat) : q \is uquat -> ~~ pureq q ->
  let: (u, a) := polar_of_uquat q in
  u != 0 ->
  is_around_axis u (- (a *+ 2)) (Linear (quat_rot_is_linear q)).
Proof.
move=> q_isuqat. rewrite /pureq => q00 u0.
set a := atan _.
split.
- set u := normalize q`1.
  simpl in u.
  rewrite -/u in u0.
  by rewrite quat_rot_is_linearE quat_rot_axis.
- move: (pframe_of_i u0).
  set v := j_of_i _. set w := k_of_i _ => f.
  rewrite quat_rot_is_linearE quat_rotE /= (_ : q`1 *d v = 0); last first.
    move: (idotj f).
    (* TODO: lemma? *)
    rewrite normalizeI // ?norm_normalize //; last by rewrite -normalize_eq0.
    rewrite /= /normalize dotmulZv => /eqP.
    rewrite mulf_eq0 => /orP [ | /eqP //].
    by rewrite div1r invr_eq0 norm_eq0 -normalize_eq0 (negbTE u0).
  rewrite scale0r mul0rn addr0.
  rewrite (_ : q`1 *v v = norm q`1 *: w); last first.
    move: (icrossj f) => /= ->.
    rewrite normalizeI ?norm_normalize //; last by rewrite -normalize_eq0.
    by rewrite [in RHS]crossmulC scalerN -linearZ /= norm_scale_normalize crossmulC.
  rewrite scalerMnl [in X in _ + X = _]scalerA; congr (_ *: _ + _ *: _).
  by rewrite cosN polar_of_uquat_prop.
  by rewrite mulrnAl -sinN opprK polar_of_uquat_prop2.
- move: (pframe_of_i u0).
  set v := j_of_i _. set w := k_of_i _ => f.
  rewrite quat_rot_is_linearE quat_rotE /= (_ : q`1 *d w = 0); last first.
    move: (idotk f).
    (* TODO: this should be shorter *)
    rewrite normalizeI // ?norm_normalize //; last by rewrite -normalize_eq0.
    rewrite /normalize dotmulZv /= => /eqP; rewrite mulf_eq0 => /orP [| /eqP //].
    by rewrite div1r invr_eq0 norm_eq0 -normalize_eq0 (negbTE u0).
  rewrite scale0r mul0rn addr0.
  rewrite (_ : q`1 *v w = - norm q`1 *: v); last first.
    move: (icrossk f) => /=.
    rewrite normalizeI ?norm_normalize //; last by rewrite -normalize_eq0.
    move/eqP; rewrite -eqr_oppLR => /eqP <-.
  by rewrite [in RHS]crossmulC opprK -linearZ /= scaleNr norm_scale_normalize linearN /= crossmulC.
rewrite addrC; congr (_ + _ *: _); last first.
  by rewrite cosN -polar_of_uquat_prop.
rewrite scaleNr scalerN scalerA mulNrn scalerMnl -scaleNr; congr (_ *: _).
by rewrite sinN polar_of_uquat_prop2 // ?opprK.
Qed.

End quaternion.

(*

  option ('rV[R]_3 (* point *) * 'rV[R]_3 (* vec *) ).
Admitted.

Definition intersection (o o' : 'rV[R]_3) (v v' : 'rV[R]_3) : option 'rV[R]_3.
Admitted.

Definition length_prop (i : 'I_n) (f f' : frame) :
  unique_common_orthogonal (origin f) (origin f') ()
  length (links i) = `| |


Definition z_vec (i : 'I_n) := zframes i



joint i is located between links i-1 and i
z_vec (frames i) "is located along the axis of joint i"

the zi axis along the axis of joint i


Definition before_after_joint (i : 'I_n) : option (link * link):=
  match ltnP O i with
    | LtnNotGeq H (* 0 < i*) => Some (links i.-1, links i)
    | GeqNotLtn H (* i <= 0*) => None
  end.

link length and twist along and about the x_i-1 axis

Hypothesis :

Check forall i, (z_ax (basis (frames i))).

x_vec (frames i.-1) _|_ plane (z_vec (frames i.-1)),(z_vec (frames i))

length (links i) = distance from (z_vec (frames i.-1)) to (z_vec (frames i)) along (x_vec)





 *)
