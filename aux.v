Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrnum ssrint div rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial.
From mathcomp
Require Import perm finset path fingroup complex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.

Reserved Notation "u '``_' i"
    (at level 3, i at level 2, left associativity, format "u '``_' i").
Notation "u '``_' i" := (u (GRing.zero (Zp_zmodType O)) i) : ring_scope.
Notation "''e_' i" := (delta_mx 0 i)
 (format "''e_' i", at level 3) : ring_scope.
Local Open Scope ring_scope.

Lemma row_mx_eq0 (M : zmodType) (m n1 n2 : nat)
 (A1 : 'M[M]_(m, n1)) (A2 : 'M_(m, n2)):
 (row_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
apply/eqP/andP; last by case=> /eqP -> /eqP ->; rewrite row_mx0.
by rewrite -row_mx0 => /eq_row_mx [-> ->].
Qed.

Lemma col_mx_eq0 (M : zmodType) (m1 m2 n : nat)
 (A1 : 'M[M]_(m1, n)) (A2 : 'M_(m2, n)):
 (col_mx A1 A2 == 0) = (A1 == 0) && (A2 == 0).
Proof.
by rewrite -![_ == 0](inj_eq (@trmx_inj _ _ _)) !trmx0 tr_col_mx row_mx_eq0.
Qed.

Lemma col_mx_row_mx (T : ringType) (m1 n1 : nat) (A : 'M[T]_(m1, n1)) n2 m2 :
  col_mx (row_mx A (0 : 'M_(m1, n2))) (0 : 'M_(m2, n1 + n2)) = row_mx (col_mx A 0) 0.
Proof.
set a : 'M_(m2, _ + n2) := 0.
have -> : a = row_mx (0 : 'M_(m2, n1)) 0 by rewrite row_mx0.
by rewrite -block_mxEv block_mxEh col_mx0.
Qed.

(* courtesy of GG *)
Lemma mxdirect_delta (F : fieldType) (T : finType) (n : nat) (P : pred T) f :
  {in P & , injective f} ->
  mxdirect (\sum_(i | P i) <<'e_(f i) : 'rV[F]_n>>)%MS.
Proof.
pose fP := image f P => Uf; have UfP: uniq fP by apply/dinjectiveP.
suffices /mxdirectP: mxdirect (\sum_i <<'e_i : 'rV[F]_n>>).
  rewrite /= !(bigID [mem fP] predT) -!big_uniq //= !big_map !big_filter.
  by move/mxdirectP; rewrite mxdirect_addsE => /andP[].
apply/mxdirectP=> /=; transitivity (mxrank (1%:M : 'M[F]_n)).
  apply/eqmx_rank; rewrite submx1 mx1_sum_delta summx_sub_sums // => i _.
  by rewrite -(mul_delta_mx (0 : 'I_1)) genmxE submxMl.
rewrite mxrank1 -[LHS]card_ord -sum1_card.
by apply/eq_bigr=> i _; rewrite /= mxrank_gen mxrank_delta.
Qed.

Lemma sqr_normr (R : realDomainType) (k : R) : `| k | ^+ 2 = k ^+ 2.
Proof. by rewrite real_normK ?num_real. Qed.

Lemma pnatf_unit {R : numFieldType} n : n.+1%:R \is a @GRing.unit R.
Proof. by rewrite unitfE pnatr_eq0. Qed.

Lemma lift0E m (i : 'I_m.+1) : fintype.lift ord0 i = i.+1%:R.
Proof. by apply/val_inj; rewrite Zp_nat /= modn_small // ltnS. Qed.

Module Simp.
Ltac ord :=
  do ?[rewrite !lift0E
      |rewrite ord1
      |rewrite -[ord_max]natr_Zp /=
      |rewrite -[widen_ord _ _]natr_Zp /=
      |rewrite -[fintype.lift _ _]natr_Zp /=
      |rewrite -[Ordinal _]natr_Zp /=
      |rewrite -[_ + _ : 'I__]natr_Zp /=
      |rewrite -[_ * _ : 'I__]natr_Zp /=
      |rewrite -[- _ : 'I__]natr_Zp /=].

Ltac r := rewrite ?(Monoid.simpm,
                    mulr0,mul0r,mul1r,mulr1,addr0,add0r,
                    mulr1n,mulNr,mulrN,opprK,oppr0,
                    scale0r, scaler0, scaleN1r, scale1r,
                    eqxx).

End Simp.

Lemma rew_condAr (a b c : bool) : a = b && c -> (b -> c = a).
Proof. by case: b. Qed.

Lemma ifnot01 (i : 'I_2) : (i != 0) = (i == 1).
Proof. by case: i => -[] // []. Qed.

Lemma liftE0 m (i : 'I_m.+2) : fintype.lift i ord0 = (i == 0)%:R.
Proof. by Simp.ord; rewrite -val_eqE /=; case: (val i). Qed.

Lemma liftE1 {m} (i : 'I_m.+3) : fintype.lift i 1 = (i <= 1).+1%:R.
Proof. by Simp.ord; case: (val i) => [|[]]. Qed.

(*Lemma sum1E_gen {T : ringType} (f : 'I_1 -> T) P : \sum_(i < 1 | P i) f i = (P ord0)%:R * f 0.
Proof.
case/boolP : (P ord0) => P0; rewrite ?(mul1r,mul0r).
  by rewrite (bigD1 ord0) //= big1 ?addr0 // => i; rewrite (ord1 i) eqxx andbF.
by rewrite big1 // => /= i; rewrite (ord1 i) (negbTE P0).
Qed.  *)

Lemma sum1E {T : ringType} (f : 'I_1 -> T) : \sum_(i < 1) f i = f 0.
Proof. by rewrite big_ord1. Qed.

Lemma sum2E {T : ringType} (f : 'I_2 -> T) : \sum_(i < 2) f i = f 0 + f 1.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma sum3E {T : ringType} (f : 'I_3 -> T) : \sum_(i < 3) f i = f 0 + f 1 + f 2%:R.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma sum4E {T : ringType} (f : 'I_4 -> T) : \sum_(i < 4) f i = f 0 + f 1 + f 2%:R + f 3%:R.
Proof. by rewrite !(big_ord1, big_ord_recr) /=; Simp.ord. Qed.

Lemma opp_self {R : rcfType} n (u : 'rV[R]_n) : u = - u -> u = 0.
Proof.
move/eqP.
by rewrite -subr_eq0 opprK -mulr2n -scaler_nat scaler_eq0 pnatr_eq0 /= => /eqP.
Qed.

Section extra_complex.

Variable R : rcfType.

Lemma opp_conjc (a b : R) : (- (a -i* b) = (- a +i* b))%C.
Proof. by apply/eqP; rewrite eq_complex /= opprK !eqxx. Qed.

Lemma Re_scale (x : R[i]) (k : R) : k != 0 -> complex.Re (x / k%:C%C) = complex.Re x / k.
Proof.
move=> k0; case: x => a b /=.
rewrite expr0n /= addr0 mul0r -mulrN opprK mulr0 addr0.
by rewrite expr2 invrM // ?unitfE // (mulrA k) divff // mul1r.
Qed.

Lemma complexZ1 (a b k : R) : ((k * a) +i* (k * b) = k%:C * (a +i* b))%C.
Proof. by simpc. Qed.

Lemma complexZ2 (a b k : R) : ((k * a) -i* (k * b) = k%:C * (a -i* b))%C.
Proof. by simpc. Qed.

Lemma ReZ (x : R[i]) (k : R) : complex.Re (k%:C%C * x) = k * complex.Re x.
Proof. case: x => a b /=; by rewrite mul0r subr0. Qed.

Lemma ImZ (x : R[i]) (k : R) : complex.Im ((k%:C)%C * x) = k * complex.Im x.
Proof. by case: x => a b /=; rewrite mul0r addr0. Qed.

Definition complexZ := (complexZ1, @complexZ2).

End extra_complex.
