From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import interval reals trigo.

(******************************************************************************)
(*    Extra material for trigo                                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.


Arguments pi {R}.

Section Extra.

Variable R : realType.

Implicit Types a : R.

Definition norm_angle a := 
  if sin a < 0 then - acos (cos a) else acos (cos a).

Lemma cos_norm_angle a : cos (norm_angle a) = cos a.
Proof.
rewrite /norm_angle.
by case: ltP; rewrite ?cosN acosK // in_itv/= cos_geN1 cos_le1.
Qed.

Lemma sin_norm_angle a : sin (norm_angle a) = sin a.
Proof.
rewrite /norm_angle.
case: ltP => [sa_lt0|sa_gt0]; rewrite ?sinN sin_acos.
  rewrite -sin2cos2 sqrtr_sqr ltr0_norm // opprK //.
  by rewrite cos_geN1 cos_le1.
rewrite -sin2cos2 sqrtr_sqr ger0_norm //.
by rewrite cos_geN1 cos_le1.
Qed.

Lemma norm_angle_lepi a : norm_angle a <= pi.
Proof.
rewrite /norm_angle; case: (ltP _ 0) => [sa_gt0|sa_lt0]; last first.
  by rewrite acos_lepi ?(cos_geN1, cos_le1).
rewrite ler_oppl. 
apply: le_trans (acos_ge0  _); first by rewrite oppr_cp0 pi_ge0.
by rewrite ?(cos_geN1, cos_le1).
Qed.

Lemma norm_angle_gtNpi a : - pi < norm_angle a.
Proof.
rewrite /norm_angle; case: (ltP _ 0) => [sa_gt0|sa_lt0]; last first.
  apply: lt_le_trans (acos_ge0  _); first by rewrite oppr_cp0 pi_gt0.
  by rewrite !(cos_geN1, cos_le1).
rewrite ltr_oppl opprK acos_ltpi // ?(cos_le1, andbT).
have := cos_geN1 a; case: ltgtP => // caE.
have := sa_gt0; have /eqP := sin2cos2 a; rewrite -caE.
by rewrite -signr_odd /= expr0 subrr expf_eq0 /= => /eqP ->; rewrite ltxx.
Qed.

Lemma norm_angle_bound a : - pi < norm_angle a <= pi.
Proof. by rewrite norm_angle_gtNpi norm_angle_lepi. Qed.


Lemma acos1 : acos (1 : R) = 0.
Proof.
have := @cosK R 0; rewrite cos0 => -> //.
by rewrite in_itv //= lexx pi_ge0.
Qed.

Lemma acos0 : acos (0 : R) = pi / 2%:R.
Proof.
have := @cosK R (pi / 2%:R).
rewrite cos_pihalf => -> //.
rewrite in_itv //= divr_ge0 ?ler0n ?pi_ge0 //=.
rewrite ler_pdivr_mulr ?ltr0n //.
by rewrite mulr_natr mulr2n -ler_subl_addr subrr pi_ge0.
Qed.

Lemma acosN1 : acos (-1) = (pi : R).
Proof.
have oneB : -1 <= (-1 : R) <= 1 by rewrite lexx ge0_cp ?(ler0n _ 1).
apply: cos_inj; rewrite ?in_itv//= ?pi_ge0 ?lexx //.
  by rewrite acos_ge0 // acos_lepi.
by rewrite acosK ?in_itv//= cospi.
Qed.

Lemma cosKN a : - pi <= a <= 0-> acos (cos a) = - a.
Proof.
move=> Hs.
rewrite -(cosN a) cosK // ?in_itv/=.
by rewrite ler_oppr oppr0 ler_oppl andbC.
Qed.

Lemma sqrD1_cossin (x y : R) :
  x ^+ 2 + y ^+ 2 = 1 -> {a | [/\ - pi < a <= pi & x = cos a /\ y = sin a]}.
Proof.
move=> xE.
pose a1 : R := norm_angle (acos x).
have /andP[a1_gtNpi a1_lepi] : - pi < a1 <= pi.
  by apply: norm_angle_bound (acos x).
have ca1E : cos a1 = x.
  rewrite cos_norm_angle acosK // in_itv /=.
  rewrite -ler_norml -(expr_le1 (_ : 0 < 2)%N) // real_normK ?num_real //.
  by rewrite -xE -[X in X <= _]addr0 ler_add // sqr_ge0.
have y2E :  y ^+ 2 = sin a1 ^+ 2.
  by rewrite -[LHS](addKr (x ^+ 2)) xE addrC -ca1E -sin2cos2.
exists (if sin a1 == y then a1 else -a1).
case: eqP => [->|/eqP sina1Dy]; split => //; first by rewrite a1_gtNpi a1_lepi.
  rewrite ltr_oppl opprK ler_oppl lt_neqAle a1_lepi (ltW a1_gtNpi) ?andbT //.
  apply: contra sina1Dy => /eqP a1E.
  by rewrite eq_sym a1E sinpi -[_ == 0](expf_eq0 _ 2%N) y2E a1E sinpi expr0n.
rewrite cosN sinN; split => //.
by have /eqP:= y2E; rewrite eqf_sqr eq_sym (negPf sina1Dy) => /eqP.
Qed.

End Extra.

