(* coq-robot (c) 2017 AIST and INRIA. License: LGPL-2.1-or-later. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint.
From mathcomp Require Import ssrnum rat poly closed_field polyrcf matrix.
From mathcomp Require Import mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp Require Import complex finset fingroup perm.
Require Import ssr_ext.

(******************************************************************************)
(*                               Angles                                       *)
(*                                                                            *)
(* NB(2022-02-15): The development in this directory now uses trigonometric   *)
(* from mathcomp-analysis instead of the notation of angle provided by this   *)
(* file.                                                                      *)
(*                                                                            *)
(* This files provides a theory of angles defined using complex numbers and   *)
(* develops the theory of trigonometric functions including trigonometric     *)
(* laws such as the cancellation laws between trigonometric functions and     *)
(* their inverse, Pythagorean identity, double-angle and half-angle formulas, *)
(* law of cosines and of sines, etc.                                          *)
(*                                                                            *)
(*      angle T == type of angles over the rcfType T, i.e., a complex number  *)
(*                 whose modulus is 1                                         *)
(*       angle0 == 0 angle corresponding to the complex number 1              *)
(*        arg x == angle corresponding to the complex number x/|x|            *)
(*           pi == the angle corresponding to the complete number -1          *)
(*                                                                            *)
(* Angles form a ZmodType, so that we can do scalar multiplication of angles: *)
(* half_angle a == the angle corresponding to a/2                             *)
(*       pihalf == pi/2                                                       *)
(*    piquarter == pi/4                                                       *)
(*                                                                            *)
(* Trigonometric functions:                                                   *)
(*       cos a == the real part of the angle a                                *)
(*       sin a == the imaginary part of angle a                               *)
(*       tan a == tangent a                                                   *)
(*      acos x == arccosine, the inverse trigonometric function of cosine     *)
(*      asin x == arcsin x                                                    *)
(*      atan x == arctan x                                                    *)
(*   atan2 x y == the 2-argument arctangent, i.e., the angle between the      *)
(*                positive x axis and the ray to the point (x, y)             *)
(*       cot a == cotangent a                                                 *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Section nthroot.

(* TODO: remove? *)
Lemma rootCD (C : numClosedFieldType) (m n : nat) (x : C) :
  (m * n).-root (x) = m.-root (n.-root x).
Proof.
have [->|m_gt0] := posnP m; first by rewrite mul0n !root0C.
have [->|n_gt0] := posnP n; first by rewrite muln0 root0C rootC0.
have mn_gt0: (m * n > 0)%N by rewrite ?muln_gt0 ?m_gt0.
wlog x_gt0 : x / x >= 0 => [hwlog_x_ge0|]; last first.
  apply: (@pexpIrn _ (m * n)) => //; rewrite ?nnegrE//= ?rootC_ge0 //.
  by rewrite rootCK // exprM !rootCK.
wlog nx_eq1 : x / `|x| = 1 => [hwlog_nx_eq1|].
  have [->|x_neq0] := eqVneq x 0; first by rewrite !rootC0.
  rewrite -[x](@mulfVK _ `|x|) ?normr_eq0 // rootCMr //.
  rewrite hwlog_nx_eq1 ?normrM ?normfV ?normr_id ?divff ?normr_eq0 //.
  by rewrite hwlog_x_ge0 //; do !rewrite -rootCMr ?rootC_ge0 //.
 have [|m_gt1] := leqP m 1%N.
   by case: m m_gt0 mn_gt0 hwlog_x_ge0 => [|[|m]] // _ _;
     rewrite mul1n root1C.
 have [|n_gt1] := leqP n 1%N.
   by case: n n_gt0 mn_gt0 hwlog_x_ge0 => [|[|n]] // _ _;
     rewrite muln1 root1C.
 have mDn_gt1: (m * n > 1)%N.
   by rewrite -subn_eq0; move: m n {n_gt0 m_gt0} n_gt1 m_gt1
     mn_gt0 hwlog_x_ge0=> [|[|m]] [|[|n]].
apply: eqC_semipolar => //; first 2 last.
- by rewrite mulr_ge0 ?Im_rootC_ge0.
- by rewrite !norm_rootC hwlog_x_ge0.
apply/eqP; rewrite eq_le !rootC_Re_max ?exprM ?rootCK ?Im_rootC_ge0 //.
apply: eqC_semipolar; first 2 last.
- rewrite mulr_ge0 ?Im_rootC_ge0 //. admit.
- by rewrite normrX !norm_rootC hwlog_x_ge0 // rootCK.
apply/eqP; rewrite eq_le rootC_Re_max -?exprM ?rootCK //=; last first.
  admit.
admit.
Abort.

End nthroot.

Section angle_def.

Variable T : rcfType.

Record angle := Angle {
  expi :> T[i];
  _ : `| expi | == 1 }.

Fact angle0_subproof : `| 1 / `| 1 | | == 1 :> T[i].
Proof. by rewrite normr1 divr1 normr1. Qed.

Definition angle0 := Angle angle0_subproof.

HB.instance Definition _ := [isSub for expi].

Lemma normr_expi a : `|expi a| = 1.
Proof. by case: a => x /= /eqP. Qed.

Lemma expi_eq0 a : (expi a == 0) = false.
Proof. case: a => /= a /eqP Ha; apply/negbTE; by rewrite -normr_gt0 Ha. Qed.

Lemma expi_inj : injective expi.
Proof. move=> [a a1] [b b1] /= ab; by apply/val_inj. Qed.

Lemma expi_is_unit a : expi a \is a GRing.unit.
Proof. by rewrite unitfE -normr_eq0 normr_expi oner_eq0. Qed.

Definition arg (x : T[i]) : angle :=
  insubd angle0 (x / `| x |).

Lemma argZ x (k : T) : 0 < k -> arg (k %:C%C * x) = arg x.
Proof.
move=> k0; rewrite /arg; congr (insubd _ _).
rewrite normrM gtr0_norm; last by rewrite ltcR.
rewrite -mulf_div divff ?mul1r //.
by rewrite lt0r_neq0 // ltcR.
Qed.

Lemma argZ_neg x (k : T) : k < 0 -> arg (k %:C%C * x) = arg (- x).
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

Lemma expi_conjc (a : T[i]) : a != 0 -> (expi (arg a))^-1 = expi (arg a^*).
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

Lemma arg_Re k : 0 < k -> arg k%:C%C = arg 1.
Proof. by move=> k_gt0; rewrite -[(k%:C)%C]mulr1 argZ. Qed.

Lemma arg_Re_neg k : k < 0 -> arg k%:C%C = arg (- 1).
Proof. by move=> k_gt0; rewrite -[(k%:C)%C]mulr1 argZ_neg. Qed.

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

Lemma add_Nangle x : add_angle (opp_angle x) x = arg 1.
Proof.
rewrite /add_angle /opp_angle argK; first by rewrite mulVr // expi_is_unit.
by rewrite normrV ?expi_is_unit // normr_expi invr1.
Qed.

HB.instance Definition _ := [Equality of angle by <:].
HB.instance Definition _ := [Choice of angle by <:].
HB.instance Definition _ :=
  @GRing.isZmodule.Build angle _ opp_angle add_angle add_angleA add_angleC add_0angle add_Nangle.

Lemma arg1 : arg 1 = 0.
Proof. apply val_inj => /=; by rewrite argK // normr1. Qed.

Lemma expiD a b : expi (a + b) = expi a * expi b.
Proof.
move: a b => [a a1] [b b1] /=.
by rewrite /add_angle /= argK // normrM  (eqP a1) (eqP b1) mulr1.
Qed.

Definition pi := arg (-1).

Lemma expipi : expi pi = -1. Proof. by rewrite argK ?normrN1. Qed.

Lemma argN1 : arg (- 1) = pi.
Proof. apply val_inj => /=; by rewrite argK // ?normrN1. Qed.

Lemma expi2pi : expi (pi + pi) = 1.
Proof. by rewrite /pi expiD argK // ?normrN1 // mulrNN mulr1. Qed.

Lemma pi2 : pi *+ 2 = 0.
Proof. apply expi_inj => //; by rewrite expi2pi -arg1 argK // normr1. Qed.

End angle_def.

Arguments expi {T} _.
Arguments angle0 {T}.
Arguments pi {T}.

Section angle_basic_prop.

Variable T : rcfType.
Implicit Types a b : angle T.

Lemma add_angleE a b : a + b = add_angle a b.
Proof. done. Qed.

Lemma opp_angleE a : - a = opp_angle a.
Proof. done. Qed.

Lemma argc (z : T[i]) : z != 0 -> arg z^* = - arg z.
Proof.
case: z => a b z0 /=; by rewrite {2}/arg opp_angleE /opp_angle expi_conjc //= expiK.
Qed.

Definition cos a := complex.Re (expi a).

Lemma cos0 : cos 0 = 1.
Proof. by rewrite /cos -arg1 argK // ger0_norm // ler01. Qed.

Lemma cospi : cos pi = -1.
Proof. by rewrite /cos /pi argK //= normrN normr1. Qed.

Lemma cos_max a : `| cos a | <= 1.
Proof.
rewrite -lecR (le_trans (normc_ge_Re _)) //; by case: a => ? /= /eqP ->.
Qed.

Lemma cosN a : cos (- a) = cos a.
Proof.
case: a => -[a b] ab; rewrite opp_angleE /cos /opp_angle /=.
rewrite invc_norm (eqP ab) expr1n invr1 mul1r expi_arg; last first.
  by rewrite conjc_eq0 -normr_eq0 (eqP ab) oner_eq0.
by rewrite normcJ (eqP ab) divr1.
Qed.

Definition sin a := complex.Im (expi a).

Lemma sin0 : sin 0 = 0.
Proof. by rewrite /sin -arg1 argK // normr1. Qed.

Lemma sinpi : sin pi = 0.
Proof. by rewrite /sin /pi argK /= ?oppr0 // normrN normr1. Qed.

Lemma sinN a : sin (- a) = - sin a.
Proof.
case: a => -[a b] ab; rewrite opp_angleE /sin /opp_angle /=.
rewrite invc_norm (eqP ab) expr1n invr1 mul1r expi_arg; last first.
  by rewrite conjc_eq0 -normr_eq0 (eqP ab) oner_eq0.
by rewrite normcJ (eqP ab) divr1.
Qed.

Lemma eq_angle a b : (a == b) = ((cos a == cos b) && (sin a == sin b)).
Proof.
case: a b => [[a b] ab] [[c d] cd].
rewrite /cos /= /sin /=.
apply/idP/idP; first by case/eqP => -> ->; rewrite 2!eqxx.
case/andP => /eqP ac /eqP bd.
apply/eqP/val_inj => /=; by rewrite ac bd.
Qed.

Lemma sqrD1_cossin (x y : T) :
  x ^+ 2 + y ^+ 2 = 1 -> {a | x = cos a /\ y = sin a}.
Proof.
move=> v1.
have {}v1 : (`| x +i* y | = 1)%C by rewrite normc_def /= v1 sqrtr1.
exists (arg (x +i* y)%C).
rewrite /cos /sin expi_arg //; last by rewrite -normr_eq0 v1 oner_neq0.
by rewrite v1 divr1.
Qed.

(* relation expi<->cos/sin *)

Lemma expi_cos_sin a : expi a = (cos a +i* sin a)%C.
Proof. by case: a => -[a0 a1] Ha; rewrite /cos /sin. Qed.

Lemma expi0 : expi 0 = 1 :> T[i].
Proof. by rewrite expi_cos_sin cos0 sin0. Qed.

Lemma expi_expr k a : expi a ^+ k = expi (a *+ k).
Proof.
elim: k => [|k ih]; by
  [rewrite expr0 mulr0n expi0 | rewrite exprS ih mulrS expiD].
Qed.

Lemma moivre n a : ((cos a +i* sin a) ^+n = cos (a *+ n) +i* sin (a *+ n))%C.
Proof.
rewrite -!expi_cos_sin.
elim: n => [|n ih]; by [rewrite expr0 mulr0n expi0 | rewrite expi_expr].
Qed.

Lemma pi_neq0 : pi != 0 :> angle T.
Proof.
apply/eqP => /(congr1 expi).
rewrite argK ?expi0; last by rewrite normrN normr1.
by move/eqP; rewrite eq_sym -subr_eq0 opprK (_ : 1 + 1 = 2%:R) // pnatr_eq0.
Qed.

Lemma expii : expi (arg 'i) = 'i :> T[i].
Proof. by rewrite argK // normc_def /= expr0n expr1n add0r sqrtr1. Qed.

Lemma expiNi : expi (- arg 'i) = -'i :> T[i].
Proof.
rewrite expi_cos_sin sinN cosN /cos /sin expi_arg; last first.
  by rewrite -normr_eq0 normci oner_neq0.
rewrite normci divr1 /=; apply/eqP; by rewrite eq_complex /= oppr0 2!eqxx.
Qed.

Lemma expiNpi : expi (- pi) = - 1 :> T[i].
Proof.
rewrite /pi.
rewrite expi_cos_sin cosN sinN cospi sinpi.
by apply/eqP; rewrite eq_complex /= !eqxx.
Qed.

Lemma piNpi : pi = - pi :> angle T.
Proof. by apply expi_inj; rewrite expiNpi expipi. Qed.

Lemma arg0_inv (x : T[i]) y : y != 0 -> `|x| = y -> arg x = 0 -> x = y.
Proof.
move=> y0; case: x => x1 x2 norma H.
rewrite -(mulr1 y) -expi0 -H expi_arg; last by rewrite -normr_eq0 norma.
by rewrite norma mulrCA divrr // mulr1.
Qed.

Lemma argpi_inv (x : T[i]) y : y != 0 -> `|x| = y -> arg x = pi -> x = - y.
Proof.
move=> y0; case: x => x1 x2 norma H.
rewrite -(mulrN1 y) -expipi -H expi_arg; last by rewrite -normr_eq0 norma.
by rewrite norma mulrCA divrr // mulr1.
Qed.

(* standard trigonometric relations *)

Lemma cos2Dsin2 a : (cos a) ^+ 2 + (sin a) ^+ 2 = 1.
Proof.
move: (add_Re2_Im2 (expi a)).
by rewrite normr_expi expr1n => /(congr1 (@complex.Re T)) => /= <-.
Qed.

Lemma sin2cos2 a : sin a ^+ 2 = 1 - cos a ^+ 2.
Proof. move/eqP: (cos2Dsin2 a); by rewrite eq_sym addrC -subr_eq => /eqP. Qed.

Lemma cos2sin2 a : cos a ^+ 2 = 1 - sin a ^+ 2.
Proof. move/eqP: (cos2Dsin2 a); by rewrite eq_sym -subr_eq => /eqP. Qed.

Lemma sinD a b : sin (a + b) = sin a * cos b + cos a * sin b.
Proof. by rewrite {1}/sin expiD 2!expi_cos_sin /= addrC. Qed.

Lemma sinDpi a : sin (a + pi) = - sin a.
Proof. by rewrite sinD ?(cosN, sinN) cospi mulrN1 sinpi ?oppr0 mulr0 addr0. Qed.

Lemma sin_mulr2n a : sin (a *+ 2) = (cos a * sin a) *+ 2.
Proof. by rewrite mulr2n sinD mulrC -mulr2n. Qed.

Lemma cosD a b : cos (a + b) = cos a * cos b - sin a * sin b.
Proof. by rewrite {1}/cos expiD 2!expi_cos_sin /= addrC. Qed.

Lemma cosDpi a : cos (a + pi) = - cos a.
Proof. by rewrite cosD ?(cosN, sinN) cospi mulrN1 sinpi ?oppr0 mulr0 subr0. Qed.

Lemma cosB a b : cos (a - b) = cos a * cos b + sin a * sin b.
Proof. by rewrite cosD cosN sinN mulrN opprK. Qed.

Lemma sinB a b : sin (a - b) = sin a * cos b - cos a * sin b.
Proof. by rewrite sinD cosN sinN mulrN. Qed.

Lemma abs_sin a : `| sin a | = Num.sqrt (1 - cos a ^+ 2).
Proof.
apply/eqP; rewrite -(@eqrXn2 _ 2) //; last by rewrite sqrtr_ge0.
rewrite -normrX ger0_norm; last by rewrite sqr_ge0.
rewrite sqr_sqrtr; last first.
  by rewrite lterBDr add0r -sqr_normr exprn_ilte1 // cos_max.
by rewrite -subr_eq opprK addrC cos2Dsin2.
Qed.

(* valeurs remarquables de cos/sin *)

Lemma norm_cos_eq1 a : (`|cos a| == 1) = (sin a == 0).
Proof.
by rewrite -sqrf_eq0 -sqrp_eq1 // sqr_normr sin2cos2 subr_eq0 eq_sym.
Qed.

Lemma norm_sin_eq1 a : (`|sin a| == 1) = (cos a == 0).
Proof.
by rewrite -sqrf_eq0 -sqrp_eq1 // sqr_normr cos2sin2 subr_eq0 eq_sym.
Qed.

Lemma cos1sin0 a : `|cos a| = 1 -> sin a = 0.
Proof. by move/eqP; rewrite norm_cos_eq1 => /eqP. Qed.

Lemma sin1cos0 a : `|sin a| = 1 -> cos a = 0.
Proof. by move/eqP; rewrite norm_sin_eq1 => /eqP. Qed.

Lemma sin0cos1 a : sin a = 0 -> `|cos a| = 1.
Proof. by move/eqP; rewrite -norm_cos_eq1 => /eqP. Qed.

Lemma cos0sin1 a : cos a = 0 -> `|sin a| = 1.
Proof. by move/eqP; rewrite -norm_sin_eq1 => /eqP. Qed.

Lemma cos_eq1 a : (cos a == 1) = (a == 0).
Proof.
apply/eqP/eqP=> [cosa|->]; last by rewrite cos0.
by rewrite -[a]expiK expi_cos_sin cosa cos1sin0 ?arg1 ?cosa ?normr1.
Qed.

Lemma cos1_angle0 a : cos a = 1 -> a = 0.
Proof. by move/eqP; rewrite cos_eq1 => /eqP. Qed.

Lemma cos_eqN1 a : (cos a == -1) = (a == pi).
Proof.
apply/eqP/eqP=> [cosa|->]; last by rewrite cospi.
rewrite -[a]expiK expi_cos_sin cosa cos1sin0 ?complexr0 ?rmorphN ?argN1 //.
by rewrite cosa normrN1.
Qed.

Lemma cosN1_angle0 a : cos a = -1 -> a = pi.
Proof. by move/eqP; rewrite cos_eqN1 => /eqP. Qed.

Lemma sin_eq0 a : (sin a == 0) = (a == 0) || (a == pi).
Proof. by rewrite -sqrf_eq0 sin2cos2 subr_eq0 eq_sym sqrf_eq1 cos_eq1 cos_eqN1. Qed.

Lemma sin0_inv a : sin a = 0 -> {a = 0} + { a = pi }.
Proof. by move/eqP; rewrite sin_eq0; case: eqP => /= ?/eqP?; [left|right]. Qed.

Definition tan a := sin a / cos a.

Lemma tan0 : tan 0 = 0 :> T.
Proof. by rewrite /tan sin0 cos0 mul0r. Qed.

Lemma tanpi : tan pi = 0.
Proof. by rewrite /tan sinpi mul0r. Qed.

Lemma tanN x : tan (- x) = - tan x :> T.
Proof. by rewrite /tan sinN cosN mulNr. Qed.

Lemma cos2_tan2 x : cos x != 0 -> 1 / (cos x) ^+ 2 = 1 + (tan x) ^+ 2.
Proof.
move=> cosx; rewrite /tan exprMn sin2cos2 mulrBl -exprMn divrr ?unitfE //.
by rewrite expr1n addrCA subrr addr0 div1r mul1r exprVn.
Qed.

Definition pihalf : angle T := arg 'i.

Lemma expi_pihalf : expi pihalf = 'i.
Proof. by rewrite /pihalf argK // normc_def /= expr0n expr1n add0r sqrtr1. Qed.

Lemma expi_Npihalf : expi (- pihalf) = - 'i.
Proof. by rewrite /pihalf expiNi. Qed.

Lemma sin_pihalf : sin pihalf = 1.
Proof.
have i1 : `|'i| = 1 :> T[i] by rewrite normc_def /= expr0n add0r expr1n sqrtr1.
rewrite /sin /pihalf expi_arg //.
by rewrite i1 divr1.
by rewrite -normr_eq0 i1 oner_neq0.
Qed.

Lemma cos_pihalf : cos pihalf = 0.
Proof.
have i1 : `|'i| = 1 :> T[i] by rewrite normc_def /= expr0n add0r expr1n sqrtr1.
rewrite /cos /pihalf expi_arg //.
by rewrite i1 divr1.
by rewrite -normr_eq0 i1 oner_neq0.
Qed.

Lemma tan_pihalf : tan pihalf = 0.
Proof. by rewrite /tan sin_pihalf cos_pihalf invr0 mulr0. Qed.

Lemma cosDpihalf a : cos (a + pihalf) = - sin a.
Proof. by rewrite cosD cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma cosBpihalf a : cos (a - pihalf) = sin a.
Proof. by rewrite cosB cos_pihalf sin_pihalf mulr0 add0r mulr1. Qed.

Lemma sinDpihalf a : sin (a + pihalf) = cos a.
Proof. by rewrite sinD cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

Lemma sinBpihalf a : sin (a - pihalf) = - cos a.
Proof. by rewrite sinB cos_pihalf sin_pihalf mulr0 add0r mulr1. Qed.

Lemma cos0_inv a : cos a = 0 -> {a = pihalf} + {a = - pihalf}.
Proof.
case: a => -[a b] ni; rewrite /cos /= => a0.
have [b1|b1] : {b = 1} + {b = - 1}.
  move: ni.
  rewrite a0 normc_def /= expr0n add0r sqrtr_sqr eq_complex /= eqxx andbT.
  case: (lerP 0 b) => b0.
  - rewrite ger0_norm // => /eqP ->; by left.
  - rewrite ltr0_norm // eqr_oppLR => /eqP ->; by right.
- left; apply val_inj => /=;
  by rewrite /pihalf argK // ?a0 ?b1 // normc_def /= expr0n add0r expr1n sqrtr1.
- right; apply val_inj => /=.
  by apply/eqP; rewrite /pihalf a0 b1 expiNi eq_complex /= oppr0 2!eqxx.
Qed.

Definition piquarter : angle T := arg (Num.sqrt (2%:R^-1) +i* Num.sqrt (2%:R^-1))%C.

Lemma expi_piquarter :
  expi piquarter = (Num.sqrt (2%:R^-1) +i* Num.sqrt (2%:R^-1))%C.
Proof.
rewrite /piquarter argK // normc_def /= sqr_sqrtr ?invr_ge0 ?ler0n //.
by rewrite -div1r -mulr2n -mulrnAl divrr ?unitfE ?pnatr_eq0 // sqrtr1.
Qed.

(*
sin(t) = ( exp(it) - exp(-it) )/2i
cos(t) = ( exp(it) + exp(-it) )/2
*)

Definition acos (x : T) : angle T := arg (x +i* Num.sqrt (1 - x ^+ 2))%C.

Lemma acos1 : acos 1 = 0.
Proof. by rewrite /acos expr1n subrr sqrtr0 complexr0 arg1. Qed.

Lemma acosN1 : acos (- 1) = pi.
Proof.
rewrite /acos sqrrN expr1n subrr sqrtr0 complexr0 (_ : ((_)%:C)%C = -1) //.
apply/eqP; by rewrite eq_complex /= oppr0 eqxx eqxx.
Qed.

Definition asin (x : T) : angle T := arg (Num.sqrt (1 - x ^+ 2) +i* x)%C.

Lemma asinN x : asin (- x) = - asin x.
Proof.
rewrite /asin sqrrN -argc //= eq_complex /= negb_and.
case/boolP : (x == 0) => [/eqP ->|]; last by rewrite orbT.
by rewrite expr0n /= subr0 sqrtr1 oner_neq0.
Qed.

Definition atan (x : T) : angle T :=
  if x == 0 then 0 else arg ((x^-1 +i* 1)%C *~ sgz x).

Lemma atan0 : atan 0 = 0.
Proof. by rewrite /atan eqxx. Qed.

Lemma atan1 : atan 1 = piquarter.
Proof.
rewrite /atan oner_eq0 invr1 sgz1 mulr1z.
rewrite -(@argZ _ _ (Num.sqrt 2%:R^-1)) ?sqrtr_gt0 ?invr_gt0 ?ltr0Sn //.
by rewrite -complexZ1 mulr1.
Qed.

Lemma atanN x : atan (- x) = - atan x.
Proof.
rewrite /atan eqr_oppLR oppr0.
case: ifPn => [|x0]; first by rewrite oppr0.
rewrite -argc.
  congr arg; apply/eqP.
  rewrite sgzN mulrNz /= eq_complex /=.
  move: x0; rewrite neq_lt => /orP [] x0.
    by rewrite ltr0_sgz // 2!mulrN1z opprK /= invrN opprK 2!eqxx.
  by rewrite gtr0_sgz // 2!mulr1z /= invrN opprK 2!eqxx.
move: x0; rewrite neq_lt => /orP [] x0.
  rewrite ltr0_sgz // -?oppr_gt0 ?opprK // mulrN1z eq_complex /= negb_and orbC.
  by rewrite eqr_oppLR oppr0 oner_neq0.
by rewrite gtr0_sgz ?oppr_gt0 // mulr1z eq_complex /= negb_and oner_neq0 orbC.
Qed.

Definition atan2 x y :=
  if y > 0 then atan (x / y) else
  if y < 0 then
     (if x >= 0 then atan (x / y) + pi else
        (* x < 0 *) atan (x / y) - pi) else
  (* y == 0 *)
     (if x > 0 then pihalf else
      if x < 0 then - pihalf else
        0) (* undefined *).

Lemma atan200 : atan2 0 0 = 0.
Proof. by rewrite /atan2 ltxx. Qed.

Lemma atan2_11 : atan2 1 1 = piquarter.
Proof. by rewrite /atan2 ltr01 invr1 mulr1 atan1. Qed.

Lemma atan2N (x y : T) : atan2 (- x) y = - atan2 x y.
Proof.
rewrite /atan2; have [y0|y0]:= ltP 0 y; first by rewrite mulNr atanN.
rewrite lt_neqAle y0 andbT; have [y0'|y0'] /= := boolP (y == 0).
  by rewrite oppr_gt0 oppr_lt0; case: ltrgt0P => x0; rewrite ?opprK ?oppr0.
by rewrite oppr_ge0; case: ltrgt0P => x0;
   rewrite mulNr atanN opprD ?opprK // {1}piNpi.
Qed.

(* cancellation laws *)

(* The following lemmas are true in specific domains only, such as
]-pi/2, pi/2[ = [pred a | cos a > 0]
]0, pi[ = [pred a | sin a > 0]
[-pi/2, pi/2[ = [pred a | cos a > 0]
[0, pi] = [pred a | sin a >= 0]
[0, pi[ = [pred a | sin a >= 0 && a != pi]
*)

Definition Opi_closed := [pred a | 0 <= sin a].
Definition piO_closed := [pred a | sin a < 0].

Lemma angle_in a : a \in Opi_closed \/ a \in piO_closed.
Proof. rewrite 2!inE; case: (lerP 0 (sin a)); by auto. Qed.

(* ]-pi/2, pi/2[ *)
Definition Npi2pi2_open : pred (angle T) := [pred a | cos a > 0].
Definition Npi2pi2_closed : pred (angle T) := [pred a | cos a >= 0].
Lemma Npi2pi2_openP a : (a \in Npi2pi2_open) = (0 < cos a).
Proof. by rewrite inE. Qed.

Lemma acosK (r : T) : -1 <= r <= 1 -> cos (acos r) = r.
Proof.
move=> rdom; rewrite /acos /cos argK // normc_def /= sqr_sqrtr; last first.
  by rewrite subr_ge0 -ler_sqrt // ?ltr01 // sqrtr1 sqrtr_sqr ler_norml.
by rewrite addrC subrK sqrtr1.
Qed.

Lemma tanK a : a \in Npi2pi2_open -> atan (tan a) = a.
Proof.
rewrite inE => adoml; rewrite /atan /tan mulf_eq0.
have [|saNZ] /= := boolP (sin a == 0).
  rewrite sin_eq0 => /orP[] /eqP aE //.
  by rewrite aE cospi // -subr_lt0 opprK add0r (ltr_nat _ 1 0) in adoml.
rewrite invr_eq0.
move: (adoml); rewrite lt0r => /andP[/negPf-> _].
have -> : ((sin a / cos a)^-1 +i* 1 = (sin a)^-1%:C * (cos a +i* sin a))%C.
  by rewrite invf_div -complexZ mulVf // mulrC.
rewrite sgzM; case: (sgzP (sin a)) saNZ => //= saP _.
  by rewrite mul1r gtr0_sgz ?invr_gt0 // argZ ?invr_gt0 // -expi_cos_sin expiK.
rewrite mulN1r gtr0_sgz ?invr_gt0 // mulrN1z -!mulrN.
by rewrite argZ_neg ?invr_lt0 // opprK -expi_cos_sin expiK.
Qed.

Lemma tanDpi a : tan (a + pi) = tan a.
Proof. by rewrite /tan sinDpi cosDpi mulNr invrN mulrN opprK. Qed.

Lemma tanK_closed a : a \notin Npi2pi2_closed -> atan (tan a) = a + pi.
Proof.
rewrite inE => adoml.
rewrite -{1}[a]addr0 -pi2 mulr2n addrA tanDpi tanK // inE cosDpi.
by rewrite oppr_cp0 ltNge.
Qed.

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

Lemma sinK (x : angle T) : 0 <= cos x (* TODO: define Npi2pi2_closed? *) ->
  asin (sin x) = x.
Proof.
case: x => /= -[x y] x1 cosx1; apply/val_inj/eqP => /=.
rewrite eq_complex /asin /sin argK /= ?eqxx ?andbT; last first.
  rewrite {cosx1}.
  rewrite normc_def /= sqr_sqrtr ?subrK ?sqrtr1 // subr_ge0.
  move: x1; rewrite normc_def eq_complex eqxx andbT /=.
  move/eqP/(congr1 (fun x => x^+2)); rewrite expr1n.
  rewrite sqr_sqrtr ?addr_ge0 // ?sqr_ge0 // => <-.
  by rewrite lerDr // sqr_ge0.
rewrite /cos /= in cosx1.
move : x1; rewrite normc_def /= eq_complex /= eqxx andbT.
move/eqP/(congr1 (fun x => x^+2)); rewrite expr1n.
rewrite  sqr_sqrtr // ?addr_ge0 // ?sqr_ge0 // => <-.
by rewrite addrK sqrtr_sqr ger0_norm.
Qed.

Lemma asinK r : -1 <= r <= 1 -> sin (asin r) = r.
Proof.
move=> rdom; rewrite /sin /asin argK // normc_def /= sqr_sqrtr; last first.
  by rewrite subr_ge0 -ler_sqrt // ?ltr01 // sqrtr1 sqrtr_sqr ler_norml.
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
      move/lt_total : x0 => /orP [] x0; last by rewrite gtr0_sgz //= invr_gt0.
      by rewrite ltr0_sgz //= ltrNr oppr0 invr_lt0.
    abstract: myltr0.
    rewrite -ltcR -normc_def normr_gt0 eq_complex /= negb_and.
    move/lt_total : x0 => /orP [] x0; last by rewrite gtr0_sgz //= invr_eq0 gt_eqF.
    by rewrite ltr0_sgz //= eqr_oppLR oppr0 invr_eq0 lt_eqF.
  by rewrite gt_eqF.
by rewrite eq_complex /= negb_and gt_eqF.
Qed.

Lemma atanKpos x : 0 < x -> tan (atan x) = x.
Proof.
move=> x0; rewrite /atan gt_eqF // gtr0_sgz // mulr1z /tan /sin /cos.
rewrite expi_arg /=; last by rewrite eq_complex /= negb_and oner_neq0 orbT.
rewrite mul0r oppr0 mulr0 add0r mulr0 subr0 expr0n addr0 expr1n.
rewrite sqr_sqrtr; last by rewrite addr_ge0 // ?ler01 // sqr_ge0.
set y := Num.sqrt _ / _; move=> [:yunit].
rewrite mul1r invrM; last 2 first.
  by rewrite unitrV unitfE gt_eqF.
  abstract: yunit.
  rewrite unitfE /y mulf_eq0 negb_or sqrtr_eq0 -ltNge invr_eq0.
  move=> [:x2D1]; apply/andP; split.
    abstract: x2D1.
    by rewrite addr_gt0 // ?ltr01 // exprn_even_gt0 //= invr_eq0 gt_eqF.
  by rewrite gt_eqF.
by rewrite mulrA divrr // invrK mul1r.
Qed.

Lemma atanKneg x : x < 0 -> tan (atan x) = x.
Proof.
rewrite -oppr_gt0 => x0; rewrite /atan lt_eqF -?oppr_gt0 //.
move/eqP: (atanKpos x0); rewrite -eqr_oppLR => /eqP H.
by rewrite -{3}H {H} atanN tanN opprK /atan lt_eqF // -oppr_gt0.
Qed.

Lemma atanK x : tan (atan x) = x.
Proof.
case: (lerP 0 x); last by apply atanKneg.
rewrite le_eqVlt => /orP [/eqP <-|]; by [rewrite atan0 tan0 | apply atanKpos].
Qed.

Lemma sqr_sin_atan (x : T) : (sin (atan x)) ^+ 2 = x ^+ 2 / (1 + x ^+ 2).
Proof.
case/boolP : (x == 0) => [/eqP ->|x0].
  by rewrite atan0 sin0 expr0n /= mul0r.
rewrite sin2cos2.
apply/eqP; rewrite -eqr_opp opprB subr_eq; apply/eqP.
rewrite -mulNr.
have /divrr H : 1 + x ^+ 2 \in GRing.unit.
  by rewrite unitfE gt_eqF // -(addr0 0) ltr_leD // ?ltr01 // sqr_ge0.
rewrite -{2}H {H} addrC mulNr -mulrBl -invf_div -[LHS]invrK; congr (_ ^-1).
rewrite -exprVn -div1r expr_div_n expr1n cos2_tan2.
  by rewrite atanK addrK divr1.
by rewrite gt_eqF // -Npi2pi2_openP atan_in.
Qed.

Lemma sin_atan_ltr0 (x : T) : x < 0 -> sin (atan x) < 0.
Proof.
move=> x0.
rewrite /sin /atan lt_eqF // ltr0_sgz // mulrN1z /= expi_arg //=.
  rewrite expr0n addr0 mul0r oppr0 mulr0 add0r.
  rewrite sqr_sqrtr; last by rewrite addr_ge0 // sqr_ge0.
  rewrite pmulr_llt0; first by rewrite oppr_lt0 ltr01.
  rewrite (sqrrN 1) expr1n divr_gt0 //.
    rewrite sqrtr_gt0 addr_gt0 // ?ltr01 //.
    by rewrite exprn_gt0 // oppr_gt0 invr_lt0.
  by rewrite addr_gt0 // ?ltr01 // exprn_gt0 // oppr_gt0 invr_lt0.
by rewrite eq_complex /= negb_and /= orbC eqr_oppLR oppr0 oner_eq0.
Qed.

Lemma sin_atan_gtr0 (x : T) : 0 < x -> 0 < sin (atan x).
Proof.
move=> x0.
by rewrite -(opprK (sin _)) -sinN -atanN -oppr_lt0 opprK sin_atan_ltr0 // oppr_lt0.
Qed.

Lemma sin_atan (x : T) : sin (atan x) = x / Num.sqrt (1 + x ^+ 2).
Proof.
apply/eqP.
case/boolP : (x == 0) => [/eqP ->|].
  by rewrite atan0 sin0 mul0r.
move/lt_total => /orP [] x0.
  rewrite -eqr_opp -(@eqrXn2 _ 2) //; last 2 first.
    move/sin_atan_ltr0 : x0; by rewrite oppr_ge0 => /ltW.
    by rewrite -mulNr divr_ge0 // ?sqrtr_ge0 // oppr_ge0 ltW.
  by rewrite 2!sqrrN sqr_sin_atan exprMn exprVn sqr_sqrtr // addr_ge0 // ?ler01 // sqr_ge0.
rewrite -(@eqrXn2 _ 2) //; last 2 first.
  by rewrite ltW // sin_atan_gtr0.
  by rewrite mulr_ge0 // ?invr_ge0 ?sqrtr_ge0 // ltW.
by rewrite sqr_sin_atan exprMn exprVn sqr_sqrtr // addr_ge0 // ?ler01 // sqr_ge0.
Qed.

Lemma sin_acos x : `|x| <= 1 -> sin (acos x) = Num.sqrt (1 - x ^+ 2).
Proof.
move=> Nx_le1; rewrite /sin /acos argK //; simpc; rewrite sqr_sqrtr.
  by rewrite addrC addrNK sqrtr1.
by rewrite subr_ge0 -[_ ^+ _]real_normK ?num_real // exprn_ile1.
Qed.

Lemma cos_asin (x : T) : `| x | < 1 -> cos (asin x) = Num.sqrt (1 - x ^+ 2).
Proof.
move=> x1.
rewrite /asin /cos argK // normc_def /= sqr_sqrtr ?subr_ge0 ?subrK ?sqrtr1 //.
by rewrite -sqr_normr expr_le1 // ltW.
Qed.

Lemma cos_atan x : cos (atan x) = 1 / Num.sqrt (1 + x ^+ 2).
Proof.
move: (atan_in x); rewrite Npi2pi2_openP lt_neqAle => /andP [H1 H2].
move: (H1); rewrite eq_sym; move/cos2_tan2.
rewrite atanK => <-.
rewrite sqrtrM ?ler01 // sqrtr1 2!mul1r.
rewrite -exprVn sqrtr_sqr ger0_norm; by [rewrite invrK | rewrite invr_ge0].
Qed.

End angle_basic_prop.

Section half_angle.

Variable T : rcfType.

Definition half_anglec (x : T[i]) :=
  (if 0 <= complex.Im x then
    Num.sqrt ((1 + complex.Re x) / 2%:R) +i* Num.sqrt ((1 - complex.Re x) / 2%:R)
  else
    - Num.sqrt ((1 + complex.Re x) / 2%:R) +i* Num.sqrt ((1 - complex.Re x) / 2%:R))%C.

Lemma Re_half_anglec (x : T[i]) : `|x| = 1 -> 0 <= 1 + complex.Re x.
Proof.
move=> x1; rewrite -lerBlDr add0r.
suff : `| complex.Re x |%:C%C <= `|x|; last by rewrite normc_ge_Re.
rewrite x1 -lecR; apply: le_trans; by rewrite lecR ler_normr lexx orbT.
Qed.

Lemma Im_half_anglec (x : T[i]) : `|x| = 1 -> complex.Re x <= 1.
Proof.
move=> x1; suff : `| complex.Re x |%:C%C <= `|x|; last by rewrite normc_ge_Re.
rewrite x1 -lecR; apply: le_trans; by rewrite lecR ler_normr lexx.
Qed.

Lemma norm_half_anglec (x : T[i]) : `|x| = 1 -> `|half_anglec x| == 1.
Proof.
move=> x1.
rewrite /half_anglec.
case: ifP => a0.
  rewrite normc_def /= sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // Re_half_anglec.
  rewrite sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
  by rewrite mulrC (mulrC (1 - complex.Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatf_unit // sqrtr1.
rewrite normc_def /= sqr_sqrtr; last first.
  by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
rewrite sqrrN sqr_sqrtr; last first.
  by rewrite divr_ge0 // ?ler0n // Re_half_anglec.
by rewrite mulrC (mulrC (1 - complex.Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatf_unit // sqrtr1.
Qed.

Definition half_angle (x : angle T) := Angle (norm_half_anglec (normr_expi x)).

Lemma half_angle0 : half_angle 0 = 0.
Proof.
apply val_inj => /=; rewrite /half_anglec; case: ifPn => /=; rewrite expi0 /=.
2: by rewrite lexx.
move=> _; rewrite subrr mul0r sqrtr0 divrr ?unitfE // ?complexr0 ?sqrtr1 //.
by rewrite (_ : 1 + 1 = 2%:R) // pnatr_eq0.
Qed.

Lemma half_anglepi : half_angle pi = pihalf T.
Proof.
apply val_inj => /=; rewrite /half_anglec; case: ifPn => /=; rewrite expipi /= oppr0.
2: by rewrite lexx.
move=> _; rewrite subrr mul0r sqrtr0 opprK expi_pihalf.
rewrite (_ : 1 + 1 = 2%:R) // ?pnatr_eq0 divrr ?unitfE ?pnatr_eq0 //.
by rewrite sqrtr1.
Qed.

Lemma sin_half_angle_ge0 a : 0 <= sin (half_angle a).
Proof.
case: a => -[a b] /= ab.
rewrite /sin /= /half_anglec /=; case: ifPn => b0 /=; by rewrite sqrtr_ge0.
Qed.

Lemma halfP a : half_angle a + half_angle a = a.
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
    by rewrite -(mulr_natl (complex.Re _)) mulrA mulVr ?pnatf_unit // mul1r eqxx.
  rewrite mulNr mulrN opprK; exact: tmp.
rewrite /sin /= add_angleE /add_angle /half_angle /= argK; last first.
  by rewrite normrM (eqP (norm_half_anglec (normr_expi _))) mulr1.
rewrite /half_anglec. simpc. rewrite /=.
case: ifPn => a0 /=.
  rewrite mulrC -mulr2n.
  rewrite (@sqrtrM _ (1 - complex.Re a)); last by rewrite subr_ge0 Im_half_anglec // normr_expi.
  rewrite (@sqrtrM _ (1 + complex.Re a)); last by rewrite Re_half_anglec // normr_expi.
  rewrite mulrCA -mulrA -(sqrtrM 2^-1) ?invr_ge0//.
  rewrite -expr2 sqrtr_sqr normfV ger0_norm// -mulr_natr -2!mulrA mulVf ?pnatr_eq0// mulr1.
  rewrite mulrC -sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
  rewrite -subr_sqr expr1n.
  rewrite -(@eqrXn2 _ 2%N) //; last by rewrite sqrtr_ge0.
  by rewrite -sin2cos2 sqr_sqrtr // sqr_ge0.
rewrite mulrN mulNr -opprD eqr_oppLR.
rewrite mulrC -mulr2n.
rewrite (@sqrtrM _ (1 - complex.Re a)); last by rewrite subr_ge0 Im_half_anglec // normr_expi.
rewrite (@sqrtrM _ (1 + complex.Re a)); last by rewrite Re_half_anglec // normr_expi.
rewrite mulrAC -2!mulrA -sqrtrM ?invr_ge0//.
rewrite -expr2 sqrtr_sqr normfV ger0_norm// mulrA -[eqbLHS]mulr_natr -!mulrA mulVf ?pnatr_eq0// mulr1.
rewrite -sqrtrM; last by rewrite subr_ge0 Im_half_anglec // normr_expi.
rewrite -subr_sqr expr1n.
rewrite -(@eqrXn2 _ 2%N) //; last 2 first.
  by rewrite sqrtr_ge0.
  by rewrite ltW // oppr_gt0 ltNge.
by rewrite -sin2cos2 sqrrN sqr_sqrtr // sqr_ge0.
Qed.

Lemma pihalf_is_half : pihalf _ = half_angle pi.
Proof.
rewrite /half_angle; apply val_inj => /=.
rewrite /half_anglec expipi /= oppr0 lexx subrr mul0r sqrtr0 opprK.
by rewrite -(@natrD _ 1 1) divrr ?unitfE ?pnatr_eq0 // sqrtr1 expi_pihalf.
Qed.

Lemma pi_pihalf : pi = pihalf T *+ 2.
Proof. by rewrite -[LHS]halfP pihalf_is_half -mulr2n. Qed.

Lemma piquarter_is_half : piquarter _ = half_angle (pihalf _).
Proof.
rewrite /half_angle; apply val_inj => /=.
by rewrite /half_anglec expi_pihalf /= ler01 addr0 subr0 div1r expi_piquarter.
Qed.

Lemma pi_piquarter : pi = piquarter T *+ 4.
Proof.
rewrite (mulrnA _ 2 2) -[LHS]halfP -mulr2n; congr (_ *+ 2).
by rewrite piquarter_is_half mulr2n halfP pihalf_is_half.
Qed.

Lemma sin_half_angle a : `| sin (half_angle a) | = Num.sqrt ((1 - cos a) / 2%:R).
Proof.
move: (cosD (half_angle a) (half_angle a)).
rewrite halfP -2!expr2 cos2sin2 -addrA -opprD -mulr2n => /eqP.
rewrite eq_sym subr_eq addrC -subr_eq eq_sym => /eqP/(congr1 (fun x => x / 2%:R)).
rewrite -(mulr_natl (sin _ ^+ _)) mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
by move/(congr1 Num.sqrt); rewrite sqrtr_sqr.
Qed.

Lemma cos_half_angle a : `| cos (half_angle a) | = Num.sqrt ((1 + cos a) / 2%:R).
Proof.
move: (cosD (half_angle a) (half_angle a)).
rewrite halfP -2!expr2 sin2cos2 opprB addrA -mulr2n => /eqP.
rewrite eq_sym subr_eq addrC => /eqP/(congr1 (fun x => x / 2%:R)).
rewrite -mulr_natl mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
by move/(congr1 Num.sqrt); rewrite sqrtr_sqr.
Qed.

Lemma tan_half_angle a : tan (half_angle a) = (1 - cos a) / sin a.
Proof.
rewrite /tan.
move: (sin_half_angle a) => H1.
move: (cos_half_angle a) => H2.
have H3 : cos a <= 1 by move: (@ler_norml _ (cos a) 1); rewrite cos_max => /esym/andP[].
have H4 : -1 <= cos a by move: (@ler_norml _ (cos a) 1); rewrite cos_max => /esym/andP[].
move: (sin_half_angle_ge0 a) => sa0.
move: H1; rewrite ger0_norm // => ->.
rewrite sqrtrM; last by rewrite subr_ge0.
case: (lerP 0 (cos (half_angle a))) => ca0.
  move: H2; rewrite ger0_norm // => ->.
  rewrite sqrtrM; last by rewrite -lerBDl add0r.
  rewrite -mulf_div divrr ?unitfE ?sqrtr_eq0 -?ltNge ?invr_gt0 ?ltr0Sn // mulr1.
  case/boolP : (cos a == 1) => [/eqP ca1|ca1]; first by rewrite ca1 subrr sqrtr0 2!mul0r.
  rewrite -[LHS]mulr1 -{3}(@divrr _ (Num.sqrt (1 - cos a))); last first.
    by rewrite unitfE sqrtr_eq0 -ltNge subr_gt0 lt_neqAle ca1.
  rewrite mulf_div -sqrtrM; last by rewrite subr_ge0.
  rewrite -expr2 -sqrtrM; last by rewrite -lerBDl add0r.
  rewrite (mulrC (1 + cos a)) -subr_sqr expr1n.
  rewrite sqrtr_sqr -sin2cos2 sqrtr_sqr.
  rewrite ger0_norm; last by rewrite subr_ge0.
  rewrite ger0_norm // -(halfP a) sinD mulrC -mulr2n -mulr_natl.
  by rewrite mulr_ge0 // ?ler0n // mulr_ge0.
move: (cos_half_angle a).
rewrite ltr0_norm // => /eqP.
rewrite eqr_oppLR => /eqP ->.
rewrite invrN mulrN sqrtrM; last by rewrite -lerBDl add0r.
rewrite -mulf_div divrr ?unitfE ?sqrtr_eq0 -?ltNge ?invr_gt0 ?ltr0Sn // mulr1.
case/boolP : (cos a == 1) => [/eqP ca1|ca1]; first by rewrite ca1 subrr sqrtr0 2!mul0r oppr0.
rewrite -[LHS]mulr1 -{3}(@divrr _ (Num.sqrt (1 - cos a))); last first.
  by rewrite unitfE sqrtr_eq0 -ltNge subr_gt0 lt_neqAle ca1.
rewrite mulNr mulf_div -sqrtrM; last by rewrite subr_ge0.
rewrite -expr2 -sqrtrM; last by rewrite -lerBDl add0r.
rewrite (mulrC (1 + cos a)) -subr_sqr expr1n.
rewrite sqrtr_sqr -sin2cos2 sqrtr_sqr.
rewrite ger0_norm; last by rewrite subr_ge0.
rewrite ler0_norm //; last first.
  by rewrite -(halfP a) sinD mulrC -mulr2n -mulr_natl pmulr_rle0 ?ltr0n // nmulr_rle0.
by rewrite invrN mulrN opprK.
Qed.

Lemma tan_half_angle' a : tan (half_angle a) = sin a / (1 + cos a).
Proof.
case/boolP : (cos a == 1) => [/eqP /cos1_angle0 ->|ca1].
  by rewrite sin0 mul0r /tan half_angle0 sin0 mul0r.
case/boolP : (a == pi) => [/eqP|] api.
  by rewrite api sinpi mul0r half_anglepi tan_pihalf.
rewrite -[RHS]mulr1 -{2}(@divrr _ (1 - cos a)); last by rewrite unitfE subr_eq0 eq_sym.
rewrite mulf_div (mulrC (1 + cos a)) -subr_sqr expr1n -sin2cos2 expr2.
rewrite -mulf_div divrr ?mul1r ?tan_half_angle //.
rewrite unitfE.
apply: contra ca1 => /eqP/sin0_inv[->|/eqP]; first by rewrite cos0.
by rewrite (negbTE api).
Qed.

End half_angle.

Lemma atan2_N1N1 (T : rcfType) : atan2 (- 1) (- 1) = - piquarter T *+ 3.
Proof.
rewrite /atan2 ltr0N1 ltrN10 ler0N1 divrr; last first.
  by rewrite unitfE eqr_oppLR oppr0 oner_neq0.
rewrite atan1 pi_piquarter -opprB -{2}(mulr1n (piquarter T)).
by rewrite -mulrnBr // mulNrn.
Qed.

Section properties_of_atan2.

Variables (T : rcfType).

Lemma sqrtr_sqrN2 (x : T) : x != 0 -> Num.sqrt (x ^- 2) = `|x|^-1.
Proof.
move=> x0.
apply (@mulrI _ `|x|); first by rewrite unitfE normr_eq0.
rewrite -{1}(sqrtr_sqr x) -sqrtrM ?sqr_ge0 // divrr; last by rewrite unitfE normr_eq0.
by rewrite divrr ?sqrtr1 // unitfE sqrf_eq0.
Qed.

Lemma sqrtr_1sqr2 (x y : T) : Num.sqrt (x ^+ 2 + y ^+ 2) = 1 -> x != 0 ->
  Num.sqrt (1 + (y / x) ^+ 2) = `|x|^-1.
Proof.
move=> u1 k0.
rewrite exprMn exprVn -(@divrr _ (x ^+ 2)) ?unitfE ?sqrf_eq0 //.
by rewrite -mulrDl sqrtrM ?u1 ?mul1r ?sqrtr_sqrN2 // addr_ge0// sqr_ge0.
Qed.

Lemma N1x2_gt0 (x : T) : `| x | < 1 -> 0 < 1 - x ^+ 2.
Proof. move=> x1; by rewrite subr_gt0 -sqr_normr expr_lt1. Qed.

Definition yarc (x : T) := Num.sqrt (1 - x ^+ 2).

Lemma yarc0 : yarc 0 = 1.
Proof. by rewrite /yarc expr0n subr0 sqrtr1. Qed.

Lemma yarc1 x : `| x | = 1 -> yarc x = 0.
Proof. by move/eqP; rewrite -sqr_norm_eq1 /yarc => /eqP ->; rewrite subrr sqrtr0. Qed.

Lemma yarc_neq0 (x : T) : `| x | < 1 -> yarc x != 0.
Proof. by move=> x1; rewrite sqrtr_eq0 -ltNge N1x2_gt0. Qed.

Lemma yarc_gt0 (x : T) : `| x | < 1 -> 0 < yarc x.
Proof. by move=> x1; rewrite lt_neqAle sqrtr_ge0 andbT eq_sym yarc_neq0. Qed.

Lemma sqr_yarc (x : T) : `| x | < 1 -> (yarc x) ^+ 2 = 1 - x ^+ 2.
Proof. move=> x1; by rewrite /yarc sqr_sqrtr // ltW // N1x2_gt0. Qed.

Lemma yarc_sin (x : angle T) : yarc (sin x) = `| cos x |.
Proof. by rewrite /yarc -cos2sin2 sqrtr_sqr. Qed.

Lemma inv_yarc (x : T) : `| x | < 1 -> (yarc x)^-1 = Num.sqrt (1 - x ^+ 2)^-1.
Proof.
move=> x1.
apply (@mulrI _ (yarc x)); first by rewrite unitfE yarc_neq0.
rewrite divrr; last by rewrite unitfE yarc_neq0.
rewrite -sqrtrM; last by rewrite ltW // N1x2_gt0.
by rewrite divrr ?sqrtr1 // unitfE gt_eqF // N1x2_gt0.
Qed.

Lemma inv_yarc_gt0 (x : T) : `| x | < 1 -> 0 < (yarc x)^-1.
Proof. move=> x1; by rewrite inv_yarc // sqrtr_gt0 invr_gt0 N1x2_gt0. Qed.

Lemma atan2_x_gt0E (x y : T) : y > 0 -> atan2 x y = atan (x / y).
Proof. move=> y0; by rewrite /atan2 y0. Qed.

Lemma atan2_ge0_lt0E (x y : T) : x >= 0 -> y < 0 -> atan2 x y = atan (x / y) + pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltNge ltW. Qed.

Lemma atan2_lt0_lt0E (x y : T) : x < 0 -> y < 0 -> atan2 x y = atan (x / y) - pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltNge ltW //= leNgt x0. Qed.

Lemma atan2_gt0_0E (x : T) : x > 0 -> atan2 x 0 = pihalf _.
Proof. by move=> x0; rewrite /atan2 x0 ltxx. Qed.

Lemma atan2_lt0_0E (x : T) : x < 0 -> atan2 x 0 = - pihalf _.
Proof. move=> x0; by rewrite /atan2 ltxx ltNge ltW //= x0. Qed.

Lemma cos_atan2 (x y : T) : y != 0 -> cos (atan2 x y) = y / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neq_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // cosDpi ?eqxx // cos_atan mul1r expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 lt_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?lt_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltNge ltr_pwDl // ?sqr_ge0 // exprn_even_gt0 // orbC lt_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 lt_eqF.
    by rewrite !invrN invrK mulNr opprK.
  rewrite atan2_lt0_lt0E // -piNpi cosDpi ?eqxx ?orbT // cos_atan mul1r expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // cos_atan mul1r.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gt_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gt_eqF // gtr0_norm // invrM ?invrK //.
by rewrite unitfE sqrtr_eq0 -ltNge ltr_pwDl // ?sqr_ge0 // exprn_gt0.
by rewrite unitfE invr_neq0 // gt_eqF.
Qed.

Lemma cos_atan2_xyarc (x : T) : `| x | < 1 -> cos (atan2 (- x) (yarc x)) = yarc x.
Proof.
move=> x1; by rewrite cos_atan2 ?yarc_neq0 // sqr_yarc // sqrrN subrK sqrtr1 divr1.
Qed.

Lemma cos_atan2_yarcx (x : T) : `| x | < 1 -> cos (atan2 (yarc x) x) = x.
Proof.
move=> x1.
have [/eqP x0|x0] := boolP (x == 0).
  rewrite x0 yarc0.
  by rewrite /atan2 ltxx ltr01 cos_pihalf.
rewrite cos_atan2 //.
by rewrite sqr_yarc // addrCA subrr addr0 sqrtr1 divr1.
Qed.

Lemma sin_atan2 (x y : T) : y != 0 -> sin (atan2 x y) = x / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neq_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // sinDpi ?eqxx // sin_atan expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 lt_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?lt_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltNge ltr_wpDr // ?sqr_ge0 // exprn_even_gt0 // orbC lt_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 lt_eqF.
    rewrite !invrN invrK mulNr mulrN opprK -mulrA (mulrA _^-1) mulVr ?mul1r //.
    by rewrite unitfE lt_eqF.
  rewrite atan2_lt0_lt0E // -piNpi sinDpi ?eqxx ?orbT // sin_atan expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // sin_atan.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gt_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gt_eqF // gtr0_norm // invrM; last 2 first.
  by rewrite unitfE sqrtr_eq0 -ltNge ltr_wpDr // ?sqr_ge0 // exprn_gt0.
  by rewrite unitfE invr_neq0 // gt_eqF.
rewrite invrK -(mulrA x) (mulrA _^-1) mulVr ?mul1r //.
by rewrite unitfE gt_eqF.
Qed.

Lemma sin_atan20x (x : T) : sin (atan2 0 x) = 0.
Proof.
have [/eqP ->|x0] := boolP (x == 0); first by rewrite atan200 sin0.
by rewrite sin_atan2 // mul0r.
Qed.

Lemma sin_atan2_0 (x : T) : sin (atan2 x 0) = Num.sg x.
Proof.
rewrite /atan2 ltxx; case: ifPn => [x0|]; first by rewrite sin_pihalf gtr0_sg.
rewrite -leNgt le_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltxx sin0 sgr0.
by rewrite x0 sinN sin_pihalf ltr0_sg.
Qed.

Lemma sin_atan2_xyarc (x : T) : `| x | < 1 -> sin (atan2 x (yarc x)) = x.
Proof.
move=> x1; by rewrite sin_atan2 ?yarc_neq0 // sqr_yarc // subrK sqrtr1 divr1.
Qed.

Lemma sin_atan2_yarcx (x : T) : `| x | < 1 -> sin (atan2 (yarc x) x) = yarc x.
Proof.
move=> x1.
have [/eqP x0|x0] := boolP (x == 0).
  rewrite x0 yarc0.
  by rewrite /atan2 ltxx ltr01 sin_pihalf.
rewrite sin_atan2 //.
by rewrite sqr_yarc // addrCA subrr addr0 sqrtr1 divr1.
Qed.

Lemma cos_atan2_0 (x : T) : cos (atan2 x 0) = (x == 0)%:R.
Proof.
rewrite /atan2 ltxx; case: ifPn => [x0|]; first by rewrite cos_pihalf gt_eqF.
rewrite -leNgt le_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltxx cos0 eqxx.
by rewrite x0 cosN cos_pihalf lt_eqF.
Qed.

End properties_of_atan2.

Section derived_trigonometric_functions.

Variable T : rcfType.
Implicit Types a : angle T.

Definition cot a := (tan a)^-1.

Lemma cot_pihalf : cot (pihalf T) = 0.
Proof. by rewrite /cot tan_pihalf invr0. Qed.

Lemma cot_half_angle a : cot (half_angle a) = sin a / (1 - cos a).
Proof. by rewrite /cot tan_half_angle invf_div. Qed.

Lemma cot_half_angle' a : cot (half_angle a) = (1 + cos a) / sin a.
Proof. by rewrite /cot tan_half_angle' invf_div. Qed.

Definition sec a := (cos a)^-1.

Lemma secpi : sec pi = -1.
Proof. by rewrite /sec cospi invrN invr1. Qed.

End derived_trigonometric_functions.
