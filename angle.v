Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrfun ssrbool eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp
Require Import bigop ssralg ssrint div ssrnum rat poly closed_field polyrcf.
From mathcomp
Require Import matrix mxalgebra tuple mxpoly zmodp binomial realalg.
From mathcomp
Require Import complex.
From mathcomp
Require Import finset fingroup perm.

Require Import aux.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(************************************************************************************)
(* (addition, scalar multiplication, half-angle)                                    *)
(*     (definitions of cos, sin, tan, acos, asin, and atan, and various properties) *)
(************************************************************************************)

Section angle.
Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable R : rcfType.

Record angle := Angle {
  expi : R[i];
  _ : `| expi | == 1 }.

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

Definition arg (x : R[i]) : angle :=
  insubd angle0 (x / `| x |).

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

Definition pihalf := (arg (0 +i* 1) : angle).

Lemma expi_pihalf : expi pihalf = 'i.
Proof. by rewrite /pihalf argK // normc_def /= expr0n expr1n add0r sqrtr1. Qed.

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

Lemma tan_pihalf : tan pihalf = 0.
Proof. by rewrite /tan sin_pihalf cos_pihalf invr0 mulr0. Qed.

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

Lemma sinDpihalf a : sin (a + pihalf) = cos a.
Proof. by rewrite sinD cos_pihalf mulr0 add0r sin_pihalf mulr1. Qed.

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

Lemma cospi : cos pi = -1.
Proof. by rewrite /cos /pi argK //= normrN normr1. Qed.

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

Lemma sinpi : sin pi = 0.
Proof. by rewrite /sin /pi argK /= ?oppr0 // normrN normr1. Qed.

Lemma tan0 : tan 0 = 0 :> R.
Proof. by rewrite /tan sin0 cos0 mul0r. Qed.

Lemma tanpi : tan pi = 0.
Proof. by rewrite /tan sinpi mul0r. Qed.

Lemma abs_sin a : `| sin a | = Num.sqrt (1 - cos a ^+ 2).
Proof.
apply/eqP; rewrite -(@eqr_expn2 _ 2) //; last by rewrite sqrtr_ge0.
rewrite -normrX ger0_norm; last by rewrite sqr_ge0.
rewrite sqr_sqrtr; last first.
  by rewrite lter_sub_addr add0r -sqr_normr exprn_ilte1 // cos_max.
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

Lemma sin0_inv a : sin a = 0 -> a = 0 \/ a = pi.
Proof.
move=> sa0.
move/eqP : (cos2Dsin2 a).
rewrite {}sa0 expr0n addr0 sqrf_eq1; case/orP => /eqP.
move/cos1_angle0; by auto.
move/cosN1_angle0; by auto.
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
by move/eqP; rewrite addr0 -{1}(@expr1n _ 2%N) -sqr_normr eqr_expn2 // ?ler01 // => /eqP.
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

Lemma angle_in a : a \in Opi_closed \/ a \in piO_closed.
Proof. rewrite 2!inE; case: (lerP 0 (sin a)); by auto. Qed.

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
(*Num.sqrt ((1 + Re x) / 2%:R) -i* Num.sqrt ((1 - Re x) / 2%:R)*)
    - Num.sqrt ((1 + Re x) / 2%:R) +i* Num.sqrt ((1 - Re x) / 2%:R).

Lemma norm_half_anglec (x : R[i]) : `|x| = 1 -> `|half_anglec x| == 1.
Proof.
move=> x1.
rewrite /half_anglec.
case: ifP => a0.
  rewrite normc_def /= sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // Re_half_anglec.
  rewrite sqr_sqrtr; last first.
    by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
  by rewrite mulrC (mulrC (1 - Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatf_unit // sqrtr1.
rewrite normc_def /= sqr_sqrtr; last first.
  (*by rewrite divr_ge0 // ?Re_half_anglec // ler0n.*)
  by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.
rewrite sqrrN sqr_sqrtr; last first.
  (*by rewrite divr_ge0 // ?ler0n // subr_ge0 Im_half_anglec.*)
  by rewrite divr_ge0 // ?ler0n // Re_half_anglec.
by rewrite mulrC (mulrC (1 - Re x)) -mulrDr addrCA addrK -mulr2n mulVr ?pnatf_unit // sqrtr1.
Qed.

Definition half_angle (x : angle) := Angle (norm_half_anglec (normr_expi x)).

Lemma half_angle0 : half_angle 0 = 0.
Proof.
apply val_inj => /=; rewrite /half_anglec; case: ifPn => /=; rewrite expi0 /=.
2: by rewrite lerr.
move=> _; rewrite subrr mul0r sqrtr0 divrr ?unitfE // ?complexr0 ?sqrtr1 //.
by rewrite (_ : 1 + 1 = 2%:R) // pnatr_eq0.
Qed.

Lemma half_anglepi : half_angle pi = pihalf.
Proof.
apply val_inj => /=; rewrite /half_anglec; case: ifPn => /=; rewrite expipi /= oppr0.
2: by rewrite lerr.
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
    by rewrite -(mulr_natl (Re _)) mulrA mulVr ?pnatf_unit // mul1r eqxx.
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

Lemma sin_half_angle a : `| sin (half_angle a) | = Num.sqrt ((1 - cos a) / 2%:R).
Proof.
move: (cosD (half_angle a) (half_angle a)).
rewrite halfP -2!expr2 cos2sin2 -addrA -opprD -mulr2n => /eqP.
rewrite eq_sym subr_eq addrC -subr_eq eq_sym => /eqP/(congr1 (fun x => x / 2%:R)).
rewrite -mulr_natl mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
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
  rewrite sqrtrM; last by rewrite -ler_sub_addl add0r.
  rewrite -mulf_div divrr ?unitfE ?sqrtr_eq0 -?ltrNge ?invr_gt0 ?ltr0Sn // mulr1.
  case/boolP : (cos a == 1) => [/eqP ca1|ca1]; first by rewrite ca1 subrr sqrtr0 2!mul0r.
  rewrite -[LHS]mulr1 -{3}(@divrr _ (Num.sqrt (1 - cos a))); last first.
    by rewrite unitfE sqrtr_eq0 -ltrNge subr_gt0 ltr_neqAle ca1.
  rewrite mulf_div -sqrtrM; last by rewrite subr_ge0.
  rewrite -expr2 -sqrtrM; last by rewrite -ler_sub_addl add0r.
  rewrite (mulrC (1 + cos a)) -subr_sqr expr1n.
  rewrite sqrtr_sqr -sin2cos2 sqrtr_sqr.
  rewrite ger0_norm; last by rewrite subr_ge0.
  rewrite ger0_norm // -(halfP a) sinD mulrC -mulr2n -mulr_natl.
  by rewrite mulr_ge0 // ?ler0n // mulr_ge0.
move: (cos_half_angle a).
rewrite ltr0_norm // => /eqP.
rewrite eqr_oppLR => /eqP ->.
rewrite invrN mulrN sqrtrM; last by rewrite -ler_sub_addl add0r.
rewrite -mulf_div divrr ?unitfE ?sqrtr_eq0 -?ltrNge ?invr_gt0 ?ltr0Sn // mulr1.
case/boolP : (cos a == 1) => [/eqP ca1|ca1]; first by rewrite ca1 subrr sqrtr0 2!mul0r oppr0.
rewrite -[LHS]mulr1 -{3}(@divrr _ (Num.sqrt (1 - cos a))); last first.
  by rewrite unitfE sqrtr_eq0 -ltrNge subr_gt0 ltr_neqAle ca1.
rewrite mulNr mulf_div -sqrtrM; last by rewrite subr_ge0.
rewrite -expr2 -sqrtrM; last by rewrite -ler_sub_addl add0r.
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

Definition cot (a : angle) := (tan a)^-1.

Lemma cot_pihalf : cot pihalf = 0.
Proof. by rewrite /cot tan_pihalf invr0. Qed.

Lemma cot_half_angle a : cot (half_angle a) = sin a / (1 - cos a).
Proof. by rewrite /cot tan_half_angle invf_div. Qed.

Lemma cot_half_angle' a : cot (half_angle a) = (1 + cos a) / sin a.
Proof. by rewrite /cot tan_half_angle' invf_div. Qed.

Definition sec a := (cos a)^-1.

Lemma secpi : sec pi = -1.
Proof. by rewrite /sec cospi invrN invr1. Qed.

End angle.

Arguments pi {R}.