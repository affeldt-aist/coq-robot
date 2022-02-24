From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import interval reals trigo.
Require Import ssr_ext.

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

Lemma sin_eq0_Npipi a :
  - pi < a <= pi -> (sin a == 0) = ((a == 0) || (a == pi)).
Proof.
move=> /andP[a_gtNpi a_lepi].
have [->|/eqP aD0 /=] := a =P 0; first by rewrite sin0 eqxx.
have [->|/eqP aDpi /=] := a =P pi; first by rewrite sinpi eqxx.
case: ltgtP aD0 => //= aL _.
  suff: sin a < 0 by case: ltgtP.
  rewrite -[X in X < _]opprK -sinN oppr_cp0 sin_gt0_pi //.
  by rewrite oppr_cp0 aL ltr_oppl a_gtNpi.
suff: 0 < sin a by case: ltgtP.
by rewrite sin_gt0_pi // aL lt_neqAle aDpi.
Qed.

Lemma cos_eq0_Npipi a :
  - pi < a <= pi -> (cos a == 0) = ((a == pi / 2%:R) || (a == - (pi / 2%:R))).
Proof.
move=> /andP[a_gtNpi a_lepi].
have piE : pi = pi / 2%:R + pi / 2%:R :> R.
  by rewrite -mulrDl -mulr2n -mulr_natr mulfK // ?pnatr_eq0.
case: (ltgtP a) => /= [aLhpi|hpiLa|->]; last by rewrite cos_pihalf eqxx.
  case: (ltgtP a) => /=[aLNhpi|NhpiLa|->]; last by rewrite cosN cos_pihalf eqxx.
    suff : 0 < sin (- (a + pi / 2%:R)).
      by rewrite sinN sinDpihalf oppr_cp0; case: ltgtP.
    rewrite sin_gt0_pi // oppr_cp0.
    rewrite -{1}[_ / _]opprK subr_lt0 aLNhpi /=.
    rewrite ltr_oppl (lt_le_trans a_gtNpi) //.
    rewrite -subr_le0 opprD addrA subrr sub0r oppr_cp0.
    by rewrite divr_ge0 ?ler0n // pi_ge0.
  suff : 0 < cos a by case: ltgtP.
  by rewrite cos_gt0_pihalf // NhpiLa aLhpi.
case: (ltgtP a) => /=[aLNhpi|NhpiLa|->]; last by rewrite cosN cos_pihalf eqxx.
  have := lt_trans hpiLa aLNhpi.
  by rewrite -subr_lt0 opprK -piE ltNge pi_ge0.
suff : 0 < cos (a - pi).
  by rewrite -cosN opprD opprK cosDpi cosN oppr_cp0; case: ltgtP.
rewrite cos_gt0_pihalf //.
rewrite -subr_gt0 {1}piE opprD opprK !addrA subrK subr_gt0 hpiLa /=.
apply: le_lt_trans (_ : 0 < _); first by rewrite subr_le0.
by rewrite divr_gt0 ?ltr0n // pi_gt0.
Qed.

Lemma sin_eq1_Npipi a :
  - pi < a <= pi -> (sin a == 1) = (a == pi / 2%:R).
Proof.
move=> aB; have /andP[a_gtNpi a_lepi] := (aB).
case: (ltgtP a) => /=[aLNhpi|NhpiLa|->]; last by rewrite sin_pihalf eqxx.
  case: eqP => // saE.
  have : cos a == 0 by rewrite -norm_sin_eq1 saE normr1.
  rewrite cos_eq0_Npipi //.
  case: ltgtP aLNhpi => //= _ _ /eqP aE.
  by move/eqP: saE; rewrite aE sinN sin_pihalf eqrNxx oner_eq0.
case: eqP => // saE.
have : cos a == 0 by rewrite -norm_sin_eq1 saE normr1.
rewrite cos_eq0_Npipi //.
case: ltgtP NhpiLa => //= _ _ /eqP aE.
by move/eqP: saE; rewrite aE sinN sin_pihalf eqrNxx oner_eq0.
Qed.

Lemma cos_eq1_Npipi a :
  - pi < a <= pi -> (cos a == 1) = (a == 0).
Proof.
move=> aB; have /andP[a_gtNpi a_lepi] := (aB).
case: (ltgtP a) => /=[a_lt0|a_gt0|->]; last by rewrite cos0 eqxx.
  case: eqP => // caE.
  have : sin a == 0 by rewrite -norm_cos_eq1 caE normr1.
  rewrite sin_eq0_Npipi //.
  case: ltgtP a_lt0=> //= _ _ /eqP aE.
  by move/eqP: caE; rewrite aE cospi eqrNxx oner_eq0.
case: eqP => // caE.
have : sin a == 0 by rewrite -norm_cos_eq1 caE normr1.
rewrite sin_eq0_Npipi //.
case: ltgtP a_gt0 => //= _ _ /eqP aE.
by move/eqP: caE; rewrite aE cospi eqrNxx oner_eq0.
Qed.

Lemma sin_eqN1_Npipi a : - pi < a <= pi -> (sin a == -1) = (a == - (pi / 2%:R)).
Proof.
case: (a =P pi) => [->|/eqP aDpi].
  rewrite sinpi eq_sym oppr_eq0 oner_eq0 => _.
  rewrite -subr_eq0  opprK -{1}[pi]mulr1 -mulrDr mulf_eq0.
  case: ltgtP (pi_gt0 R) => //= _ _.
  have -> : 1 + 2%:R^-1 = 3%:R / 2%:R :> R.
    by rewrite (natrD _  2 1) mulrDl divff ?mul1r // pnatr_eq0.
  by rewrite mulf_eq0 invr_eq0 ?pnatr_eq0.
move=> aB; rewrite -eqr_oppLR -sinN sin_eq1_Npipi ?eqr_oppLR //.
rewrite ltr_oppr opprK ler_oppl andbC.
by case: ltgtP aDpi aB => //= _; case: ltgtP.
Qed.

Lemma cos_eqN1_Npipi a : - pi < a <= pi -> (cos a == -1) = (a == pi).
Proof.
case: (a =P pi) => [->|aDpi]; first by rewrite cospi eqxx.
case: eqP => // caE aB.
have : sin a == 0 by rewrite -norm_cos_eq1 caE normrN normr1.
rewrite sin_eq0_Npipi //; case: eqP => /= [aE _|_ /eqP //].
by move/eqP: caE; rewrite aE cos0 -eqr_oppLR eqrNxx oner_eq0.
Qed.

(* NB: PR to analysis in progress *)
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

Lemma acosN1 : acos (- 1) = (pi : R).
Proof.
have oneB : -1 <= (-1 : R) <= 1 by rewrite lexx ge0_cp ?(ler0n _ 1).
apply: cos_inj; rewrite ?in_itv//= ?pi_ge0 ?lexx //.
  by rewrite acos_ge0 // acos_lepi.
by rewrite acosK ?in_itv//= cospi.
Qed.

Lemma acosN a : -1 <= a <= 1 -> acos (- a) = pi - acos a.
Proof.
move=> aB.
have aBN : -1 <= - a <= 1 by rewrite ler_oppl opprK ler_oppl andbC.
apply: cos_inj; first by rewrite in_itv/= acos_ge0 // acos_lepi.
  rewrite in_itv/= subr_ge0 acos_lepi // -subr_le0 addrAC subrr sub0r.
  by rewrite oppr_cp0 acos_ge0.
by rewrite addrC cosDpi cosN !acosK.
Qed.

Lemma cosKN a : - pi <= a <= 0 -> acos (cos a) = - a.
Proof.
move=> Hs.
rewrite -(cosN a) cosK // ?in_itv/=.
by rewrite ler_oppr oppr0 ler_oppl andbC.
Qed.

Lemma atan0 : atan 0 = 0 :> R.
Proof.
apply: tan_inj; first 2 last.
- by rewrite atanK tan0.
- by rewrite in_itv/= atan_gtNpi2 atan_ltpi2.
by rewrite in_itv/= oppr_cp0 divr_gt0 ?pi_gt0 // ltr0n.
Qed.

Lemma atan1 : atan 1 = pi / 4%:R :> R.
Proof.
apply: tan_inj; first 2 last.
- by rewrite atanK tan_piquarter.
- by rewrite in_itv/= atan_gtNpi2 atan_ltpi2.
have v2_ge0 : 0 <= 2%:R :> R by rewrite ler0n.
have v2_gt0 : 0 < 2%:R :> R by rewrite ltr0n.
rewrite in_itv/= -mulNr (lt_trans _ (_ : 0 < _ )) /=; last 2 first.
- by rewrite mulNr oppr_cp0 divr_gt0 // pi_gt0.
- by rewrite divr_gt0 ?pi_gt0 // ltr0n.
rewrite (natrM _ 2 2) invfM mulrA lter_pdivr_mulr // divfK ?natr_eq0 //.
  by rewrite ltr_pdivr_mulr // mulr_natr mulr2n -subr_gte0 addrK ?pi_gt0.
by case: ltgtP v2_gt0.
Qed.

Lemma atanN (x : R) : atan (- x) = - atan x.
Proof.
apply: tan_inj; first by rewrite in_itv/= atan_ltpi2 atan_gtNpi2.
  by rewrite in_itv/= ltr_oppl opprK ltr_oppl andbC atan_ltpi2 atan_gtNpi2.
by rewrite tanN !atanK.
Qed.
(* /NB: PR to analysis in progress *)

Lemma sin_half_angle a : `| sin (a / 2%:R) | = Num.sqrt ((1 - cos a) / 2%:R).
Proof.
move: (cosD (a / 2%:R) (a / 2%:R)).
rewrite -mulrDl -mulr2n -mulr_natr mulfK ?pnatr_eq0 //.
rewrite -2!expr2 cos2sin2 -addrA -opprD -mulr2n => /eqP.
rewrite eq_sym subr_eq addrC -subr_eq eq_sym => /eqP/(congr1 (fun x => x / 2%:R)).
rewrite -mulr_natl mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
by move/(congr1 Num.sqrt); rewrite sqrtr_sqr.
Qed.

Lemma cos_half_angle a : `| cos (a / 2%:R) | = Num.sqrt ((1 + cos a) / 2%:R).
Proof.
move: (cosD (a / 2%:R) (a / 2%:R)).
rewrite -mulrDl -mulr2n -mulr_natr mulfK ?pnatr_eq0 //.
rewrite -2!expr2 sin2cos2 opprB addrA -mulr2n => /eqP.
rewrite eq_sym subr_eq addrC => /eqP/(congr1 (fun x => x / 2%:R)).
rewrite -mulr_natl mulrC mulrA mulVr ?unitfE ?pnatr_eq0 // mul1r.
by move/(congr1 Num.sqrt); rewrite sqrtr_sqr.
Qed.

Lemma tan_half_angle a : tan (a / 2%:R) = (1 - cos a) / sin a.
Proof.
have aE : a = a / 2%:R + a / 2%:R.
  by rewrite -mulrDl -mulr2n -mulr_natr mulfK ?pnatr_eq0.
rewrite [in RHS]aE cosD sinD -!expr2 [sin _ * _]mulrC -mulr2n.
rewrite opprD opprK addrA -sin2cos2 -mulr2n.
rewrite -[X in _ = X / _]mulr_natr -[X in _ = _ / X]mulr_natr.
rewrite -mulf_div divff ?pnatr_eq0 // mulr1 /tan.
case: (sin (a / 2%:R) =P 0) => [->|/eqP saD0]; first by rewrite expr0n /= !mul0r.
by rewrite expr2 -mulf_div divff // mulr1.
Qed.

Lemma tan_half_angle' a : tan (a / 2%:R) = sin a / (1 + cos a).
Proof.
have aE : a = a / 2%:R + a / 2%:R.
  by rewrite -mulrDl -mulr2n -mulr_natr mulfK ?pnatr_eq0.
rewrite [in RHS]aE cosD sinD -!expr2 [sin _ * _]mulrC -mulr2n.
rewrite -opprB opprD opprK addrA -cos2sin2 -mulr2n.
rewrite -[X in _ = X / _]mulr_natr -[X in _ = _ / X]mulr_natr.
rewrite -mulf_div divff ?pnatr_eq0 // mulr1 /tan.
case: (cos (a / 2%:R) =P 0) => [->|/eqP saD0]; first by rewrite invr0 mulr0 !mul0r.
by rewrite expr2 -mulf_div divff // mul1r.
Qed.

End Extra.

From mathcomp Require Import ssrint complex sequences exp.
Local Open Scope complex_scope.

Lemma intrN (R : ringType) z : (-z)%:~R = - (z%:~R) :> R.
Proof. by rewrite -[in LHS]mulN1r intrM (intr_sign _ 1) mulN1r. Qed.

Lemma intrB (R : ringType) (z1 z2 : int) : (z1 - z2)%:~R = z1%:~R - z2%:~R :> R.
Proof. by rewrite intrD intrN. Qed.

Section Rfloor.

Local Open Scope real_scope.
Variable R : realType.
Implicit Types x y : R.

Lemma RfloorDz x z : Rfloor (x + z%:~R) = Rfloor x + z%:~R.
Proof.
have /andP[rxLx xLrx1] := mem_rg1_Rfloor x.
rewrite [in RHS]RfloorE -intrD.
apply/range1zP.
rewrite intrD -RfloorE /range1 /= ler_add2r rxLx /=.
by rewrite addrAC ltr_add2r.
Qed.

Lemma RfloorDn x n : Rfloor (x + n%:R) = Rfloor x + n%:R.
Proof. by apply: RfloorDz x n. Qed.

Lemma Rfloor_eq0 (x : R) : (Rfloor x == 0) = (0 <= x < 1).
Proof.
apply/eqP/idP => [/(range1zP 0)|xB]; first by rewrite /range1 /= add0r.
by apply/(range1zP 0); rewrite /range1 add0r.
Qed.

End Rfloor.


Section Rmod.

Local Open Scope real_scope.
Variable R : realType.
Implicit Types x y : R.


Definition Rmod x y := x - y * Rfloor (x / y).

Local Notation "m %% d" := (Rmod m d).
Local Notation "m = n %[mod d ]" := (m %% d = n %% d).

Lemma Rmodx0 x : x %% 0 = x.
Proof. by rewrite /Rmod mul0r subr0. Qed.

Lemma Rmod0x (x : R) : 0 %% x = 0.
Proof. by rewrite /Rmod mul0r Rfloor0 mulr0 subr0. Qed.

Lemma RmodMzl z x : (z%:~R * x) %% x = 0.
Proof.
have [->| /eqP x_neq0] := (x =P 0); first by rewrite !Rmodx0 mulr0.
by rewrite /Rmod mulfK // Rfloor_natz mulrC subrr.
Qed.

Lemma RmodMzr z x : (x * z%:~R) %% x = 0.
Proof.
have [->| /eqP x_neq0] := (x =P 0); first by rewrite !Rmodx0 mul0r.
by rewrite /Rmod mulrAC divff // mul1r Rfloor_natz subrr.
Qed.

Lemma Rmodxx x : x %% x = 0.
Proof.
have [->| /eqP x_neq0] := (x =P 0); first by rewrite !Rmodx0.
by rewrite /Rmod divff // Rfloor1 mulr1 subrr.
Qed.

Lemma Rmod_mod x y : x %% y = x %[mod y].
Proof.
have [->| /eqP y_neq0] := (y =P 0); first by rewrite !Rmodx0.
rewrite /Rmod !(mulrBl, mulrDl) mulrAC divff // mul1r.
by rewrite RfloorE -intrN RfloorDz intrN -RfloorE subrr mulr0 subr0.
Qed.

Lemma RmodD x y z :  x + y = x %% z + y %% z %[mod z].
Proof.
have [->| /eqP z_neq0] := (z =P 0); first by rewrite !Rmodx0.
rewrite /Rmod !(mulrBl, mulrDl) mulrAC divff // mulrAC divff // !mul1r.
rewrite !addrA  [Rfloor (y / z)]RfloorE -!intrN RfloorDz intrN -RfloorE.
rewrite [_ + _ + y /z]addrAC.
rewrite [Rfloor (x / z)]RfloorE -!intrN RfloorDz intrN -RfloorE.
rewrite !(mulrBr, mulrDr, opprB, opprD) !addrA subrK.
by rewrite [_ + _ + y]addrAC subrK.
Qed.

Lemma RmodDl (x y : R) : y + x = x %[mod y].
Proof. by rewrite RmodD Rmodxx add0r Rmod_mod. Qed.

Lemma RmodDr (x y : R) : x + y = x %[mod y].
Proof. by rewrite RmodD Rmodxx addr0 Rmod_mod. Qed.

Lemma RmodDml (x y z : R) : x %% z + y = x + y %[mod z].
Proof. by rewrite RmodD Rmod_mod -RmodD. Qed.

Lemma RmodDmr (x y z : R) : x + y %% z = x + y %[mod z].
Proof. by rewrite RmodD Rmod_mod -RmodD. Qed.

Lemma RmodBr (x y : R) : x - y = x %[mod y].
Proof. by rewrite RmodD -mulN1r (RmodMzl (-1)) addr0 Rmod_mod. Qed.

Lemma Rmodpbound (x y : R) : 0 < y -> 0 <= x %% y < y.
Proof.
move=> y_gt0.
have y_neq0 : y != 0 by case: ltgtP y_gt0.
have y_ge0 := ltW y_gt0.
rewrite /Rmod.
have /andP[rxLx xLrx1] := mem_rg1_Rfloor (x / y).
rewrite -[X in X - _](divfK y_neq0) mulrC -mulrBr pmulr_rge0 //.
rewrite subr_cp0 rxLx /= -[X in _ < X]mulr1 -subr_gte0 -mulrBr pmulr_rgt0 //.
by rewrite subr_cp0 ltr_sub_addr addrC.
Qed.

Lemma Rmodnbound (x y : R) : y < 0 -> y < x %% y <= 0.
Proof.
move=> y_lt0.
have y_neq0 : y != 0 by case: ltgtP y_lt0.
have y_le0 := ltW y_lt0.
rewrite /Rmod.
have /andP[rxLx xLrx1] := mem_rg1_Rfloor (x / y).
rewrite -[X in X - _](divfK y_neq0) mulrC -mulrBr nmulr_rle0 //.
rewrite subr_ge0 rxLx andbT.
rewrite -[X in X < _]mulr1 -subr_gte0 -mulrBr nmulr_rgt0 //.
by rewrite subr_lt0 ltr_sub_addr addrC.
Qed.

Lemma Rmod_psmall (x y : R) : 0 <= x < y -> x %% y = x.
Proof.
move=> /andP[x_ge0 x_gty].
suff : 0 <= x / y < 1.
  by rewrite -Rfloor_eq0 /Rmod => /eqP->; rewrite mulr0 subr0.
rewrite divr_ge0  ?(le_trans x_ge0 (ltW x_gty)) //=.
by rewrite lter_pdivr_mulr ?mul1r // (le_lt_trans x_ge0).
Qed.

Lemma Rmod_nsmall (x y : R) : y < x <= 0 -> x %% y = x.
Proof.
move=> /andP[y_ltx x_le0].
suff : 0 <= (- x) / (- y) < 1.
  rewrite invrN mulNr mulrN opprK.
  by rewrite -Rfloor_eq0 /Rmod => /eqP->; rewrite mulr0 subr0.
rewrite divr_ge0 ?oppr_cp0 // ?(le_trans (ltW y_ltx) x_le0) //=.
by rewrite lter_pdivr_mulr ?mul1r ?lter_oppE // (lt_le_trans y_ltx).
Qed.

End Rmod.
Notation "m %% d" := (Rmod m d) : real_scope.
Notation "m = n %[mod d ]" := (m %% d = n %% d) : real_scope.


Section Rcmod.

Local Open Scope real_scope.
Variable R : realType.
Implicit Types x y : R.

Definition Rcmod x y :=
  let r := x %% (2%:R * y) in 
  if 0 <= r <= y then r else r - (2%:R * y).

Local Notation "m '%c%' d" := (Rcmod m d)  (at level 40, no associativity).
Local Notation "m = n %[cmod d ]" := 
  (m %c% d = n %c% d) (at level 70, n at next level).

Lemma Rcmodx0 x : x %c% 0 = x.
Proof. by rewrite /Rcmod mulr0 Rmodx0 subr0 if_same. Qed.

Lemma Rcmodxx x : 0 <= x -> x %c% x = x.
Proof.
move=> x_ge0; rewrite /Rcmod.
have [->| /eqP x_neq0] := (x =P 0).
  by rewrite mulr0 !Rmodx0 subr0 if_same.
have x_gt0 : 0 < x by case: ltgtP x_neq0 x_ge0.
have x_gtx2 : x < 2%:R * x by rewrite mulr2n mulrDl mul1r -subr_gte0 addrK.
by rewrite ifT ?Rmod_psmall ?x_ge0 /=.
Qed.

Lemma Rcmod_mod x y : 0 <= y -> x %c% y = x %[cmod y].
Proof.
move=> y_ge0.
have [->| /eqP y_neq0] := (y =P 0); first by rewrite !Rcmodx0.
rewrite /Rcmod.
case: (boolP (0 <= x %% (2%:R * y) <= y)) => [|/negPf Hle].
  by rewrite Rmod_mod => ->.
by rewrite RmodBr Rmod_mod Hle.
Qed.

Lemma RcmodD x y z :  0 <= z -> x + y = x %c% z + y %c% z %[cmod z].
Proof.
move=> z_ge0.
have [->| /eqP z_neq0] := (z =P 0); first by rewrite !Rcmodx0.
rewrite /Rcmod.
case: (boolP (0 <= x %% (2%:R * z) <= z)) => [|/negPf Hxle];
case: (boolP (0 <= y %% (2%:R * z) <= z)) => [|/negPf Hyle].
- by rewrite -RmodD.
- by rewrite addrA RmodBr -RmodD.
- by rewrite [(_ - _ + _) %% _]RmodD RmodBr -!RmodD.
by rewrite [(_ - _ + _) %% _]RmodD !RmodBr -!RmodD.
Qed.

Lemma RcmodDml (x y z : R) : 0 <= z -> x %c% z + y = x + y %[cmod z].
Proof. by move=> z_ge0; rewrite RcmodD // Rcmod_mod // -RcmodD. Qed.

Lemma RcmodDmr (x y z : R) : 0 <= z -> x + y %c% z = x + y %[cmod z].
Proof. by move=> z_ge0; rewrite RcmodD // Rcmod_mod // -RcmodD. Qed.

Lemma Rcmodbound (x y : R) : 0 < y -> - y < x %c% y <= y.
Proof.
move=> y_gt0.
have y_ge0 := ltW y_gt0.
have y2_gt0 : 0 < 2%:R * y by rewrite mulr_gt0 // ltr0n.
have /andP[m_ge0 m_gty]:= Rmodpbound x y2_gt0.
rewrite /Rcmod m_ge0 /=.
case: (leP _ y) => [->|y_ltm].
  by rewrite (lt_le_trans _ m_ge0) // oppr_cp0.
rewrite ltr_subr_addr addrC {1}[_ * y]mulrDl mul1r addrK y_ltm //=.
by rewrite -lter_sub_addr opprK (le_trans (ltW m_gty)) // ler_addr.
Qed.

Lemma Rcmod_small (x y : R) : -y < x <= y -> x %c% y = x.
Proof.
move=> /andP[x_gtNy x_lty].
have y_gt0 : 0 < y.
  case: ltP; rewrite // -oppr_ge0  => H.
  have : - - y <= -y by rewrite ge0_cp.
  by rewrite leNgt opprK (lt_le_trans x_gtNy).
have y2_gt0 : 0 < 2%:R * y by rewrite mulr_gt0 // ltr0n.
case: (leP 0 x) => [x_ge0 | x_lt0].
  rewrite /Rcmod Rmod_psmall; first by rewrite x_ge0 x_lty.
  by rewrite x_ge0 (le_lt_trans x_lty) // -subr_gte0 mulrDl mul1r addrK.
rewrite /Rcmod -RmodDl Rmod_psmall //.
  rewrite ifN; first by rewrite [_ + x]addrC addrK.
  rewrite negb_and -!ltNge -ltr_subl_addl -[X in X - _]mul1r -mulrBl.
  by rewrite -(intrB _ 1 2) mulN1r x_gtNy orbT.
rewrite (le_trans (_ : 0 <= y + x)).
- by rewrite -ltr_subr_addl subrr x_lt0.
- by rewrite -ler_subl_addl sub0r ltW.
by rewrite ler_add2r mulrDl mul1r ler_addr ltW.
Qed.

Lemma Rcmod0x (x : R) : 0 <= x -> 0 %c% x = 0.
Proof. by move=> x_ge0; rewrite /Rcmod Rmod0x x_ge0 lexx. Qed.


Lemma Rcmodx2 (x : R) : 0 <= x -> (2%:R * x) %c% x = 0.
Proof.  by move=> x_ge0; rewrite /Rcmod Rmodxx x_ge0 lexx. Qed.


End Rcmod.

Local Notation "m '%c%' d" := (Rcmod m d)  (at level 40, no associativity).
Local Notation "m = n %[cmod d ]" := 
  (m %c% d = n %c% d) (at level 70, n at next level).
Section backport_complex.
Variable R : realType.

Lemma eq0c (x : R) : (x%:C == 0) = (x == 0).
Proof. by rewrite eq_complex eqxx/= andbT. Qed.

Lemma real_complexN (r : R) : (- r)%:C = - r%:C.
Proof. by apply/eqP; rewrite eq_complex/= oppr0 !eqxx. Qed.

Lemma real_complexM (r s : R) : (r * s)%:C = r%:C * s%:C.
Proof. by apply/eqP; rewrite eq_complex/= 2!mulr0 mul0r subr0 addr0 !eqxx. Qed.

Lemma scalec r s : (r * s)*i = r%:C * s*i :> R[i].
Proof. by apply/eqP; rewrite eq_complex/= mulr0 !mul0r subr0 addr0 !eqxx. Qed.

End backport_complex.

Section backport_trigo_alternating.
Variables (U : zmodType) (V : ringType).
Implicit Type f : U -> V.

Lemma alternatingN f (T : U) : alternating f T -> alternating f (- T).
Proof. by move=> fT u; rewrite -[LHS]opprK -fT subrK. Qed.

Lemma alternatingz f (T : U) : alternating f T ->
  forall k a, f (a + T *~ k) = (- 1) ^+ `|k|%N * f a.
Proof.
move=> fT k; have [k0 a|k0 a] := leP 0 k.
  by rewrite -(gez0_abs k0) -pmulrn alternatingn.
rewrite -(alternatingn (alternatingN fT)) -[in LHS](opprK k) -(ltz0_abs k0).
by rewrite  mulrNz mulNrn.
Qed.

End backport_trigo_alternating.

Section backport_trigo.
Variable R : realType.

Lemma sin_nat_pi n : sin (pi *+ n) = 0 :> R.
Proof. by rewrite -[_ *+ _]add0r (alternatingn (@sinDpi _)) sin0 mulr0. Qed.

Lemma sin_int_pi k : sin (pi *~ k) = 0 :> R.
Proof. by rewrite -[_ *~ _]add0r (alternatingz (@sinDpi _)) sin0 mulr0. Qed.

Lemma cos_nat_pi n : cos (pi *+ n) = (- 1) ^+ n :> R.
Proof. by rewrite -[_ *+ _]add0r (alternatingn (@cosDpi _)) cos0 mulr1. Qed.

Lemma cos_int_pi k  : cos (pi *~ k) = (- 1) ^+ `|k|%N :> R.
Proof. by rewrite -[_ *~ _]add0r (alternatingz (@cosDpi _)) cos0 mulr1. Qed.

Lemma sin_eq0 (r : R) : sin r = 0 <-> exists k, r = pi *~ k.
Proof.
split; last by move=> [k ->]; rewrite sin_int_pi.
wlog rpi : r / - pi < r <= pi.
  move=> h1 sr0; wlog r0 : r sr0 / 0 <= r.
    move=> h2; have [|r0] := leP 0 r; first exact: h2.
    have := h2 (- r); rewrite sinN sr0 oppr0 => /(_ erefl); rewrite ler_oppr.
    by rewrite oppr0 => /(_ (ltW r0))[k rkpi]; exists (- k); rewrite mulrNz -rkpi opprK.
  have [rpi|pir] := leP r pi.
    by apply: h1 => //; rewrite rpi (lt_le_trans _ r0)// ltr_oppl oppr0 pi_gt0.
  have /h1 : - pi < r - pi *~ floor (r / pi) <= pi.
    apply/andP; split.
      rewrite -mulrzl ltr_subr_addr addrC -[X in _ - X]mul1r -mulrBl.
      rewrite -ltr_pdivl_mulr ?pi_gt0// ltr_subl_addr -RfloorE.
      by rewrite (le_lt_trans (Rfloor_le _))// ltr_addl ltr01.
    rewrite -mulrzl ler_subl_addr -[X in X + _]mul1r -mulrDl.
    by rewrite -ler_pdivr_mulr ?pi_gt0// addrC -RfloorE ltW // lt_succ_Rfloor.
  rewrite sinB sin_int_pi mulr0 subr0 sr0 mul0r => /(_ erefl)[k /eqP].
  rewrite subr_eq -mulrzDl => /eqP rkpi; eexists; exact: rkpi.
by move=> /eqP; rewrite sin_eq0_Npipi// => /orP[|] /eqP ->;
  [exists 0; rewrite mulr0z|exists 1; rewrite mulr1z].
Qed.

Lemma expR_eq0 (x : R) : expR x = 1 -> x = 0.
Proof.
move/eqP; rewrite eq_le => /andP[eone onee]; apply/eqP; rewrite eq_le.
apply/andP; split.
  by move: eone; rewrite -ler_ln ?posrE ?ltr01 ?expR_gt0// ln1 expK.
by move: onee; rewrite -ler_ln ?posrE ?ltr01 ?expR_gt0// ln1 expK.
Qed.

End backport_trigo.

Section exp.
Variable R : realType.

Definition exp (z : R[i]) := (expR (Re z))%:C * (cos (Im z) +i* sin (Im z)).

Lemma exp_neq0 (z : R[i]) : exp z != 0.
Proof.
apply: mulf_neq0; first by rewrite eq0c gt_eqF// expR_gt0.
rewrite eq_complex/= -norm_sin_eq1; apply/negP => /andP[]/[swap]/eqP ->.
by rewrite normr0 eq_sym oner_eq0.
Qed.

Lemma exp_pi : exp (pi *i) = - 1.
Proof.
by rewrite /exp/= expR0 sinpi cospi/= mul1r complexr0 real_complexN.
Qed.

Lemma exp0 : exp 0 = 1.
Proof. by rewrite /exp/= cos0 sin0 expR0 mul1r. Qed.

Lemma exp_pihalf : exp ((pi / 2%:R) *i) = 'i.
Proof. by rewrite /exp/= sin_pihalf cos_pihalf expR0 mul1r. Qed.

Lemma expD (z w : R[i]) : exp (z + w) = exp z * exp w.
Proof.
move: z w => [x1 y1] [x2 y2]; rewrite /exp /=.
rewrite mulrCA !mulrA -real_complexM -expRD (addrC x2) -mulrA; congr (_ * _).
by rewrite cosD sinD/=; apply/eqP; rewrite eq_complex/= eqxx/= addrC.
Qed.

Lemma norm_exp (z : R[i]) : `| exp z | = (expR (Re z))%:C.
Proof.
move: z => [x y]/=; rewrite normc_def/= 2!mul0r subr0 addr0.
do 2 (rewrite exprMn_comm//; last exact: mulrC).
by rewrite -mulrDr cos2Dsin2 mulr1 sqrtr_sqr gtr0_norm// expR_gt0.
Qed.

Lemma real_complexD x y : (x + y)%:C = x%:C + y%:C :> R[i].
Proof. by apply/eqP; rewrite eq_complex /= addr0 !eqxx. Qed.

Lemma natrC n : n%:R %:C = n%:R :> R[i].
Proof.
elim: n => //= n IH.
rewrite -addn1 !natrD -IH real_complexD.
by apply/eqP; rewrite eq_complex !eqxx.
Qed.

Lemma intrC z : z%:~R %:C = z%:~R :> R[i].
Proof.
case: z => //= n; first by by rewrite natrC.
by rewrite NegzE !intrN real_complexN natrC.
Qed.

Lemma exp_eq1 (z : R[i]) : exp z = 1 <-> exists k, z = 2%:R * k%:~R * pi *i.
Proof.
split.
  move: z => [x y] /eqP; rewrite eq_complex/= 2!mul0r addr0 subr0 => /andP[].
  move=> /[swap]; rewrite mulf_eq0 gt_eqF/= ?expR_gt0// => /eqP/sin_eq0[k yk] h.
  have cs0 : 0 < cos y.
    by move: (@ltr01 R); rewrite -(eqP h); rewrite pmulr_rgt0 // expR_gt0.
  have ok : ~~ odd `|k|%N.
    apply/negP => ok; move: cs0.
    by rewrite yk cos_int_pi -signr_odd ok/= expr1 ltr0N1.
  move: h; rewrite yk cos_int_pi -signr_odd (negbTE ok) expr0 mulr1 => /eqP.
  move/expR_eq0 => ->{x}.
  rewrite (intEsg k); exists (sgz k * `|k|./2%N).
  rewrite (_ : _ * _%:~R = k%:~R); last first.
    rewrite intrM mulrCA -natrM mul2n.
    move: (odd_double_half `|k|); rewrite (negbTE ok) add0n => ->.
    by rewrite [in RHS](intEsg k) intrM.
  by rewrite -[in LHS]mulrzr mulrC scalec -intEsg intrC.
move=> [k ->].
rewrite /exp/=.
rewrite -(intrM _ 2) -intrC ReZ mulr0 expR0 mul1r.
by rewrite ImZ /= mulrzl cos_int_pi sin_int_pi abszM /= exprM sqrrN !expr1n.
Qed.

End exp.

Module Angle.
Section angle.
Record t (R : realType) := mk {
  a : R ;
  _ : - pi < a <= pi }.
End angle.
Module Exports.
Section exports.
Variable R : realType.
Local Notation angle := (@t R).
Canonical angle_subType := [subType for @a R].
Coercion a : angle >-> Real.sort.
End exports.
End Exports.
End Angle.
Export Angle.Exports.

Notation angle := Angle.t.

Section angle_canonicals.
Local Open Scope real_scope.
Variable R : realType.

Lemma angle0_subproof : - pi < (0 : R) <= pi.
Proof. by rewrite pi_ge0 andbT oppr_lt0 pi_gt0. Qed.

Definition angle0 := Angle.mk angle0_subproof.

Lemma angleNpi (a : angle R) : - pi < (a : R).
Proof. by case: a => ? /= /andP[]. Qed.

Lemma angle_pi (a : angle R) : (a : R) <= pi.
Proof. by case: a => ? /= /andP[]. Qed.

Let add (a b : angle R) : R := ((a : R) + (b : R)) %c% pi.
Let add_pi (a b : angle R) : - pi < add a b <= pi.
Proof. by apply/Rcmodbound/pi_gt0. Qed.

Definition add_angle (a b : angle R) : angle R := Angle.mk (add_pi a b).

Let opp (a : angle R) : R := if a == pi :> R then pi else - (a : R).

Let opp_pi (a : angle R) : - pi < opp a <= pi.
Proof.
apply/andP; split; rewrite /opp.
  case: ifPn => [_|api].
    by rewrite (@lt_trans _ _ 0) ?pi_gt0// ltr_oppl oppr0 pi_gt0.
  by rewrite ltr_oppl opprK lt_neqAle api (angle_pi a).
case: ifPn => // api.
by rewrite ler_oppl (le_trans (ltW (angleNpi a))).
Qed.

Definition opp_angle (a : angle R) : angle R := Angle.mk (opp_pi a).

Lemma add_angleC : commutative add_angle.
Proof.
by move=> a b; apply/val_inj => /=; rewrite /add addrC.
Qed.

Lemma add_angleA : associative add_angle.
Proof.
move=> a b c ; apply/val_inj; rewrite /add_angle /add /=.
have pi_ge0 := pi_ge0.
by rewrite [LHS]RcmodD // [RHS]RcmodD // !Rcmod_mod // -!RcmodD // addrA.
Qed.

Lemma add_0angle x : add_angle angle0 x = x.
Proof.
by apply/val_inj => /=; rewrite /add/= add0r Rcmod_small // angleNpi angle_pi.
Qed.

Lemma add_Nangle x : add_angle (opp_angle x) x = angle0.
Proof.
apply/val_inj => /=; rewrite /add/= /opp/=.
case: eqP => [->|_].
  by rewrite -mulr2n -mulr_natl Rcmodx2 // pi_ge0.
by rewrite addrC subrr Rcmod0x // pi_ge0.
Qed.

Definition angle_eqMixin := [eqMixin of angle R by <:].
Canonical angle_eqType := EqType (angle R) angle_eqMixin.
Definition angle_choiceMixin := [choiceMixin of angle R by <:].
Canonical angle_choiceType := ChoiceType (angle R) angle_choiceMixin.
Definition angle_ZmodMixin := ZmodMixin add_angleA add_angleC add_0angle
 add_Nangle.
Canonical angle_ZmodType := ZmodType (angle R) angle_ZmodMixin.

End angle_canonicals.

Section Extra2.

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

Lemma norm_angleDpi a : norm_angle (a + pi) = norm_angle (a - pi).
Proof.
rewrite /norm_angle sinDpi cosDpi -[_ - pi]opprB sinN addrC sinDpi sinN opprK.
by rewrite cosN cosDpi cosN.
Qed.

Lemma norm_angleNpi a : norm_angle (- pi) = pi.
Proof. by rewrite /norm_angle sinN sinpi oppr0 ltxx cosN cospi acosN1. Qed.

Lemma norm_angle_id a : - pi < a <= pi -> norm_angle a = a.
Proof.
move=> aB; rewrite /norm_angle; case: (ltP a 0) => [a_lt0|a_ge0]; last first.
  have aB1 : 0 <= a <= pi by rewrite a_ge0; case/andP: aB.
  by rewrite ltNge sin_ge0_pi /= ?cosK.
have aB1 : - pi < a < 0 by rewrite a_lt0 andbT; case/andP: aB.
have aB2 : - pi <= a <= 0 by case/andP: aB1 => *; rewrite !ltW.
rewrite -oppr_cp0 -sinN sin_gt0_pi; last by rewrite oppr_cp0 andbC ltr_oppl.
by rewrite -cosN cosK ?opprK // in_itv/= oppr_cp0 andbC ler_oppl.
Qed.

Lemma norm_angleN a : sin a != 0 -> norm_angle (- a) = - norm_angle a.
Proof.
by rewrite /norm_angle sinN  oppr_cp0; case: ltgtP => //= sH _;
   rewrite cosN ?opprK.
Qed.

Lemma sqrD1_cossin (x y : R) :
  x ^+ 2 + y ^+ 2 = 1 -> {a | [/\ - pi < a <= pi, x = cos a & y = sin a]}.
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
- rewrite ltr_oppl opprK ler_oppl lt_neqAle a1_lepi (ltW a1_gtNpi) ?andbT //.
  apply: contra sina1Dy => /eqP a1E.
  by rewrite eq_sym a1E sinpi -[_ == 0](expf_eq0 _ 2%N) y2E a1E sinpi expr0n.
- by rewrite cosN.
by have /eqP:= y2E; rewrite sinN eqf_sqr eq_sym (negPf sina1Dy) => /eqP.
Qed.

Lemma sqr_sin_atan (x : R) : (sin (atan x)) ^+ 2 = x ^+ 2 / (1 + x ^+ 2).
Proof.
case/boolP : (x == 0) => [/eqP ->|x0].
  by rewrite atan0 sin0 expr0n /= mul0r.
rewrite sin2cos2.
apply/eqP; rewrite -eqr_opp opprB subr_eq; apply/eqP.
rewrite -mulNr.
have /divrr H : 1 + x ^+ 2 \in GRing.unit.
  by rewrite unitfE gt_eqF // -(addr0 0) ltr_le_add // ?ltr01 // sqr_ge0.
rewrite -{2}H {H} addrC mulNr -mulrBl -invf_div -[LHS]invrK; congr (_ ^-1).
rewrite -exprVn -div1r expr_div_n expr1n cos2_tan2.
  by rewrite atanK addrK divr1 mul1r.
by rewrite gt_eqF // cos_gt0_pihalf // atan_ltpi2 atan_gtNpi2.
Qed.

Lemma ltr_atan : {mono (@atan R) : x y / x < y >-> x < y}.
Proof.
move=> x y; rewrite -[LHS]ltr_tan ?in_itv /= ?atan_gtNpi2 ?atan_ltpi2//.
by rewrite !atanK.
Qed.

Lemma sin_atan_ltr0 (x : R) : x < 0 -> sin (atan x) < 0.
Proof.
move=> x0.
rewrite -[X in X < _]opprK -sinN oppr_cp0 sin_gt0_pi //.
rewrite oppr_cp0 ltr_oppl andbC (lt_trans _ (atan_gtNpi2 _)) /=; last first.
  rewrite ltr_oppl opprK ltr_pdivr_mulr ?ltr0n // mulr_natr mulr2n.
  by rewrite -subr_gt0 addrK pi_gt0.
by rewrite -atan0 ltr_atan.
Qed.

Lemma sin_atan_gtr0 (x : R) : 0 < x -> 0 < sin (atan x).
Proof.
move=> x0.
by rewrite -(opprK (sin _)) -sinN -atanN -oppr_lt0 opprK sin_atan_ltr0 // oppr_lt0.
Qed.

Lemma sin_atan (x : R) : sin (atan x) = x / Num.sqrt (1 + x ^+ 2).
Proof.
apply/eqP.
case/boolP : (x == 0) => [/eqP ->|].
  by rewrite atan0 sin0 mul0r.
move/lt_total => /orP [] x0.
  rewrite -eqr_opp -(@eqr_expn2 _ 2) //; last 2 first.
    move/sin_atan_ltr0 : x0; by rewrite oppr_ge0 => /ltW.
    by rewrite -mulNr divr_ge0 // ?sqrtr_ge0 // oppr_ge0 ltW.
  by rewrite 2!sqrrN sqr_sin_atan exprMn exprVn sqr_sqrtr // addr_ge0 // ?ler01 // sqr_ge0.
rewrite -(@eqr_expn2 _ 2) //; last 2 first.
  by rewrite ltW // sin_atan_gtr0.
  by rewrite mulr_ge0 // ?invr_ge0 ?sqrtr_ge0 // ltW.
by rewrite sqr_sin_atan exprMn exprVn sqr_sqrtr // addr_ge0 // ?ler01 // sqr_ge0.
Qed.

Definition atan2 (x y : R) :=
  if y > 0 then atan (x / y) else
  if y < 0 then
     (if x >= 0 then atan (x / y) + pi else
        (* x < 0 *) atan (x / y) - pi) else
  (* y == 0 *)
     (if x > 0 then pi / 2%:R else
      if x < 0 then - (pi / 2%:R) else
        0) (* undefined *).

Lemma atan200 : atan2 0 0 = 0.
Proof. by rewrite /atan2 ltxx. Qed.

Lemma atan2_11 : atan2 1 1 = pi / 4%:R.
Proof. by rewrite /atan2 ltr01 invr1 mulr1 atan1. Qed.

Lemma atan2_0P y : 0 < y -> atan2 0 y = 0.
Proof.
by rewrite /atan2 mul0r atan0 add0r ltxx lexx => ->.
Qed.

Lemma atan2_0N y : y < 0 -> atan2 0 y = pi.
Proof.
by rewrite /atan2 mul0r atan0 add0r ltxx lexx; case: ltgtP.
Qed.

Lemma atan2_0l y : 0 < y -> atan2 0 y = 0.
Proof.
by rewrite /atan2 mul0r atan0 add0r ltxx lexx => ->.
Qed.

Lemma atan2N (x y : R) : x != 0 -> atan2 (- x) y = - atan2 x y.
Proof.
rewrite /atan2; have [y0|y0]:= ltP 0 y; first by rewrite mulNr atanN.
rewrite lt_neqAle y0 andbT; have [y0'|y0'] /= := boolP (y == 0).
  by rewrite oppr_gt0 oppr_lt0; case: ltrgt0P => x0; rewrite ?opprK ?oppr0.
by rewrite oppr_ge0; case: ltrgt0P => x0 // _; rewrite mulNr atanN opprD ?opprK.
Qed.

Lemma atan2_N1N1 : atan2 (- 1) (- 1) = - (pi / 4%:R) *+ 3.
Proof.
rewrite /atan2 ltr0N1 ltrN10 ler0N1 divrr; last first.
  by rewrite unitfE eqr_oppLR oppr0 oner_neq0.
rewrite atan1 -[in RHS]mulr_natr.
have -> : 3%:R = 4%:R - 1%:R :> R by rewrite -natrB.
by rewrite mulNr -mulrN opprB mulrBr mulr1 divfK // pnatr_eq0.
Qed.

(* properties_of_atan2. *)

Lemma sqrtr_sqrN2 (x : R) : x != 0 -> Num.sqrt (x ^- 2) = `|x|^-1.
Proof.
move=> x0.
apply (@mulrI _ `|x|); first by rewrite unitfE normr_eq0.
rewrite -{1}(sqrtr_sqr x) -sqrtrM ?sqr_ge0 // divrr; last by rewrite unitfE normr_eq0.
by rewrite divrr ?sqrtr1 // unitfE sqrf_eq0.
Qed.

Lemma sqrtr_1sqr2 (x y : R) : Num.sqrt (x ^+ 2 + y ^+ 2) = 1 -> x != 0 ->
  Num.sqrt (1 + (y / x) ^+ 2) = `|x|^-1.
Proof.
move=> u1 k0.
rewrite exprMn exprVn -(@divrr _ (x ^+ 2)) ?unitfE ?sqrf_eq0 //.
by rewrite -mulrDl sqrtrM ?u1 ?mul1r ?sqrtr_sqrN2 // addr_ge0// sqr_ge0.
Qed.

Lemma N1x2_gt0 (x : R) : `| x | < 1 -> 0 < 1 - x ^+ 2.
Proof. by move=> x1; rewrite subr_gt0 -sqr_normr expr_lt1. Qed.

Definition yarc (x : R) := Num.sqrt (1 - x ^+ 2).

Lemma yarc0 : yarc 0 = 1.
Proof. by rewrite /yarc expr0n subr0 sqrtr1. Qed.

Lemma yarc1 x : `| x | = 1 -> yarc x = 0.
Proof. by move/eqP; rewrite -sqr_norm_eq1 /yarc => /eqP ->; rewrite subrr sqrtr0. Qed.

Lemma yarc_neq0 (x : R) : `| x | < 1 -> yarc x != 0.
Proof. by move=> x1; rewrite sqrtr_eq0 -ltNge N1x2_gt0. Qed.

Lemma yarc_gt0 (x : R) : `| x | < 1 -> 0 < yarc x.
Proof. by move=> x1; rewrite lt_neqAle sqrtr_ge0 andbT eq_sym yarc_neq0. Qed.

Lemma sqr_yarc (x : R) : `| x | < 1 -> (yarc x) ^+ 2 = 1 - x ^+ 2.
Proof. move=> x1; by rewrite /yarc sqr_sqrtr // ltW // N1x2_gt0. Qed.

Lemma yarc_sin (x : R) : yarc (sin x) = `| cos x |.
Proof. by rewrite /yarc -cos2sin2 sqrtr_sqr. Qed.

Lemma inv_yarc (x : R) : `| x | < 1 -> (yarc x)^-1 = Num.sqrt (1 - x ^+ 2)^-1.
Proof.
move=> x1.
apply (@mulrI _ (yarc x)); first by rewrite unitfE yarc_neq0.
rewrite divrr; last by rewrite unitfE yarc_neq0.
rewrite -sqrtrM; last by rewrite ltW // N1x2_gt0.
by rewrite divrr ?sqrtr1 // unitfE gt_eqF // N1x2_gt0.
Qed.

Lemma inv_yarc_gt0 (x : R) : `| x | < 1 -> 0 < (yarc x)^-1.
Proof. move=> x1; by rewrite inv_yarc // sqrtr_gt0 invr_gt0 N1x2_gt0. Qed.

Lemma atan2_x_gt0E (x y : R) : y > 0 -> atan2 x y = atan (x / y).
Proof. move=> y0; by rewrite /atan2 y0. Qed.

Lemma atan2_ge0_lt0E (x y : R) : x >= 0 -> y < 0 -> atan2 x y = atan (x / y) + pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltNge ltW. Qed.

Lemma atan2_lt0_lt0E (x y : R) : x < 0 -> y < 0 -> atan2 x y = atan (x / y) - pi.
Proof. move=> x0 y0; by rewrite /atan2 x0 y0 ltNge ltW //= leNgt x0. Qed.

Lemma atan2_gt0_0E (x : R) : x > 0 -> atan2 x 0 = pi / 2%:R.
Proof. by move=> x0; rewrite /atan2 x0 ltxx. Qed.

Lemma atan2_lt0_0E (x : R) : x < 0 -> atan2 x 0 = - (pi / 2%:R).
Proof. move=> x0; by rewrite /atan2 ltxx ltNge ltW //= x0. Qed.

Lemma cos_atan2 (x y : R) : y != 0 -> cos (atan2 x y) = y / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neq_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // cosDpi ?eqxx // cos_atan expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 lt_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?lt_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_even_gt0 // orbC lt_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 lt_eqF.
    by rewrite !invrN invrK mulNr opprK.
  rewrite atan2_lt0_lt0E // -cosN opprD opprK cosDpi cosN.
  rewrite cos_atan expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // cos_atan.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gt_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gt_eqF // gtr0_norm // invrM ?invrK //.
by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_gt0.
by rewrite unitfE invr_neq0 // gt_eqF.
Qed.

Lemma cos_atan2_xyarc (x : R) : `| x | < 1 -> cos (atan2 (- x) (yarc x)) = yarc x.
Proof.
move=> x1; by rewrite cos_atan2 ?yarc_neq0 // sqr_yarc // sqrrN subrK sqrtr1 divr1.
Qed.

Lemma cos_atan2_yarcx (x : R) : `| x | < 1 -> cos (atan2 (yarc x) x) = x.
Proof.
move=> x1.
have [/eqP x0|x0] := boolP (x == 0).
  rewrite x0 yarc0.
  by rewrite /atan2 ltxx ltr01 cos_pihalf.
rewrite cos_atan2 //.
by rewrite sqr_yarc // addrCA subrr addr0 sqrtr1 divr1.
Qed.

Lemma sin_atan2 (x y : R) :
  y != 0 -> sin (atan2 x y) = x / Num.sqrt (y ^+ 2 + x ^+ 2).
Proof.
rewrite neq_lt => /orP[] y0.
  move=> [:H].
  case: (lerP 0 x) => x0.
    rewrite atan2_ge0_lt0E // sinDpi ?eqxx // sin_atan expr_div_n.
    abstract: H.
    rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 lt_eqF.
    rewrite -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
    rewrite sqrtr_sqrN2 ?lt_eqF // ltr0_norm // invrM; last 2 first.
      by rewrite unitfE sqrtr_eq0 -ltNge ltr_paddr // ?sqr_ge0 // exprn_even_gt0 // orbC lt_eqF.
      by rewrite unitfE invr_eq0 eqr_oppLR oppr0 lt_eqF.
    rewrite !invrN invrK mulNr mulrN opprK -mulrA (mulrA _^-1) mulVf ?mul1r //.
    by case: ltgtP y0.
  rewrite atan2_lt0_lt0E // -[LHS]opprK -sinN opprD opprK sinDpi sinN opprK.
  rewrite sin_atan expr_div_n.
  exact: H.
rewrite {1}atan2_x_gt0E // sin_atan.
rewrite -{1}(@divrr _ (y ^+ 2)); last by rewrite unitfE sqrf_eq0 gt_eqF.
rewrite expr_div_n -mulrDl sqrtrM; last by rewrite addr_ge0 // sqr_ge0.
rewrite sqrtr_sqrN2 ?gt_eqF // gtr0_norm // invf_div mulrA divfK //.
by case: ltgtP y0.
Qed.

Lemma sin_atan20x (x : R) : sin (atan2 0 x) = 0.
Proof.
have [/eqP ->|x0] := boolP (x == 0); first by rewrite atan200 sin0.
by rewrite sin_atan2 // mul0r.
Qed.

Lemma sin_atan2_0 (x : R) : sin (atan2 x 0) = Num.sg x.
Proof.
rewrite /atan2 ltxx; case: ifPn => [x0|]; first by rewrite sin_pihalf gtr0_sg.
rewrite -leNgt le_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltxx sin0 sgr0.
by rewrite x0 sinN sin_pihalf ltr0_sg.
Qed.

Lemma sin_atan2_xyarc (x : R) : `| x | < 1 -> sin (atan2 x (yarc x)) = x.
Proof.
move=> x1; by rewrite sin_atan2 ?yarc_neq0 // sqr_yarc // subrK sqrtr1 divr1.
Qed.

Lemma sin_atan2_yarcx (x : R) : `| x | < 1 -> sin (atan2 (yarc x) x) = yarc x.
Proof.
move=> x1.
have [/eqP x0|x0] := boolP (x == 0).
  rewrite x0 yarc0.
  by rewrite /atan2 ltxx ltr01 sin_pihalf.
rewrite sin_atan2 //.
by rewrite sqr_yarc // addrCA subrr addr0 sqrtr1 divr1.
Qed.

Lemma cos_atan2_0 (x : R) : cos (atan2 x 0) = (x == 0)%:R.
Proof.
rewrite /atan2 ltxx; case: ifPn => [x0|]; first by rewrite cos_pihalf gt_eqF.
rewrite -leNgt le_eqVlt => /orP[/eqP ->| x0]; first by rewrite ltxx cos0 eqxx.
by rewrite x0 cosN cos_pihalf lt_eqF.
Qed.

(* derived_trigonometric_functions. *)

Definition cot a := (tan a)^-1.

Lemma cot_pihalf : cot (pi / 2%:R) = 0.
Proof. by rewrite /cot tan_pihalf invr0. Qed.

Lemma cot_half_angle a : cot (a / 2%:R) = sin a / (1 - cos a).
Proof. by rewrite /cot tan_half_angle invf_div. Qed.

Lemma cot_half_angle' a : cot (a / 2%:R) = (1 + cos a) / sin a.
Proof. by rewrite /cot tan_half_angle' invf_div. Qed.

Definition sec a := (cos a)^-1.

Lemma secpi : sec pi = -1.
Proof. by rewrite /sec cospi invrN invr1. Qed.

End Extra2.
