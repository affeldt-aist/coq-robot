(* LaSalle (c) 2025 Inria and AIST. Licence: CeCILL-C.                        *)
(* -------------------------------------------------------------------------- *)
(* Copyright (c) - 2017 -- 2019 Inria                                         *)
(* -------------------------------------------------------------------------- *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice seq.
From mathcomp Require Import order interval_inference.
From mathcomp Require Import fintype bigop ssralg ssrnum finmap interval ssrint.
From mathcomp Require Import matrix zmodp ring.
From mathcomp Require Import mathcomp_extra.
From mathcomp Require Import boolp reals classical_sets functions.
From mathcomp Require Import topology normedtype prodnormedzmodule landau derive.
Require Import lasalle.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory Order.POrderTheory Order.TotalTheory.

Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Notation "p ..[ i ]" := (p 0 (inZp i)) (at level 10).

Lemma poly2_factor {R : realType} (a b c x : R) :
  a != 0 -> a * (x ^+ 2) + b * x + c = 0 ->
  x = (- b + Num.sqrt (b ^+ 2 - 4%:R * a * c)) / (2 * a) \/
  x = (- b - Num.sqrt (b ^+ 2 - 4%:R * a * c)) / (2 * a).
Proof.
move=> ane0 xroot.
set dlt := b ^+ 2 - 4%:R * a * c.
set x1 := (- b + Num.sqrt dlt) / (2 * a).
set x2 := (- b - Num.sqrt dlt) / (2 * a).
suff poly_fact : a * (x ^+ 2) + b * x + c = a * (x - x1) * (x - x2).
  move: xroot; rewrite poly_fact => /eqP; rewrite mulf_eq0 => /orP [].
    by rewrite mulrI_eq0; [rewrite subr_eq0 => /eqP->; left|apply/lregP].
  by rewrite subr_eq0 => /eqP->; right.
rewrite /x1 /x2; case: (lerP 0 dlt) => [dltge0|dltlt0].
  rewrite -mulrA mulrBr mulrBl mulrBl opprB addrA [(x * x + _) + _]addrAC.
  rewrite [_ / _ * x]mulrC.
  rewrite -[in RHS](addrA (x * x + _)).
  rewrite -(opprD (x * _)).
  rewrite -mulrDr.
  rewrite -mulrDl.
  rewrite addrCA -[- b + _ - _]addrA subrr addr0 -mul2r.
  rewrite invrM ?unitfE // [2 * _ * _]mulrC !mulrA mulfVK//.
  rewrite addrAC mulrN opprK !mulrDr mulrA [a * (x / _ * _)]mulrCA !mulrA.
  rewrite mulfVK// [b * _]mulrC; congr (_ + _ + _).
  rewrite [a * _]mulrC -[_ * a * _]mulrA mulfV // mulr1.
  rewrite ![_ * - _]mulrC !mulrA !mulrDr -!mulrDl !mulrN !mulNr !opprK.
  rewrite [_ * Num.sqrt _]mulrC -addrA addKr -!expr2 sqr_sqrtr // /dlt.
  rewrite opprD addrA subrr opprK add0r -mulrA -invrM ?unitfE //.
  rewrite (_ : 4 = 2 * 2); last by rewrite -natrM.
  rewrite mulrC !mulrA mulVf ?mul1r// (mulrC _ c) -mulrA divff ?mulr1//.
  by rewrite mulf_eq0 negb_or ane0 pnatr_eq0.
move: xroot; have -> : a * (x ^+ 2) + b * x + c =
  a * ((x + b / (2 * a)) ^+ 2) + (c - b ^+ 2 / (4%:R * a)).
  rewrite [in RHS]expr2 -mulrA mulrDr mulrDl [c - _]addrC addrA !mulrDr.
  rewrite -[_ - _]addrA -[a * _ + _ + _ in RHS]addrA; congr (_ + _ + _).
  rewrite addrA [(x + _) * _]mulrDl mulrDr addrA -mulrDr [x * _]mulrC -mulrDl.
  rewrite -[LHS]addr0 -addrA; congr (_ + _).
    rewrite mulrA; congr (_ * _); rewrite -mulrDl invrM ?unitfE //.
    rewrite mulrC -mulrA [_ * a]mulrC mulVKr ?unitfE // mulrDl.
    exact: splitr.
  rewrite !mulrA [a * _]mulrC -[b * a / _]mulrA invrM ?unitfE //.
  rewrite mulVKr ?unitfE // [b / _ * _]mulrAC -[_ / 2 * _]mulrA -mulrBr.
  rewrite [_^-1 * _]mulrCA invrM ?unitfE // -mulrBr -invrM ?unitfE //.
  by rewrite -natrM subrr !mulr0.
suff : a * (x + b / (2 * a)) ^+ 2 + (c - b ^+ 2 / (4%:R * a)) != 0.
  by move=> pn0 p0; move: pn0; rewrite p0 eq_refl.
have := ane0; rewrite neq_lt => /orP [alt0|agt0]; last first.
  apply:lt0r_neq0; rewrite ltr_wpDl //; first by rewrite pmulr_rge0 // sqr_ge0.
  rewrite subr_gt0 ltr_pdivrMr; last by rewrite pmulr_rgt0.
  by rewrite mulrC -subr_lt0.
rewrite -oppr_eq0 opprD; apply: lt0r_neq0; rewrite ltr_wpDl //.
  by rewrite oppr_ge0 nmulr_rle0 // sqr_ge0.
rewrite oppr_gt0 subr_lt0 ltr_ndivlMr; last by rewrite mulrC nmulr_rlt0.
by rewrite mulrC -subr_lt0.
Qed.

Lemma deriveE' {R : realType} (V W : normedModType R) (f : V -> W) x v :
  derive f x v = derive (fun h : R^o => f (h *: v + x)) 0 1.
Proof.
rewrite /derive.
set g1 := fun h => h^-1 *: _; set g2 := fun h => h^-1 *: _.
suff -> : g1 = g2 by [].
by rewrite funeqE /g1 /g2 => h /=; rewrite addr0 scale0r add0r [_%:A]mulr1.
Qed.

Lemma bounded_poly {R : realType} (a b c d : R) :
  0 < a -> \forall M \near +oo, forall x,
  a * (x ^+ 2) - (b * `|x|) - c < d -> `|x| < M.
Proof.
move=> agt0.
suff ptoinfty : (fun x => a * (x ^+ 2) - (b * `|x|) - c) @ +oo --> +oo.
  have dleatinfty : +oo (>= d).
    exists d; split => //.
      by rewrite num_real.
    by move=> // ? /ltW.
  have /ptoinfty [M1 [M1real sgtM1pged]] := dleatinfty; near=> M.
  move=> x pxltd; rewrite ltNge; apply/negP => Mlex.
  move: pxltd; rewrite ltNge => /negP; apply.
  rewrite -(@ger0_norm _ `|x|) // -(@ger0_norm _ (_ ^+ 2)) ?sqr_ge0 // normrX.
  by apply: sgtM1pged; apply: lt_le_trans Mlex; near: M; exists M1.
move=> A [M [Mreal sgtMA]]; rewrite !near_simpl; near=> x.
have lt0x : 0 < x by [].
rewrite ger0_norm ?ltW //; apply: sgtMA.
rewrite ltrBrDr expr2 mulrA -mulrBl; apply: le_lt_trans (ler_norm _) _.
rewrite -[ `|_|%R]sqr_sqrtr // expr2; apply: ltr_pM; last 1 first.
- by near: x; exists (Num.sqrt `|M + c|); split => //.
- exact: sqrtr_ge0.
- exact: sqrtr_ge0.
rewrite ltrBrDr -ltr_pdivrMl //; near: x.
exists (a^-1 * (Num.sqrt `|M + c| + b)); split => //.
rewrite realM//.
  by rewrite realV// num_real.
by rewrite realD// num_real.
Unshelve. all: by end_near. Qed.

(* TODO: generalize *)
Lemma eq0_derive1_cst {R : realType} (f : R^o -> R^o) (a b : R) :
  (forall t, t \in `[a, b] -> is_derive (t : R^o) 1 f 0) ->
  forall t, t \in `[a, b] -> f t = f a.
Proof.
move=> f'eq0 t tab; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: (@ler0_derive1_le_cc _ _ a b) => //; rewrite ?(itvP tab) //;[
    by move=> x /subset_itv_oo_cc /f'eq0 // df; rewrite derive1E derive_val..|].
  apply: continuous_in_subspaceT => x.
  rewrite inE/= => /f'eq0.
  move=> /(@ex_derive _ [the normedModType R of R^o]).
  move=> /derivable1_diffP /differentiable_continuous.
  exact.
apply: (@ger0_derive1_ndecr _ _ a b) => //; rewrite ?(itvP tab) //;[
  by move=> x /subset_itv_oo_cc /f'eq0 // df; rewrite derive1E derive_val..|].
apply: continuous_in_subspaceT => x.
rewrite inE/= => /f'eq0.
move=> /(@ex_derive _ [the normedModType R of R^o]).
move=> /derivable1_diffP /differentiable_continuous.
exact.
Qed.

Lemma is_derive_nneg_eq {R : realType} (f h : R^o -> R^o) (t : R^o) l1 l2 :
  (forall t, 0 <= t -> f t = h t) -> 0 <= t ->
  is_derive t 1 f l1 -> is_derive t 1 h l2 -> l1 = l2.
Proof.
move=> feg tge0 df dh.
have /@derive_val <- := df; have /@derive_val <- := dh.
apply: subr0_eq; rewrite -deriveB // /derive cvg_at_rightE; last first.
  by rewrite -[cvg _]/(derivable _ _ _).
apply: cvg_lim => A A0.
  by rewrite -closeEnbhs norm_closeE.
rewrite !near_simpl; near=> r.
rewrite /= -![(_ - _ : _ -> _) _]/(_ - _) !feg //.
  by rewrite !subrr scaler0; apply: nbhs_singleton.
by rewrite addr_ge0 // [_%:A]mulr1 ltW //; near: h; exists 1.
Unshelve. all: by end_near. Qed.

Section System.
Context {R : realType}.
Variable m M l g : {posnum R}.

Variable ke kv kx kd : {posnum R}.

Notation U := 'rV[R]_5.

(* p = (x, x', cos theta, sin theta, theta') *)
Definition E (p : U) :=
  (1 / 2) * ((M%:num + m%:num) * (p..[1] ^+ 2) +
  m%:num * (l%:num ^+ 2) * (p..[4] ^+ 2)) +
  m%:num * l%:num * p..[1] * p..[2] * p..[4] +
  m%:num * l%:num * g%:num * (p..[2] - 1).

Definition fctrl (p : U) :=
  (kv%:num * m%:num * p..[3] * (g%:num * p..[2] - l%:num * (p..[4] ^+ 2)) -
   (M%:num + m%:num * (p..[3] ^+ 2)) * (kx%:num * p..[0] + kd%:num * p..[1])) /
  (kv%:num + (M%:num + m%:num * (p..[3] ^+ 2)) * ke%:num * (E p)).

Definition Fpendulum (p : U) : U :=
  \row_(i < 5) nth 0
   [:: p..[1]
     ; ((m%:num * p..[3] * (l%:num * (p..[4] ^+ 2) - g%:num * p..[2]) +
       (fctrl p)) / (M%:num + m%:num * (p..[3] ^+ 2)))
     ; - p..[3] * p..[4]
     ; p..[2] * p..[4]
     ; (((M%:num + m%:num) * g%:num * p..[3] -
       p..[2] * (m%:num * l%:num * (p..[4] ^+ 2) * p..[3] + (fctrl p))) /
       (l%:num * (M%:num + m%:num * (p..[3] ^+ 2))))] i.

Definition V (p : U) :=
  (ke%:num / 2) * ((E p) ^+ 2) + (kv%:num / 2) * (p..[1] ^+ 2) +
  (kx%:num / 2) * (p..[0] ^+ 2).

Global Instance is_diff_component n i (p : 'rV[R]_n.+1) :
  is_diff p (fun q => q..[i] : R^o) (fun q => q..[i]).
Proof.
have comp_lin : linear (fun q : 'rV[R]_n.+1 => q..[i] : R^o).
  by move=> ???; rewrite !mxE.
have comp_cont : continuous (fun q : 'rV[R]_n.+1 => q..[i] : R^o).
  move=> q A [_/posnumP[e] Ae] /=; apply/nbhs_ballP; exists e%:num => //=.
  by move=> r [e0] /(_ ord0) /(_ (inZp i)) /Ae.
pose glM := GRing.isLinear.Build _ _ _ _ _ comp_lin.
pose gL : {linear 'rV_n.+1 -> R^o} := HB.pack (fun q : 'rV_n.+1 => q ..[ i]) glM.
apply: DiffDef; first exact: (@linear_differentiable _ _ _ gL).
by rewrite (@diff_lin _ _ _ gL).
Qed.

Global Instance is_diff_component_comp (V : normedModType R) n
  (f : V -> 'rV[R]_n.+1) i p df : is_diff p f df ->
  is_diff p (fun q => (f q)..[i] : R^o) (fun q => (df q)..[i]).
Proof.
move=> dfp.
have -> : (fun q => (f q)..[i]) = (fun v => v..[i]) \o f by rewrite funeqE.
(* This should work *)
(* apply: is_diff_eq. *)
exact: is_diff_comp.
Qed.

Global Instance is_derive_component (V : normedModType R) n
  (f : V -> 'rV[R]_n.+1) i x v df :
  is_derive x v f df -> is_derive x v (fun q => (f q)..[i] : R^o) (df..[i]).
Proof.
move=> dfx.
have diff_f : is_diff (0 : [the normedModType _ of R^o]) (fun h => f (h *: v + x)) ( *:%R^~ df ).
  have /derivable1P/derivable1_diffP fdrvbl : derivable f x v by [].
  by apply: DiffDef => //; rewrite diff1E // derive1E -deriveE' derive_val.
apply: DeriveDef; first exact/derivable1P/derivable1_diffP.
by rewrite deriveE' deriveE // diff_val scale1r.
Qed.

Lemma V_continuous : continuous V.
Proof.
by move=> ?; apply: (@differentiable_continuous _ _ R^o).
Qed.

Variable k0 : R.
Let B := ke%:num * ((minr (kv%:num / (ke%:num * (M%:num + m%:num)))
  (2 * m%:num * g%:num * l%:num)) ^+ 2) / 2.
(* restriction to make fctrl smooth *)
Hypothesis k0_valid : k0 < B.

Definition K : set U :=
  [set p : U | (p..[2] ^+ 2) + (p..[3] ^+ 2) = 1 /\ V p <= k0].

Lemma expr_continuous n : continuous (fun x : R^o => x ^+ n.+1 : R^o).
Proof.
move=> x; suff : differentiable (fun y : R^o => y ^+ n.+1) x.
  by apply: differentiable_continuous.
suff -> : (fun y => y ^+ n.+1) = ((id : R^o -> R^o) ^+ n.+1) by [].
by rewrite exprfctE.
Qed.

Lemma circle_closed : closed [set p : U | p..[2] ^+ 2 + p..[3] ^+ 2 = 1].
Proof.
move=> p clcircp.
apply/close_eq => //=; first exact: Rhausdorff.
rewrite (@ball_close _ R^o) => e /=.
have : nbhs (p ..[ 2] ^+ 2) (ball (p ..[ 2] ^+ 2) ((e%:num / 2)%:pos)%:num).
  by apply: nbhsx_ballx.
move=> /expr_continuous [_/posnumP[e1] p2e1_sp2he].
have : nbhs (p ..[ 3] ^+ 2) (ball (p ..[ 3] ^+ 2) ((e%:num / 2)%:pos)%:num).
  by apply: nbhsx_ballx.
move=> /expr_continuous [_ /posnumP[e2] p3e2_sp3he].
have [q [circq [e0 pme12_q]]] :
  [set p : U | p..[2] ^+ 2 + p..[3] ^+ 2 = 1] `&`
  ball p (minr e1%:num e2%:num) !=set0.
   apply/clcircp.
   rewrite /minr.
   by case: ifPn => // ?; apply/nbhsx_ballx.
rewrite -circq.
rewrite /ball/=.
rewrite opprD addrACA; apply: le_lt_trans (ler_normD _ _) _.
by rewrite (splitr e%:num) ltrD //; [apply/p2e1_sp2he|apply/p3e2_sp3he];
  apply: le_ball (pme12_q _ _); rewrite ge_min lexx // orbC.
Qed.

Lemma preimV_lek0_closed : closed (V @^-1` (<= k0 : _ -> _)).
Proof.
by apply: closed_comp; [move=> ??; apply: V_continuous|apply: closed_le].
Qed.

Lemma K_closed : closed K.
Proof. exact: closedI circle_closed preimV_lek0_closed. Qed.

Lemma K_bounded : bounded_set K.
Proof.
suff : \forall M \near +oo, forall p, K p -> forall i, `|p ord0 i| < M.
  rewrite /bounded_set; apply: filter_app; near=> M0.
  move=> Kbnd /= p /Kbnd ltpM0.
  rewrite /normr/=.
  rewrite mx_normrE.
  apply/bigmax_leP; split => //= i _.
  rewrite ord1.
  exact/ltW/ltpM0.
suff : \forall M \near +oo, forall p, K p -> `| p..[0] | < M /\
  `| p..[1] | < M /\ `| p..[2] | < M /\ `| p..[3] | < M /\ `| p..[4] | < M.
  apply: filter_app; near=> M0.
  move=> Kbnd p /Kbnd [ltp0M [ltp1M [ltp2M [ltp3M ltp4M]]]].
  case; do 5 ?[case; first by move=> ?; rewrite -[ Ordinal _ ]natr_Zp Zp_nat].
  by move=> n ?; suff : (n.+1.+4 < 5)%N by rewrite !ltnS ltn0.
have K1bnd : \forall M \near +oo, forall p, K p -> `| p..[1] | < M.
  near=> M0 => p [_ Vps].
    suff /lt_trans : `| p..[1] | < Num.sqrt (2 * B / kv%:num).
    by apply; near: M0; exists (Num.sqrt (2 * B / kv%:num)); split => //.
  rewrite -sqrtr_sqr ltr_sqrt // mulrAC -ltr_pdivrMl // invf_div; last first.
    by rewrite mulr0 /B/=.
  apply: le_lt_trans k0_valid; apply: le_trans Vps.
  by rewrite [V _]addrAC lerDr addr_ge0 // pmulr_rge0 // sqr_ge0.
apply: filter_app (K1bnd); near=> M0.
move=> K1ltM p Kp; have [circp Vps] := Kp; split.
  suff /lt_trans : `| p..[0] | < Num.sqrt (2 * B / kx%:num).
    by apply; near: M0; exists (Num.sqrt (2 * B / kx%:num)); split => //.
  rewrite -sqrtr_sqr ltr_sqrt // mulrAC -ltr_pdivrMl // invf_div; last first.
    by rewrite mulr0 /B.
  apply: le_lt_trans k0_valid; apply: le_trans Vps.
  by rewrite lerDr addr_ge0 // pmulr_rge0 // sqr_ge0.
split; first exact: K1ltM; split.
  suff /le_lt_trans : `| p..[2] | <= 1.
    apply.
    by near: M0; exists 1.
  by rewrite -sqrtr_sqr -sqrtr1 ler_sqrt // -circp lerDl sqr_ge0.
split.
  suff /le_lt_trans : `| p..[3] | <= 1.
    apply.
    by near: M0; exists 1.
  by rewrite -sqrtr_sqr -sqrtr1 ler_sqrt // -circp lerDr sqr_ge0.
move: p Kp {circp Vps}; near: M0; rewrite /= !near_simpl.
have [M1 [M1real sgtM1gtK1]] := K1bnd.
have := bounded_poly (m%:num * l%:num * ((`|M1| + 1) ^+ 2))
  (m%:num * l%:num * g%:num * ((`|M1| + 1) + 1)) (Num.sqrt (2 * B / ke%:num))
  [gt0 of m%:num * (l%:num ^+ 2) / 2].
apply: filter_app; near=> M0 => sEsltM0 p Kp; have [circp Vps] := Kp.
apply: sEsltM0.
have : E p < Num.sqrt (2 * B / ke%:num).
  apply: le_lt_trans (ler_norm _) _.
  rewrite -sqrtr_sqr ltr_sqrt // mulrAC -ltr_pdivrMl // invf_div; last first.
    by rewrite mulr0 /B.
  apply: le_lt_trans k0_valid; apply: le_trans Vps.
  by rewrite -[V _]addrA lerDl addr_ge0 // pmulr_rge0 // sqr_ge0.
apply: le_lt_trans; apply: lerD; last first.
  rewrite -mulrN opprD ler_wpM2l //.
  rewrite lerD2r lerNl.
  rewrite ler_wpDl // (le_trans (ler_norm _)) // normrN.
  rewrite -sqrtr_sqr.
  by rewrite -sqrtr1 ler_sqrt // -circp lerDl sqr_ge0.
rewrite mulrDr [1 / 2 * _ + _]addrC -addrA [1 / 2 * _]mulrCA mul1r mulrA.
rewrite /=.
rewrite (expr2 l%:num) lerD2l; apply: ler_wpDl.
  by rewrite pmulr_rge0 // pmulr_rge0 // sqr_ge0.
rewrite -mulrN -!mulrA ler_wpM2l // ler_wpM2l // !mulrN lerNl.
suff : `| p..[1] | * (`| p..[2] | * `| p..[4] |) <=
  (`|M1| + 1) * ((`|M1| + 1) * `| p..[4] |).
  by apply: le_trans; rewrite -!normrM -normrN ler_norm.
rewrite !mulrA ler_wpM2r // ler_pM //.
  apply/ltW/sgtM1gtK1 => //; apply: le_lt_trans (ler_norm _) _.
  by rewrite ltrDl.
have /(le_trans _) : 1 <= `|M1| + 1 by rewrite lerDr.
by apply; rewrite -sqrtr_sqr -sqrtr1 ler_sqrt // -circp lerDl sqr_ge0.
Unshelve. all: by end_near. Qed.

Lemma K_compact : compact K.
Proof. exact: bounded_closed_compact K_bounded K_closed. Qed.

Lemma Mp_ms_gt0 (p : U) : 0 < M%:num + m%:num * (p..[3] ^+ 2).
Proof. by rewrite ltr_pwDl // pmulr_rge0 // sqr_ge0. Qed.

Lemma E_small p : V p < B -> `|E p| < kv%:num / (ke%:num * (M%:num + m%:num)).
Proof.
move=> Vp_s; rewrite -ltr_sqr ?nnegrE // -normrX ger0_norm ?sqr_ge0 //.
suff : 2 * (V p) / ke%:num < (kv%:num / (ke%:num * (M%:num + m%:num))) ^+ 2.
  apply: le_lt_trans.
  rewrite ler_pdivlMr // -ler_pdivrMl // mulrC -mulrA mulrC.
  by rewrite /V -addrA lerDl addr_ge0 // pmulr_rge0 // sqr_ge0.
rewrite ltr_pdivrMr // mulrC -ltr_pdivlMr // (lt_le_trans Vp_s) //.
rewrite -mulrA mulrCA mulrA; apply: ler_pM => //; apply: ler_pM => //.
rewrite lerXn2r// ?nnegrE//.
by rewrite ge_min/= lexx.
Qed.

Lemma fctrl_wdef (p : U) : (p..[2] ^+ 2) + (p..[3] ^+ 2) = 1 -> V p < B ->
  kv%:num + (M%:num + m%:num * (p..[3] ^+ 2)) * ke%:num * (E p) != 0.
Proof.
move=> circp Vp_s; rewrite -normr_gt0.
rewrite -[X in X + _](@mulfVK _ ((M%:num + m%:num * (p..[3] ^+ 2)) * ke%:num));
  last by rewrite lt0r_neq0 // pmulr_rgt0 // Mp_ms_gt0.
rewrite mulrC -mulrDr normrM pmulr_rgt0; last first.
  by rewrite normrM pmulr_rgt0 gtr0_norm // Mp_ms_gt0.
apply: lt_le_trans (lerB_normD _ _).
rewrite subr_gt0; apply: lt_le_trans (E_small Vp_s) _.
rewrite ger0_norm; last first.
  by rewrite pmulr_rge0 // invr_ge0 pmulr_rge0 // Mp_ms_gt0.
rewrite ler_pM // lef_pV2 ?posrE //; last by rewrite pmulr_rgt0 // Mp_ms_gt0.
rewrite mulrC ler_pM //; first exact/ltW/Mp_ms_gt0.
rewrite lerD2l -{2}[m%:num]mulr1 ler_pM // ?sqr_ge0 //.
by rewrite -circp lerDr sqr_ge0.
Qed.

(* TODO: show that Fpendulum is smooth in K and remove these hypotheses using
  Cauchy-Lipschitz *)
Variable sol : U -> R -> U.
Hypothesis (sol0 : forall p, sol p 0 = p).
Hypothesis solP : forall y, K (y 0) -> is_sol Fpendulum y <-> y = sol (y 0).
Hypothesis sol_cont : forall t, {within K, continuous (sol^~ t)}.

Lemma circ_invar p :
  K p -> forall t, 0 <= t -> (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1.
Proof.
move=> Kp /= t tge0; have [circp _] := Kp; rewrite -circp -[in RHS](sol0 p).
pose f s := (sol p s)..[2] ^+ 2 + (sol p s)..[3] ^+ 2; rewrite -!/(f _).
(* BUG in unification *)
apply (@eq0_derive1_cst R (f : R^o -> R^o) 0 t); last first.
  by rewrite in_itv/= lexx tge0.
move=> s s0t; have sge0 : s >= 0 by rewrite (itvP s0t).
have [_ /(_ _ sge0) dsol] := sol_is_sol sol0 solP Kp.
apply: is_derive_eq.
rewrite 2!mxE/=.
rewrite /GRing.scale/=.
rewrite mulrCA.
by rewrite -!mulrDr addrC mulNr subrr.
Qed.

Lemma is_derive_Esol p t :
  K p -> 0 <= t -> is_derive (t : R^o) 1 (E \o (sol p) : _ -> R^o)
  ((sol p t)..[1] * fctrl (sol p t)).
Proof.
move=> Kp tge0; have [_ /(_ _ tge0) sol_att] := sol_is_sol sol0 solP Kp.
apply: is_derive_eq.
have /eqP : (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1 by apply: circ_invar.
rewrite eq_sym addrC -subr_eq => /eqP circp.
have Mpmsne0 : M%:num + m%:num * (sol p t)..[3] ^+ 2 != 0.
  by rewrite lt0r_neq0 // Mp_ms_gt0.
rewrite subr0 !mxE /= -circp -![_ *: _]/(_ * _) invrM ?unitfE //; last first.
  by rewrite circp.
set q := sol _ _ _; set x := (M%:num + m%:num * _)^-1; set y := fctrl _.
rewrite [x / _]mulrC; do ![rewrite ?[_ * (_ * x)]mulrA -?(mulrDl _ _ x)].
rewrite [_ * (_ + _ * x)]mulrDr [_ * (_ * x)]mulrA [_ + _ * x]addrC.
do 2 rewrite addrA -(mulrDl _ _ x).
rewrite -!mul2r mul1r mulrDr; do 2 rewrite [2^-1 * _]mulrCA.
do 2 rewrite [2^-1 * _]mulrA mulVf // mul1r.
rewrite [_ / _]mulrC.
rewrite ![_ * (_^-1 * _)]mulrA.
rewrite [_ * (_ / _ * _)]mulrA.
rewrite -(addrA ((M%:num + m%:num) *
   (q (inZp 1) *
    (m%:num * q (inZp 3) * (l%:num * q (inZp 4) ^+ 2 - g%:num * q (inZp 2)) + y)))).
rewrite -mulrDl.
rewrite [in _ * x]addrAC ![_ * (_ * (_ + _))]mulrA -mulrDl.
rewrite -addrA [_ * (_ * (- _ * _))]mulrA -mulrDl.
apply/(canLR (subrK _))/(canLR (mulfK _)); first by rewrite circp.
rewrite [RHS]mulrDl !mulNr [in RHS]mulrAC; apply: (canRL (addrK _)).
rewrite [(_ + _) * _]mulrDr addrAC [_ + _ * y + _]addrAC.
by field; rewrite gt_eqF.
(* this used to work with MathComp 2.4.0:
apply: (canLR (subrK _)); rewrite -mulrBl [_ * (_ + y)]mulrDr opprD addrA.
rewrite [_ * (_ - _ * y)]mulrDr addrA -[- (_ * y)]mulNr [_ * (_ * y)]mulrA.
rewrite [_ + _ * y + _]addrAC; apply: (canLR (subrK _)); rewrite -mulrBl.
rewrite [in RHS]mulrN opprK mulrACA [_ ^+2 / _]mulrAC mulfVK//.
rewrite [_ / _]mulrC ![_^-1 * _]mulrA [_^-1 * _ * _]mulrC mulVKf//.
ring.
*)
Qed.

Lemma is_deriv_Vsol p t :
  K p -> 0 <= t -> V (sol p t) < B ->
  is_derive (t : R^o) 1 (V \o (sol p) : _ -> R^o)
    (- kd%:num * ((sol p t)..[1] ^+ 2)).
Proof.
move=> Kp tge0 Vsolpt_s.
have [_ /(_ _ tge0) sol_att] := sol_is_sol sol0 solP Kp.
have Esol' := is_derive_Esol Kp tge0; apply: is_derive_eq.
rewrite [in X in _ + X]mxE /= -!mul2r -![_ *: _]/(_ * _).
do 3 rewrite [_ / _]mulrC [_^-1 * _ * _]mulrCA -[_ ^-1 * _ * _]mulrA mulVKf //.
rewrite [_ * fctrl _]mulrC [_ * Fpendulum _ _ _]mulrC mulrA mulrA -addrA.
rewrite ![in X in _ + X]mulrA -!mulrDl expr2 [RHS]mulrA; congr (_ * _).
rewrite addrA mxE /=.
have Mpmsne0 : M%:num + m%:num * (sol p t)..[3] ^+ 2 != 0.
  by rewrite lt0r_neq0 // Mp_ms_gt0.
apply: (canLR (subrK _)); rewrite [kv%:num * _]mulrA.
rewrite -[_ * fctrl _](mulfVK Mpmsne0) [_ / _ * _]mulrAC -mulrDl.
apply: (canLR (mulfK _)) => //; rewrite [kv%:num * _]mulrDr addrA addrAC.
apply: (canLR (subrK _)); rewrite mulrAC -mulrDl /fctrl [LHS]mulrA.
have circp : (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1 by apply: circ_invar.
have ? := fctrl_wdef circp Vsolpt_s; apply: (canLR (mulfK _)) => //.
ring.
Qed.

Lemma defset_invar p : K p -> forall t, 0 <= t ->
  (sol p t)..[2] ^+ 2 + (sol p t)..[3] ^+ 2 = 1 /\ V (sol p t) < B.
Proof.
move=> Kp t tge0; split; first exact: circ_invar.
set A := [set t | (0 <= t) && (B <= V (sol p t))].
case: (pselect (nonempty A))=> [An0 |]; last first.
  move=> /asboolPn /forallp_asboolPn /(_ t) /negP.
  by move => /nandP [];
    [rewrite tge0|rewrite -ltNge].
have infA : has_inf A.
  by split=> //; exists 0; apply/lbP => ? /andP [].
exfalso=> {t tge0}; have infge0 : 0 <= inf A.
  by apply: lb_le_inf => //; apply/lbP => ? /andP [].
have Vsolp_drvbl t : 0 <= t -> derivable (V \o (sol p) : R^o -> R^o) t 1.
  by move=> tge0; have [_ /(_ _ tge0) sol_att] := sol_is_sol sol0 solP Kp.
have Vsolpinf_geB : B <= V (sol p (inf A)).
  case: (lerP B (V (sol p (inf A)))) => // Vsolpinf_ltB; rewrite falseE.
  have Vsolp_cont : {for inf A, continuous (V \o (sol p))}.
    suff /differentiable_continuous :
      differentiable (V \o sol p : R^o -> R^o) (inf A) by [].
    exact/derivable1_diffP/Vsolp_drvbl.
  have BmVsolps_gt0 : 0 < B - V (sol p (inf A)) by rewrite subr_gt0.
  have /Vsolp_cont := nbhsx_ballx (V (sol p (inf A))) _ BmVsolps_gt0.
  move=> [_ /posnumP[e] /= infe_Vsolp].
  suff : inf A + e%:num / 2 <= inf A.
    by rewrite leNgt => /negP; apply; rewrite ltrDl.
  apply: lb_le_inf An0 _; apply/lbP => s /andP [sge0 Vsolps_geB].
  rewrite leNgt; apply/negP => ltsinfphe; have leinfs : inf A <= s.
    apply: inf_lbound => //.
      by case: infA.
    by rewrite /A/= sge0 Vsolps_geB.
  suff /infe_Vsolp : ball (inf A) e%:num s.
    rewrite /ball/= distrC => /(le_lt_trans (ler_norm _)).
    by rewrite ltNge => /negP; apply; rewrite lerB.
  rewrite /ball/= distrC ger0_norm ?subr_ge0 // ltrBlDl.
  by apply: lt_trans ltsinfphe _; rewrite ltrD2l {2}[e%:num]splitr ltrDl.
have Vsol_drvbl t : t \in `]0, (inf A)[ ->
  is_derive (t : R^o) 1 (V \o sol p : _ -> R^o)
  (- kd%:num * (sol p t)..[1] ^+ 2).
  move=> t0inf; apply: is_deriv_Vsol => //; first by rewrite (itvP t0inf).
  rewrite ltNge; apply/negP => Vsolpt_geB; suff : inf A <= t.
    by rewrite leNgt => /negP; apply; rewrite (itvP t0inf).
  apply: inf_lbound => //.
    by case: infA.
  apply/andP; split=> //.
  by rewrite (itvP t0inf).
have : {in `[0, (inf A)]%classic, continuous (V \o sol p)}.
  move=> t t0inf; suff /differentiable_continuous :
    differentiable (V \o sol p : R^o -> R^o) t by [].
  apply/derivable1_diffP/Vsolp_drvbl.
  rewrite inE/= in t0inf.
  by rewrite (itvP t0inf).
move/continuous_in_subspaceT.
move=> /(MVT_segment infge0)[t t0inf].
rewrite /comp sol0 subr0 => dVsol.
have infgt0 : 0 < inf A.
  rewrite lt_def; apply/andP; split=> //.
  apply/negP => /eqP infA0; have := Vsolpinf_geB.
  rewrite leNgt => /negP; apply; rewrite infA0 sol0.
  by apply: le_lt_trans k0_valid; have [] := Kp.
have : V (sol p (inf A)) - V p <= 0.
  by rewrite dVsol !mulNr oppr_le0 pmulr_lge0 // pmulr_rge0 // sqr_ge0.
rewrite leNgt => /negP; apply.
rewrite subr_gt0; apply: lt_le_trans Vsolpinf_geB.
by apply: le_lt_trans k0_valid; have [] := Kp.
Qed.

Lemma is_derive_Vsol p (t : R^o) :
  K p -> 0 <= t -> is_derive t 1 (V \o sol p : _ -> R^o)
  (- kd%:num * (sol p t)..[1] ^+ 2).
Proof.
move=> Kp tge0; have [circpt Vpts] := defset_invar Kp tge0.
exact: is_deriv_Vsol.
Qed.

Lemma Kinvar : is_invariant sol K.
Proof.
move=> p Kp t tge0; have [_ Vp_s] := Kp; split; first exact: circ_invar.
apply: le_trans Vp_s; rewrite -{2}[p]sol0.
have Vsol_deriv : forall s, s \in `[0, t] ->
  is_derive (s : R^o) 1 (V \o sol p : _ -> R^o)
  (- kd%:num * (sol p s)..[1] ^+ 2) by move=> s /andP [/(is_derive_Vsol Kp)].
apply: (@ler0_derive1_le_cc _ (V \o sol p) 0 t);[| | | | |by []].
- move=> x /subset_itv_oo_cc /Vsol_deriv.
  by apply: (@ex_derive _ [the normedModType R of R^o]).
- move=> x /subset_itv_oo_cc /Vsol_deriv.
  rewrite derive1E.
  case => _ ->.
  by rewrite mulr_le0_ge0// sqr_ge0.
- apply: continuous_in_subspaceT => x.
  rewrite inE/= => /Vsol_deriv.
  move=> /(@ex_derive _ [the normedModType R of R^o]).
  move=> /derivable1_diffP /differentiable_continuous.
  exact.
- by rewrite in_itv/= lexx tge0.
- by rewrite in_itv/= lexx tge0.
Qed.

Definition homoclinic_orbit : set U := [set p : U | p..[0] = 0 /\ p..[1] = 0 /\
  (1 / 2) * m%:num * (l%:num ^+ 2) * (p..[4] ^+ 2) =
  m%:num * g%:num * l%:num * (1 - p..[2])].

Lemma homoclinicE :
  homoclinic_orbit = [set p : U | p..[0] = 0 /\ p..[1] = 0 /\ E p = 0].
Proof.
rewrite predeqE => p; split.
  move=> [p0eq0 [p1eq0 /eqP]]; rewrite -subr_eq0 => /eqP homoeq.
  split=> //; split=> //; rewrite -homoeq /E p1eq0 expr0n /=.
  rewrite !mulr0 !mul0r addr0 add0r mulrA [_ / _ * _]mulrA -mulrN opprB.
  by rewrite [_ * _ * g%:num]mulrAC.
move=> [p0eq0 [p1eq0 Epeq0]]; split=> //; split=> //.
apply: subr0_eq.
rewrite -[RHS]Epeq0 /E p1eq0 expr0n /=.
rewrite !mulr0 !mul0r addr0 add0r [in RHS] mulrA [_ / _ * _ in RHS]mulrA -mulrN.
by rewrite opprB [_ * _ * g%:num]mulrAC.
Qed.

Lemma limSKinvar : is_invariant sol (limS sol K).
Proof.
move=> p limSKp t tge0.
exact: (@invariant_limS _ _ _ _ K_compact _ sol0 solP sol_cont Kinvar).
Qed.

Lemma subset_limSK_K : limS sol K `<=` K.
Proof.
move=> p [q Kq solq_top].
apply: compact_closed (@norm_hausdorff _ _) K_compact _ _.
have solqK : (sol q @ +oo) K.
  exists 0; split.
    by rewrite real0.
  by move=> ? /ltW; exact: Kinvar.
by move=> A /solq_top - /(_ _ solqK) [r []]; exists r.
Qed.

Lemma Vsol'_eq0 p t :
  limS sol K p -> 0 <= t -> derive1 (V \o sol p : _ -> R^o) t = 0.
Proof.
move=> limSKp tge0; have limSKsolp : limS sol K (sol p t) by apply: limSKinvar.
have Kp : K p by apply: subset_limSK_K.
have -> : derive1 (V \o sol p : _ -> R^o) t =
  derive1 (V \o sol (sol p t) : _ -> R^o) 0.
  have dVsolt := is_derive_Vsol Kp tge0; rewrite derive1E derive_val.
  have Ksolpt : K (sol p t) by apply: subset_limSK_K.
  have dVsolt' := is_derive_Vsol Ksolpt (lexx _); rewrite derive1E derive_val.
  rewrite -(solD sol0 solP Kinvar) //.
  by rewrite add0r.
apply: (stable_limS K_compact sol0 solP sol_cont Kinvar (V:=V)) limSKsolp.
- apply/subspace_continuousP => q Kq; have /(_ q) := V_continuous; apply: cvg_trans.
  exact: cvg_app (@cvg_within _ _ _ _).
- by move=> q s Kq sge0; have := is_derive_Vsol Kq sge0.
- move=> q Kq; have dVsolq := is_derive_Vsol Kq (lexx _).
  by rewrite derive1E derive_val mulNr oppr_le0 pmulr_rge0 // sqr_ge0.
Qed.

Lemma sol1_eq0 p t : limS sol K p -> 0 <= t -> (sol p t)..[1] = 0.
Proof.
move=> limSKp tge0; have Kp : K p by apply: subset_limSK_K.
have dVsol := is_derive_Vsol Kp tge0; have /eqP := Vsol'_eq0 limSKp tge0.
rewrite derive1E derive_val mulrI_eq0; last exact/lregN/lregP.
by rewrite sqrf_eq0 => /eqP.
Qed.

Lemma sol1'_eq0 p t : limS sol K p -> 0 <= t -> (Fpendulum (sol p t))..[1] = 0.
Proof.
move=> limSKp tge0; have := is_derive_cst (0 : R^o) (t : R^o) 1.
have /subset_limSK_K Kp := limSKp.
have [_ /(_ _ tge0) /(is_derive_component 1)] := sol_is_sol sol0 solP Kp.
by apply: is_derive_nneg_eq => // s sge0; rewrite sol1_eq0.
Qed.

Lemma sol0_const p t : limS sol K p -> 0 <= t -> (sol p t)..[0] = p..[0].
Proof.
move=> limSKp tge0; rewrite -[p in RHS]sol0.
apply (@eq0_derive1_cst R (fun s => (sol p s)..[0]) 0 t); last first.
  by rewrite in_itv/= lexx tge0.
move=> s /andP [sge0 _]; have /subset_limSK_K Kp := limSKp.
have [_ /(_ _ sge0) /(is_derive_component 0) dsol0] := sol_is_sol sol0 solP Kp.
by apply: DeriveDef => //; rewrite derive_val mxE /= sol1_eq0.
Qed.

Lemma Esol_const p t : limS sol K p -> 0 <= t -> (E \o sol p) t = E p.
Proof.
move=> limSKp tge0; rewrite -[p in RHS]sol0.
apply (@eq0_derive1_cst R (E \o sol p) 0 t); last first.
  by rewrite in_itv/= lexx tge0.
move=> s /andP [sge0 _]; have /subset_limSK_K Kp := limSKp.
have dEsol := is_derive_Esol Kp sge0; apply: DeriveDef => //.
by rewrite derive_val sol1_eq0 // mul0r.
Qed.

Lemma Efctrl_psol0_eq0 p t : limS sol K p -> 0 <= t ->
  ke%:num * (E (sol p t)) * (fctrl (sol p t)) + kx%:num * (sol p t)..[0] = 0.
Proof.
move=> limSKp tge0.
rewrite [RHS](_ : _ =
    - (kd%:num * (sol p t)..[1] + kv%:num * (Fpendulum (sol p t))..[1])); last first.
  by rewrite sol1'_eq0 // sol1_eq0 // !mulr0 add0r oppr0.
have [circsolt /le_lt_trans /(_ k0_valid) Vsolts] : K (sol p t).
  by apply: Kinvar tge0; apply: subset_limSK_K.
have fctrl_def := fctrl_wdef circsolt Vsolts.
have Mpmsne0 : M%:num + m%:num * (sol p t)..[3] ^+ 2 != 0.
  by rewrite lt0r_neq0 // Mp_ms_gt0.
rewrite /Fpendulum !mxE /= /fctrl; apply: (canLR (subrK _)); rewrite mulrA.
apply: (canLR (mulfK _)) => //; rewrite [RHS]mulrDl; apply: (canRL (subrK _)).
rewrite opprD [RHS]mulrDl [RHS]addrC; apply/(canRL (subrK _))/Logic.eq_sym.
rewrite mulrC -mulNr mulrA mulrA; apply: (canLR (mulfK _)) => //.
rewrite [RHS]mulrDr [LHS]mulrDr addrC; apply: (canLR (subrK _)).
rewrite mulrA -[in X in X / _]mulrA; apply: (canLR (mulfK _)) => //.
ring.
Qed.

Lemma div_fctrl_mP p t : limS sol K p -> 0 <= t ->
  (sol p t)..[3] * (g%:num * (sol p t)..[2] - l%:num * (sol p t)..[4] ^+ 2) =
  (fctrl (sol p t)) / m%:num.
Proof.
move=> limSKp tge0; apply: (canRL (mulfK _)) => //; apply: subr0_eq.
have := sol1'_eq0 limSKp tge0; rewrite !mxE /= => /(canRL (mulfK _)).
rewrite mul0r => fctrl_val.
rewrite mulrC mulrA -[in X in X - _]opprB mulrN -opprD fctrl_val ?oppr0 //.
exact/invr_neq0/lt0r_neq0/Mp_ms_gt0.
Qed.

Lemma Fpendulum4E p t : limS sol K p -> 0 <= t ->
  (Fpendulum (sol p t))..[4] = g%:num / l%:num * (sol p t)..[3].
Proof.
move=> limSKp tge0; rewrite !mxE /=.
have /(canLR (mulfVK _)) <- // := div_fctrl_mP limSKp tge0.
apply: (canLR (mulfK _)); last apply/esym.
  by apply: lt0r_neq0; rewrite pmulr_rgt0 // Mp_ms_gt0.
rewrite mulrCA mulrA mulrA [l%:num * _ in LHS]mulrC mulfVK//.
have [] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
rewrite addrC => /(canRL (addrK _)) -> _.
ring.
Qed.

Lemma En0_fctrlsol_const p t :
  limS sol K p -> E p != 0 -> 0 <= t -> fctrl (sol p t) = fctrl p.
Proof.
move=> limSKp Epn0 tge0.
have := Efctrl_psol0_eq0 limSKp tge0.
rewrite -[X in _ = X -> _](Efctrl_psol0_eq0 limSKp (lexx _)) sol0
  [E (sol p t)](Esol_const limSKp tge0) (sol0_const limSKp tge0).
have keEn0 : ke%:num * E p != 0 by rewrite mulrI_eq0 //; apply/lregP.
move/(canRL (addrK _)); rewrite -addrA subrr addr0 mulrC.
by move=> /(canRL (mulfK _)) - /(_ keEn0) ->; rewrite mulrAC -mulrA mulVKf.
Qed.

Lemma inf_in_finset (A : {fset R}) :
  has_inf [set t | t \in A] -> inf [set t | t \in A] \in A.
Proof.
move=> infA; have [[t At] _] := infA.
have Amin : \big[minr/t]_(s <- enum_fset A) s \in A.
  have : forall s, s \in enum_fset A -> s \in A by [].
  elim: (enum_fset A) => [inA|s l0 ihl0 inA]; first by rewrite big_nil.
  rewrite big_cons.
  have [sl|sl] := leP s _.
    by apply: inA; rewrite mem_head.
  by apply: ihl0 => r lr; apply: inA; rewrite inE orbC lr.
suff -> : inf [set t | t \in A] = \big[minr/t]_(s <- enum_fset A) s by [].
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: inf_lbound => //.
  by case: infA.
apply: lb_le_inf; first by have [] := infA.
apply/lbP => s As; have : s \in enum_fset A by [].
elim: (enum_fset A) => // r l0 ihl0; rewrite inE => /orP [/eqP <-|].
  by rewrite big_cons ge_min lexx.
by rewrite big_cons ge_min orbC => /ihl0 ->.
Qed.

Lemma continuous_finimage_cst (f : R -> R) n (h : 'I_n -> R) :
  {in (>= 0), continuous f} ->
  (forall t, 0 <= t -> exists i, f t = h i) ->
  forall t, 0 <= t -> f t = f 0.
Proof.
case: n h => [h ? finim_f t tge0|]; first by have /finim_f [] := tge0; case.
case=> [|n] h fcont finim_f t tge0.
  have /finim_f [i ->] := tge0; have /finim_f [j ->] := lexx (0 : R).
  by rewrite !ord1.
case: (eqVneq (f t) (f 0)) => // ftnef0.
set fl := minr (f 0) (f t); set fr := maxr (f 0) (f t).
have ltflr : fl < fr.
  rewrite /fr.
  have [left0|lt0ft] := leP (f 0) _.
    rewrite /fl; move: (left0) => /min_idPl => ->.
    by rewrite lt_def ftnef0/= left0.
  by rewrite /fl; move/ltW: (lt0ft) => /min_idPr => ->.
set img := [set x | (fl < x) && (x \in range h)].
have imgfr : (range h) fr.
  rewrite /fr.
  have [f0ft|f0ft] := leP (f 0) (f t).
    by have /finim_f [i] := tge0; exists i.
  by have /finim_f [i] := lexx (0 : R); exists i.
have imgn0 : nonempty img.
  exists fr.
  by rewrite /img/= ltflr andTb; apply/asboolP.
have infimg : has_inf img.
  by split=> //; exists fl; apply/lbP => ? /andP [/ltW].
have [] := @IVT _ f _ _ ((fl + inf img) / 2) tge0.
  apply: continuous_in_subspaceT => x.
  rewrite inE/= in_itv/= => /andP[x0 xt].
  by apply: fcont => //=.
  apply/andP; split.
    rewrite ler_pdivlMr // mulrC mul2r lerD2l.
    by apply: lb_le_inf imgn0 _; apply/lbP => ? /andP [/ltW].
  rewrite ler_pdivrMr // mulrC mul2r lerD //; first exact: ltW.
  apply: inf_lbound => //.
    by case: infimg.
  by apply/andP; split=> //; apply/asboolP.
move=> s s0t fsemid; suff ltfl_inf : fl < inf img.
  have : inf img <= (fl + inf img) / 2.
    apply: inf_lbound.
      by case: infimg.
    apply/andP; split; last first.
      have /finim_f [i] : 0 <= s by rewrite (itvP s0t).
      by rewrite fsemid => midegi; apply/asboolP; exists i.
    by rewrite ltr_pdivlMr // mulrC mul2r ltrD2l.
  by rewrite ler_pdivlMr // mulrC mul2r lerD2r leNgt ltfl_inf.
have imgE : img = pred_of_finset [fset x in
  [seq t <- [seq h i | i : 'I_n.+2] | fl < t]]%fset :> set R.
  rewrite funeqE => x; rewrite /img /= /pred_of_finset in_fset/=.
  apply/propext; split.
    rewrite mem_filter => /andP[flx].
    rewrite inE => -[i _ gix].
    rewrite flx/=.
    apply/mapP; exists i => //=.
    by rewrite mem_enum.
  rewrite mem_filter/= => /andP[flx /mapP[/= i _ xgi]].
  rewrite flx/= xgi.
  by apply/asboolP; exists i.
rewrite imgE; set A := [fset x in _]%fset.
have : inf (pred_of_finset A) \in A.
  by apply: inf_in_finset; rewrite -[X in has_inf X]imgE.
by rewrite /A in_fset mem_filter => /andP [].
Qed.

Lemma En0_sol2_const p :
  limS sol K p -> E p != 0 -> forall t, 0 <= t -> (sol p t)..[2] = p..[2].
Proof.
move=> limSKp Epn0 t tge0.
have Kp : K p by apply: subset_limSK_K.
set C1 := - (2 * g%:num + 2 * (E p) / (m%:num * l%:num)).
set C2 := fctrl p / m%:num.
have sol32_val : forall s, 0 <= s ->
  (sol p s)..[3] * (3%:R * g%:num * (sol p s)..[2] + C1) = C2.
  move=> s sge0.
  rewrite /C1 /C2 -(Esol_const limSKp sge0) /E /= (sol1_eq0 limSKp sge0)
    -(En0_fctrlsol_const limSKp Epn0 sge0) -(div_fctrl_mP limSKp sge0).
  rewrite !expr0n /= !mulr0 !mul0r add0r addr0.
  rewrite (mulrDr 2).
  rewrite mulrA [1 / _]mulrC.
  rewrite mulVKr ?unitfE // mul1r mulrBr addrC; apply: (canLR (subrK _)).
  rewrite -mulNr mulrDr addrC; apply: (canLR (subrK _)).
  rewrite mulrA; apply: (canLR (mulfK _)) => //.
  ring.
have sol423_val s : 0 <= s ->
  (sol p s)..[4] * (3%:R * g%:num * ((sol p s)..[2] ^+ 2 -
  (sol p s)..[3] ^+ 2) + C1 * (sol p s)..[2]) = 0.
  move=> sge0; apply (is_derive_nneg_eq sol32_val sge0); last first.
    exact: is_derive_cst.
  have [_ /(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp; apply: is_derive_eq.
  rewrite !mxE /=.
  rewrite /GRing.scale/=.
  ring.
have sol432_val' s : 0 <= s ->
  (sol p s)..[3] * (g%:num / l%:num * (3%:R * g%:num * ((sol p s)..[2] ^+ 2 -
    (sol p s)..[3] ^+ 2) + C1 * (sol p s)..[2]) -
    (sol p s)..[4] ^+ 2 * (12%:R * g%:num * (sol p s)..[2] + C1)) = 0.
  move=> sge0; apply (is_derive_nneg_eq sol423_val sge0); last first.
    exact: is_derive_cst.
  have [_ /(_ _ sge0) sol_ats] := sol_is_sol sol0 solP Kp; apply: is_derive_eq.
  rewrite Fpendulum4E // !mxE /= addrC; apply: (canLR (subrK _)).
  rewrite -![_ *: _]/(_ * _) mulrA mulrAC mulrA; apply: (canLR (mulfK _)) => //.
  rewrite [in RHS]mulrDl; apply: (canRL (subrK _)).
  rewrite [(sol p s)..[3] * _]mulrDr [in RHS]mulrDl; apply: (canRL (subrK _)).
  rewrite [_ / _ * _]mulrC [in RHS]mulrA [in RHS]mulrA mulfVK//.
  ring.
set x1 := (- C1 + Num.sqrt (C1 ^+ 2 - 4%:R * (6%:R * g%:num) *
  (- 3%:R * g%:num))) / (2 * (6%:R * g%:num)).
set x2 := (- C1 - Num.sqrt (C1 ^+ 2 - 4%:R * (6%:R * g%:num) *
  (- 3%:R * g%:num))) / (2 * (6%:R * g%:num)).
set f := fun i : 'I_4 => if i == 0 then - 1 else
                           if i == 1 then 1 else
                             if i == 2 then x1 else x2.
rewrite -[p in RHS]sol0.
apply: (@continuous_finimage_cst (fun s => (sol p s)..[2]) _ f) tge0.
  move=> s sge0; apply: (@differentiable_continuous _ R^o R^o).
  have [_ /(_ _ sge0) sol_ats]:= sol_is_sol sol0 solP Kp.
  exact/derivable1_diffP.
move=> s sge0.
have circsol : (sol p s)..[2] ^+ 2 + (sol p s)..[3] ^+ 2 = 1.
  suff [] : K (sol p s) by [].
  exact/subset_limSK_K/limSKinvar.
have solroot_imf :
  3%:R * g%:num * ((sol p s)..[2] ^+ 2 - (sol p s)..[3] ^+ 2) +
  C1 * (sol p s)..[2] = 0 -> exists i, (sol p s)..[2] = f i.
  have -> : (sol p s)..[3] ^+ 2 = 1 - (sol p s)..[2] ^+ 2.
    by rewrite -circsol [X in X - _]addrC addrK.
  move=> sol2_val.
  have sol2_root :
    6%:R * g%:num * ((sol p s)..[2] ^+ 2) + C1 * (sol p s)..[2] +
    (- 3%:R * g%:num) = 0.
    rewrite -[RHS]sol2_val.
    ring.
  case/poly2_factor: sol2_root => {sol2_val} [|sol2_val|sol2_val] //.
    by exists (2%:R); rewrite sol2_val.
  by exists (3%:R); rewrite sol2_val.
case: (eqVneq ((sol p s)..[4]) 0) => [sol4e0|sol4ne0]; last first.
  by have /sol423_val/eqP := sge0; rewrite mulrI_eq0 => [/eqP|]//; apply/lregP.
have /sol432_val' := sge0.
rewrite sol4e0 expr0n /= mul0r subr0.
case: (eqVneq ((sol p s)..[3]) 0) => [sol3e0|sol3ne0].
  move=> _; move: circsol; rewrite sol3e0 expr0n /= addr0.
  rewrite -(expr1n R 2) => /eqP; rewrite eqf_sqr=> /orP [] /eqP->.
    by exists 1.
  by exists 0.
move=> /eqP; rewrite mulrI_eq0; last exact/lregP.
by rewrite mulrI_eq0=> [/eqP|] //; apply/lregP.
Qed.

Lemma En0_sol3_const p :
  limS sol K p -> E p != 0 -> forall t, 0 <= t -> (sol p t)..[3] = p..[3].
Proof.
move=> limSKp Epn0 t tge0.
have circsol s : 0 <= s -> p..[2] ^+ 2 + (sol p s)..[3] ^+ 2 = 1.
  move=> sge0; rewrite -(En0_sol2_const limSKp Epn0 sge0).
  suff [] : K (sol p s) by [].
  exact/subset_limSK_K/limSKinvar.
set h := fun i : 'I_2 => if i == 0 then Num.sqrt (1 - p..[2] ^+ 2)
                                   else - (Num.sqrt (1 - p..[2] ^+ 2)).
rewrite -[p in RHS]sol0.
apply: (@continuous_finimage_cst (fun t => (sol p t)..[3]) _ h) tge0.
  move=> s sge0; apply: (@differentiable_continuous _ R^o R^o).
  have Kp : K p by apply: subset_limSK_K.
  have [_ /(_ _ sge0) sol_ats]:= sol_is_sol sol0 solP Kp.
  exact/derivable1_diffP.
move=> s sge0.
suff : (sol p s)..[3] ^+ 2 == (Num.sqrt (1 - p..[2] ^+ 2)) ^+2.
  by rewrite eqf_sqr => /orP [/eqP ?|/eqP ?]; [exists 0|exists 1].
have /circsol <- := sge0.
by rewrite -addrA addrCA addrA addrK sqr_sqrtr // sqr_ge0.
Qed.

Lemma En0_sol4_eq0 p :
  limS sol K p -> E p != 0 -> forall t, 0 <= t -> (sol p t)..[4] = 0.
Proof.
move=> limSKp Epn0 t tge0.
have Kp : K p by apply: subset_limSK_K.
have [_ /(_ _ tge0) sol't] := sol_is_sol sol0 solP Kp.
have : (sol p t)..[3] * (sol p t)..[4] == 0.
  rewrite -oppr_eq0 -mulNr; apply/eqP.
  apply (is_derive_nneg_eq (En0_sol2_const limSKp Epn0) tge0); last first.
    exact: is_derive_cst.
  by apply: is_derive_eq; rewrite mxE.
rewrite mulf_eq0 => /orP [] /eqP // sol3eq0.
have /eqP : (sol p t)..[2] * (sol p t)..[4] = 0.
  apply (is_derive_nneg_eq (En0_sol3_const limSKp Epn0) tge0); last first.
    exact: is_derive_cst.
  by apply: is_derive_eq; rewrite mxE.
rewrite mulf_eq0 => /orP [] /eqP // sol2eq0.
have [] : K (sol p t) by apply/Kinvar.
by rewrite sol3eq0 sol2eq0 expr0n /= addr0 => /eqP; rewrite eq_sym oner_eq0.
Qed.

Lemma En0_sol3_eq0 p t :
  limS sol K p -> E p != 0 -> 0 <= t -> (sol p t)..[3] = 0.
Proof.
move=> limSKp Epn0 tge0; rewrite En0_sol3_const => //.
case: (eqVneq (p..[3]) 0) => // p3n0.
suff : (Fpendulum (sol p 0))..[4] = 0.
  rewrite Fpendulum4E // sol0 => /eqP; rewrite mulrI_eq0; last exact/lregP.
  by move/eqP.
apply (is_derive_nneg_eq (En0_sol4_eq0 limSKp Epn0) (lexx 0)); last first.
  exact: is_derive_cst.
have Kp : K p by apply: subset_limSK_K.
have [_ /(_ _ (lexx 0))] := sol_is_sol sol0 solP Kp.
exact: is_derive_component.
Qed.

Lemma En0_sol2_eq1 p t :
  limS sol K p -> E p != 0 -> 0 <= t -> (sol p t)..[2] = 1.
Proof.
move=> limSKp Epn0 tge0.
have [] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
rewrite En0_sol3_eq0 // expr0n /= addr0 -{1}(expr1n R 2).
move/eqP; rewrite eqf_sqr => /orP [] /eqP // sol2_eqN1 _.
suff : `|E (sol p t)| < 2 * m%:num * g%:num * l%:num.
  rewrite /E sol1_eq0 // En0_sol4_eq0 // expr0n /= !mulr0 !addr0 mulr0 add0r.
  rewrite sol2_eqN1 -opprD mulrN normrN mulrC !mulrA mulrAC.
  by rewrite -(natrD _ 1 1) addn1 ltr_norml ltxx andbF.
rewrite -[X in _ < X]ger0_norm // -ltr_sqr ?nnegrE // -!normrX.
do 2 rewrite ger0_norm ?sqr_ge0 //.
suff : 2 * (V (sol p t)) / ke%:num < (2 * m%:num * g%:num * l%:num) ^+ 2.
  apply: le_lt_trans.
  rewrite -mulrA -ler_pdivrMl // ler_pdivlMr // mulrC mulrA.
  by rewrite /V -addrA lerDl addr_ge0 // pmulr_rge0 // sqr_ge0.
rewrite ltr_pdivrMr // -ltr_pdivlMl // mulrC [_ * ke%:num]mulrC.
have /lt_le_trans : V (sol p t) < B.
  have [_ Vsolp_s] : K (sol p t) by apply/subset_limSK_K/limSKinvar.
  exact: le_lt_trans k0_valid.
rewrite /B; apply; apply: ler_pM => //; apply: ler_pM => //.
by rewrite lerXn2r // ?nnegrE // ge_min lexx orbC.
Qed.

Lemma subset_limSK_homoclinic_orbit : limS sol K `<=` homoclinic_orbit.
Proof.
move=> p limSKp; rewrite homoclinicE; case: (eqVneq (E p) 0) => [Ep0|Epn0].
  have := sol1_eq0 limSKp (lexx _); rewrite sol0 => p10.
  have := Efctrl_psol0_eq0 limSKp (lexx _).
  rewrite sol0 Ep0 mulr0 mul0r add0r => /eqP.
  by rewrite mulrI_eq0 => [/eqP|] //; apply/lregP.
suff Ep0 : E p == 0 by move: Epn0; rewrite Ep0.
rewrite /E -[p]sol0 sol1_eq0 // En0_sol4_eq0 // En0_sol2_eq1 // subrr expr0n /=.
by rewrite !mulr0 !addr0 mulr0.
Qed.

Lemma cvg_to_homoclinic_orbit p : K p ->
  sol p @ +oo --> (homoclinic_orbit : set [the pseudoMetricType _ of U]).
Proof.
move=> Kp A [_/posnumP[e] hoe_A]; apply: cvg_to_limS K_compact Kinvar _ Kp _ _.
exists e%:num => //= q [r /subset_limSK_homoclinic_orbit hor re_q].
by apply: hoe_A; exists r.
Qed.

End System.
