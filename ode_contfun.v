From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval poly.
From mathcomp Require Import generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
Require Import ode_common.

(**md**************************************************************************)
(* # ODE                                                                      *)
(*   infty_norm f := infty_norm0 (repr f)                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.
Locate continuousEP.
Module Cont_on_seg_zlmodtype.
Section cont_on_seg_zlmodtype.
Context {R : realType} {V : normedModType R} (a b : R).

HB.instance Definition _ := GRing.isZmodClosed.Build _ _
  (@cont_on_seg_zmod_closed R V a b).
Fail Check continuousFunType `[a, b] [set: V] : zmodType.

HB.instance Definition _ :=
  [SubChoice_isSubZmodule of continuousFunType `[a, b] [set: V] by <:].

Check continuousFunType `[a, b] [set: V] : zmodType.

HB.instance Definition _ := GRing.isScaleClosed.Build _ _
  (cont_on_seg a b) (@contfun_scaler_closed R V a b).

Fail Check @continuousFunType R V `[a, b] [set: V] : lmodType _.

HB.instance Definition _ :=
  [SubZmodule_isSubLmodule of continuousFunType `[a, b] [set: V] by <:].

Check continuousFunType `[a, b] [set: V] : lmodType _.

End cont_on_seg_zlmodtype.
End Cont_on_seg_zlmodtype.

(* point V does not need to be 0, so rewrite f\_K explicitly *)
Section submod_itv.
Context {R : realType} {V : normedModType R} (a b : R).
Local Notation T := (continuousFunType `[a, b] [set: V]).

Definition submod_itv (ab : a <= b) : {pred T} :=
  [pred f : T | patch 0 `[a, b] f == 0].

End submod_itv.
Arguments submod_itv {R} V {a b} ab.

Section contFun_seminorm.
Context {R : realType} {W : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.
Let K := `[a, b].
Local Notation T := (continuousFunType K [set: W]).

Import Cont_on_seg_zlmodtype.

(* NB: require Nmodule properties *)
Lemma infty_norm0_eq0 : infty_norm0 (0 : T) = 0.
Proof.
rewrite /infty_norm0 -(sup1 0); congr sup.
apply eq_set => /= z ;apply propext; split => [[x _ <- ] | ->]; rewrite ?normr0 => //.
have [c Kc] := seg_nonempty ab.
by exists c; [ | rewrite normr0 ].
Qed.

(* NB: require Nmodule properties *)
Lemma infty_norm0rMn (x : T) n : infty_norm0 (x *+ n) = infty_norm0 x *+ n.
Proof.
rewrite /infty_norm0 -sup_Mn; last exact: normr_has_sup.
rewrite image_comp/=; congr (sup _).
apply eq_imagel => z Kz /=.
rewrite -normrMn /=.
have /(congr1 (fun a => a z)) <- := natmulfctE x n.
congr (normr (_ z)).
(* This is strange *)
elim: n x => //= n IH x.
by rewrite !mulrS -IH.
Qed.

Lemma infty_norm0N (x : T) : infty_norm0 (- x) = infty_norm0 x.
Proof.
rewrite /infty_norm0; congr sup.
apply: eq_set => /= x0.
apply propext; split => [[x1 in_itv] | [x1 in_itv]] H; exists x1 =>//.
by rewrite -normrN.
by rewrite normrN.
Qed.

End contFun_seminorm.

Module Cont_on_seg_quot.
Export Cont_on_seg_zlmodtype.
Section submod_definition.
Context {R : realType} {V : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.

Lemma submod_closed_itv : submod_closed (submod_itv V ab).
Proof.
split => /=.
- rewrite inE/=; apply/funext => x.
  by rewrite /patch; case: ifPn.
- move => f u v.
  rewrite !inE => u0 v0.
  apply/funext => u1.
  rewrite /patch; case: ifPn => // u1ab.
  move: u0 v0; rewrite /patch.
  move=> /(congr1 (fun x => x u1)); rewrite u1ab => uu1.
  move=> /(congr1 (fun x => x u1)); rewrite u1ab => vu1.
  by rewrite -[LHS]/(f *: u u1 + v u1) uu1 vu1 addr0 scaler0.
Qed.

Fail Check (submod_itv V ab) : zmodClosed _.

HB.instance Definition _ :=
  GRing.isZmodClosed.Build _ _ (GRing.submod_closedB submod_closed_itv).

Check (submod_itv V ab) : zmodClosed _.

End submod_definition.

Import Quotient.

Section cont_on_seg_quotient.
Context {R : realType} {W : normedModType R} (a b : R).
Hypothesis ab : a <= b.

(*Definition eq_seg (f g : continuousFunType a b) := `[< {in `[a, b], f =1 g} >].

Let eq_seg_refl : reflexive eq_seg.
Proof. by move=> f; apply/asboolP => r. Qed.

Let eq_seg_sym : symmetric eq_seg.
Proof. by move=> f g; apply/idP/idP => /asboolP h; apply/asboolP => r /h. Qed.

(* TODO: wait for quotient *)
Let eq_seg_trans : transitive eq_seg.
Proof.
by move=> f g h /asboolP fg /asboolP gh; apply/asboolP => r rab; rewrite fg// gh.
Qed.

Canonical eq_seg_canonical :=
  EquivRel eq_seg eq_seg_refl eq_seg_sym eq_seg_trans.*)

Local Open Scope quotient_scope.

Definition quot_continuousFunType := {quot (@submod_itv _ W _ _ ab)}.
Local Notation T := quot_continuousFunType.

(* NB: ZmodQuotient is defined in ring_quotient.v *)
HB.instance Definition _ := ZmodQuotient.on T.

Definition quot_continuousFunType_to_fun (f : T) :
  (* NB: was R -> R before 2025-12-26 *)
  subspace `[a, b] -> W := repr f.
Coercion quot_continuousFunType_to_fun : T >-> Funclass.

Lemma eq_segP (f g : T) : reflect ({in `[a, b], f =1 g}) (f == g %[mod T]).
Proof.
apply/(iffP idP); rewrite eqmodE//=.
- rewrite equivE inE => fgab0 x xab.
  move/(congr1 (fun z => z x)) : fgab0.
  by rewrite /patch xab => /subr0_eq.
- move=> abfg.
  rewrite /equivE inE; apply/funext => x.
  rewrite /patch; case: ifPn => //= xab.
  rewrite !fctE.
  by apply/eqP; rewrite subr_eq0; exact/eqP/abfg.
Qed.

Lemma eqmod_on_itv f g : f = g %[mod T] -> {in `[a, b], f =1 g}.
Proof.
move=> /eqmodP + x xab.
move/set_mem => abfg0.
apply: subr0_eq.
move/(congr1 (fun z => z x)) : abfg0.
by rewrite /patch xab.
Qed.

Lemma eval_mod_on_itv f x : x \in `[a, b] -> (\pi_T f : T) x = f x.
Proof.
move => xab.
apply: (@eqmod_on_itv (repr (\pi_T f)) f) => //.
by rewrite reprK.
Qed.

End cont_on_seg_quotient.
End Cont_on_seg_quot.

Section zmodule_normed.
Context {R : realType} {W : normedModType R}.
Variables a b : R.
Hypothesis ab : a <= b.
Let K := `[a, b].

Import Cont_on_seg_quot.

Local Notation V := (@quot_continuousFunType R W a b ab).

Definition infty_norm (f : V) := infty_norm0 (repr f).

Local Open Scope quotient_scope.

Lemma ler_infty_normD (x y : V) :
  infty_norm (x + y) <= infty_norm x + infty_norm y :> R.
Proof.
rewrite /infty_norm/= -sup_sumE; [|exact: normr_has_sup..].
apply: sup_le.
- move=> A -[s sab] <-{A}.
  rewrite /down/=.
  eexists.
  split.
    exists `|repr x s|.
      by exists s.
    exists `|repr y s|.
      by exists s.
    reflexivity.
  suff  -> : repr (x + y) s = repr x s + repr y s by exact: ler_normD.
  suff : (repr (x+y) = repr x + repr y %[mod V]).
    move=> /eqmod_on_itv ->.
      by [].
    by rewrite inE.
  by rewrite Quotient.pi_add !reprK.
- exact: (normr_has_sup _ _).1.
- split.
  + exists ((normr \o repr x) a + (normr \o repr y) a)=> /=.
    exists ((normr \o repr x) a) => //; [exists a => //; rewrite in_itv/= lexx ab // | ].
    by exists ((normr \o repr y) a) => //; exists a => //; rewrite bound_itvE.
  + exists (sup [set (normr \o repr x) x0 | x0 in K] + sup [set (normr \o repr y) x0 | x0 in K]).
    apply ubP => _ [x0 xs] [y0 ys] <-.
    rewrite lerD// ub_le_sup//.
      exact: (normr_has_sup x _).2.
    exact: (normr_has_sup y _).2.
Qed.

Lemma infty_normr0_eq0 (x : V) : infty_norm x = 0 -> x = 0.
Proof.
rewrite /infty_norm /infty_norm0 /= => H.
rewrite -(reprK x) -(reprK 0).
apply/eqquotP.
rewrite Quotient.equivE inE; apply: funext => x0 /=.
rewrite /patch; case : ifPn => // /set_mem in_itv.
rewrite 2!fctE.
have -> : {in K, repr (0 : V) =1 (0 : @continuousFunType R W K setT)}.
- apply/eqmod_on_itv.
  by rewrite reprK /GRing.zero /= /Quotient.zero /= -lock.
- rewrite [LHS]subr0.
  apply/eqP; rewrite -normr_le0.
  have := sup_upper_bound (normr_has_sup x ab).
  rewrite H /ubound /=.
  apply.
  by exists x0.
- by rewrite inE.
Qed.

Lemma infty_normrMn (x : V) n : infty_norm (x *+ n) = infty_norm x *+ n.
Proof.
rewrite /infty_norm -infty_norm0rMn => //.
apply: infty_norm0_itv_eq => r rab.
suff : repr (x *+ n) = repr x *+ n %[mod V] by move=> /eqmod_on_itv ->.
elim n; [rewrite !mulr0n // reprK /GRing.zero /= /Quotient.zero /= -lock // | ].
move => n' IHn'; rewrite reprK !mulrS.
rewrite reprK in IHn'.
rewrite Quotient.pi_add reprK.
by move : IHn' <-.
Qed.

Let infty_norm_pi x : infty_norm (\pi_V x) = infty_norm0 x.
Proof.
rewrite /infty_norm /=.
have /eqmod_on_itv Heq : repr (\pi_V x) = x %[mod V] by rewrite reprK.
exact: infty_norm0_itv_eq.
Qed.

Lemma infty_normrN (x : V) : infty_norm (- x) = infty_norm x.
Proof.
rewrite -(reprK x) /GRing.opp /= -Quotient.pi_opp !infty_norm_pi /infty_norm /infty_norm0.
congr sup.
apply eq_set => /= x0.
apply propext; split => [[x1 in_itv] | [x1 in_itv]] H; exists x1 =>//.
  by rewrite -normrN.
by rewrite normrN.
Qed.
(* TODO: dev the theory of sup following the theory of ess_sup *)

Fail Check V : normedZmodType R.

HB.instance Definition _ := @Num.Zmodule_isNormed.Build R V
  infty_norm ler_infty_normD infty_normr0_eq0 infty_normrMn infty_normrN.

Lemma norm_piE x : `|\pi_V x| = infty_norm0 x.
Proof. by rewrite /Num.norm /= infty_norm_pi. Qed.

Check V : normedZmodType R.

Check (pseudoMetric_normed V) : pseudoMetricType R.
Check (pseudoMetric_normed V) : normedZmodType R.

Fail Check (pseudoMetric_normed V) : normedModType R.

End zmodule_normed.

Section V_normedtype.
Context {R : realType} {W : normedModType R} {r s : R} (rs : r <= s).

Import Cont_on_seg_quot.

Local Notation V := (@quot_continuousFunType R W r s rs).

Fail Check (pseudoMetric_normed V) : normedModType R.
HB.instance Definition _ := PseudoMetric.copy V (pseudoMetric_normed V).
HB.instance Definition _ := isPointed.Build V 0.

Lemma is_normZmod_contFunBallType : NormedZmod_PseudoMetric_eq R V.
Proof. by constructor. Qed.

Fail Check V : pseudoMetricNormedZmodType R.

HB.instance Definition _ := is_normZmod_contFunBallType.

Check V : pseudoMetricNormedZmodType R.
Import Quotient.
Open Scope quotient_scope.
Definition cont_scale (k : R) (v : V) : V := \pi_V (k *: repr v).

Let cont_scalerA a b v : cont_scale a (cont_scale b v) = cont_scale (a * b) v.
Proof.
rewrite /cont_scale.
have [-> | a0] := eqVneq a 0; first by rewrite !(scale0r, mul0r).
apply/eqmodP; rewrite /equiv_equiv/= /equiv/=.
rewrite -scalerA -scalerBr.
rewrite inE.
apply/funext => x/=.
rewrite /patch; case: ifPn => // xrs.
rewrite !fctE.
apply/eqP; rewrite scaler_eq0.
rewrite (negPf a0)/= subr_eq0.
apply/eqP.
case: piP => f.
by move/eqmod_on_itv => /(_ _ xrs) <-.
Qed.

Let cont_scale1r : left_id 1 cont_scale.
Proof.
move=> v.
rewrite /cont_scale/=.
rewrite [RHS](_ : _ = (\pi_V (repr v))%qT); last by rewrite reprK.
apply/eqmodP.
by rewrite scale1r.
Qed.

Let cont_scalerDr : right_distributive cont_scale +%R.
Proof.
move=> k b c.
rewrite /cont_scale/=.
have [-> | k0] := eqVneq k 0.
  by rewrite !scale0r piE//= add0r.
rewrite /cont_scale/=.
rewrite piE/=.
apply/eqmodP.
rewrite /equiv_equiv /equiv/=.
rewrite -scalerDr.
rewrite -scalerBr.
rewrite inE.
apply/funext => x/=.
rewrite /patch; case: ifPn => // xrs.
rewrite !fctE.
apply/eqP; rewrite scaler_eq0 (negPf k0)/=.
rewrite subr_eq0.
apply/eqP.
have := @eqmod_on_itv _ _ _ _ rs (repr (b + c)) (repr b + repr c).
move=> ->//.
rewrite pi_add//=.
by rewrite !reprK.
Qed.

Let cont_scalerDl v : {morph cont_scale^~ v: a b / a + b}.
Proof.
move=> a b.
rewrite /cont_scale piE/=.
apply/eqmodP; rewrite /equiv_equiv/= /equiv/=.
rewrite -scalerDl subrr.
rewrite inE/=.
by apply/funext => x; rewrite /patch; case: ifP.
Qed.

HB.instance Definition _ :=
  @GRing.Zmodule_isLmodule.Build R V cont_scale cont_scalerA cont_scale1r
  cont_scalerDr cont_scalerDl.

Local Lemma repr_mult l (x : V) a : a \in `[r, s] ->
  repr (l *: x) a = l *: (repr x a).
Proof.
move =>ars.
have : repr (l *: x) = l *: repr x %[mod V].
  by case: piP.
move/(@eqmod_on_itv _ _ _ _ rs (repr (l *: x)) (l *: repr x)).
by move/(_ _ ars).
Qed.

Lemma is_pmnormedZmod_contFunBallType :
  PseudoMetricNormedZmod_Lmodule_isNormedModule R V.
Proof.
constructor => l x.
rewrite /Num.norm/= /infty_norm /infty_norm0 /=.
apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ge_sup.
    exists `|repr (l *: x) r|, r => //=.
    by rewrite bound_itvE.
  move=> _/= [a ars] <-.
  rewrite repr_mult; last by rewrite inE.
  rewrite normrZ ler_wpM2l// ub_le_sup//.
    exact: (normr_has_sup _ _).2.
  by exists a.
rewrite -sup_mult => //; last by apply normr_has_sup.
apply sup_le; [ | | by apply normr_has_sup].
  move => _  [_ [x0 x0rs] <- <-].
  exists (`|l| * `|repr x x0|); split=> //=; exists x0.
    by rewrite inE.
  rewrite repr_mult; last by rewrite inE.
  by rewrite normrZ.
exists `|l *: x r|, `|repr x r|.
  by exists r => //=; rewrite bound_itvE.
by rewrite normrZ.
Qed.

HB.instance Definition _ := is_pmnormedZmod_contFunBallType.
End V_normedtype.

From mathcomp Require Import all_algebra.
From mathcomp Require Import matrix_topology.

Section completeness.
Context {R : realType} (*{n : nat}*) {W : completeNormedModType R}.
(*Let W := 'rV[R]_n.*)
Variables a b : R.
Hypothesis ab : a <= b.

Import Cont_on_seg_quot.

Notation V := (@quot_continuousFunType R W _ _ ab).

Check (V : pseudoMetricType R).
Check (V : normedModType R).

Lemma infty_norm_gt_V (f : V) e :
  `| f | <  e -> {in `[a, b], forall x : R, `|f x| < e}.
Proof.
rewrite -{1}(reprK f) norm_piE => h x xab.
exact/le_lt_trans/h/infty_norm0_ge.
Qed.

Lemma infty_norm_le_V (f : V) e :
  {in `[a, b], forall x : R, `|f x| <= e} -> `| f | <=  e.
Proof. by move => h; by rewrite -(reprK f) norm_piE infty_norm0_le. Qed.

Definition lim_fun (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  subspace `[a, b] -> W :=
  fun t => lim (@^~t @ F).

Lemma lim_fun_is_fun (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  @isFun (subspace `[a, b]) W `[a, b] [set: W] (@lim_fun F FF Fc).
Proof. by constructor. Qed.

HB.instance Definition _ F FF Fc := (@lim_fun_is_fun F FF Fc).

Lemma lim_fun_cvg_pt (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall (e : R), e > 0 -> forall t, t \in `[a,b] ->
  \forall f \near F, `|lim_fun FF Fc t - (f : V) t| <= e.
Proof.
have /(_ _ _) /cauchy_cvg /cvg_app_entourageP cvF :
    forall t : R, t \in `[a,b] ->
      cauchy (fmap (fun (h : V) => h t) (fun x : set V => nbhs F (fun x0 : V => x x0))).
  move=> t tab A /=.
  rewrite -entourage_ballE.
  move=> [e /= e0 eA].
  rewrite near_simpl -near2E near_map2.
  apply : Fc.
  rewrite -entourage_ballE.
  rewrite /nbhs/=.
  exists e => //.
  move => /= [f g] /=.
  move /infty_norm_gt_V => h.
  apply eA => /=.
  rewrite -ball_normE /ball/=.
  have <- : (f - g : V) t = (f : V) t - (g : V) t.
    rewrite -(reprK f) -(reprK g)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv.
  by apply h.
have  cvg_pt : forall (t : R),  t \in `[a,b] ->  x @[x --> fmap (fun h : V => h t) F] --> lim_fun FF Fc t.
  move => t tab.
  apply /cvg_entourageP.
  by apply cvF.
move => e e0 t tab.
move /(_ t tab) : cvg_pt.
move/cvgrPdist_le/(_ _ e0).
exact.
Qed.

Lemma lim_fun_cvg_uniform (F : set_system V) (FF: ProperFilter F) (Fc : cauchy F) :
  forall (e : R), e > 0 -> \forall f \near F, forall t, t \in `[a,b] -> `|lim_fun FF Fc t - (f : V) t| <= e.
Proof.
move => e e0.
have e20 : 0 < e/2 by rewrite divr_gt0.
have := Fc _ (entourage_ball V (PosNum e20)).
move => [/= [ha hb] /= [n1 n2]] H.
near=>f.
move=>t tab.
near F => g.
rewrite -(subrKA (g t) (lim_fun FF Fc t)).
rewrite (le_trans (ler_normD _ _))// (splitr e) lerD//.
  near: g.
  by apply lim_fun_cvg_pt;rewrite // divr_gt0.
have c1 : ball f (e/2) g.
 apply (H (f, g)); split => //=.
   by near: f.
 by near: g.
rewrite /ball /= /pseudoMetric_from_normedZmodType.ball /= in c1.
rewrite distrC.
have <- : (f - g : V) t = (f : V) t - (g : V) t.
  rewrite -(reprK f) -(reprK g)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  by rewrite !eval_mod_on_itv.
rewrite ltW //.
exact: infty_norm_gt_V.
Unshelve. all: by end_near. Qed.

Lemma lim_fun_cont (F : set_system V) (FF : ProperFilter F) (Fc : cauchy F) :
  {within `[a, b], continuous (@lim_fun F FF Fc)}.
Proof.
move: ab; rewrite le_eqVlt => /predU1P[<-| ab'].
  by rewrite set_itv1; exact: continuous_subspace1.
have H : forall (e : R), e > 0 ->forall t, t \in `[a,b] -> \forall t' \near t, t' \in `[a,b] ->
    `|lim_fun FF Fc t - lim_fun FF Fc t'| <= e.
  move => e e0 t tab.
  near F => f.
  move /(continuous_within_itvP _ ab') : (@cts_fun _ _ f ) => [mc lc rc].
  move : (tab).
  rewrite -{1}setUitv1/=; last by rewrite bnd_simp ltW.
  rewrite -{1}setU1itv/=; last by rewrite bnd_simp.
  (* split t=a, t \in ]a,b[, t=b *)
  rewrite inE/= in_itv/= => -[[->|tab']|->].
  - near=> t' => t'ab.
    rewrite -(subrKA (f a) (lim_fun FF Fc a)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      suff: forall t, t \in `[a,b] ->   `|lim_fun FF Fc t - f t| <= e / 2 by apply;rewrite inE /= in_itv/= lexx ltW //.
      near:f.
      by apply lim_fun_cvg_uniform;rewrite // divr_gt0 //.
    rewrite -(subrKA (f t') (f a)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr (e/2)) lerD//.
      move : t'ab.
      rewrite -{1}setU1itv/=; last by rewrite bnd_simp.
      rewrite inE/= in_itv/= => -[-> | ].
      rewrite subrr normr0 ltW //.
      do 2 rewrite divr_gt0 //.
      near:t'.
      move  /cvgrPdist_le : lc .
      move /( _ (e/ 2/ 2)) => [| e1 e10 eh].
      do 2 rewrite divr_gt0 //.
      exists e1 => //.
      move => x bx /andP [xa _].
      by apply eh.
    rewrite distrC.
    move : (t') t'ab.
    near:f.
    by apply lim_fun_cvg_uniform; do 2 rewrite divr_gt0 //.
  - near=> t' => t'ab.
    rewrite -(subrKA (f t) (lim_fun FF Fc t)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      move : (t) (tab).
      near:f.
      by apply lim_fun_cvg_uniform;rewrite // divr_gt0 //.
    rewrite -(subrKA (f t') (f t)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr (e/2)) lerD//.
      near:t'.
      move  /(_ _ tab'): mc.
      rewrite /continuous_at cvgrPdist_le /=.
      apply.
      do 2 rewrite divr_gt0 //.
    rewrite distrC.
    move : (t') t'ab.
    near:f.
    apply lim_fun_cvg_uniform; do 2 rewrite divr_gt0 //.
(* Todo: same as 1 *)
  - near=> t' => t'ab.
    rewrite -(subrKA (f b) (lim_fun FF Fc b)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr e) lerD//.
      suff: forall t, t \in `[a,b] ->   `|lim_fun FF Fc t - f t| <= e / 2 by apply;rewrite inE /= in_itv/= lexx ltW //.
      near:f.
      by apply lim_fun_cvg_uniform;rewrite // divr_gt0 //.
    rewrite -(subrKA (f t') (f b)).
    rewrite (le_trans (ler_normD _ _))//.
    rewrite (splitr (e/2)) lerD//.
      move : t'ab.
       rewrite -{1}setUitv1/=; last by rewrite bnd_simp ltW.
      rewrite inE/= in_itv/= => -[ | -> ];last first.
      rewrite subrr normr0 ltW //.
      do 2 rewrite divr_gt0 //.
      near:t'.
      move  /cvgrPdist_le : rc .
      move /( _ (e/ 2/ 2)) => [| e1 e10 eh].
      do 2 rewrite divr_gt0 //.
      exists e1 => //.
      move => x bx /andP [_ xb].
      by apply eh.
    rewrite distrC.
    move : (t') t'ab.
    near:f.
    by apply lim_fun_cvg_uniform; do 2 rewrite divr_gt0 //.
apply/continuous_within_itvP => //; split.
- move => t tab.
  apply/cvgrPdist_le => /= e e0.
  near=>t'.
  have : t' \in `[a,b].
    rewrite inE; apply: subset_itv_oo_cc.
    near: t'.
    apply/at_right_in_segment.
    by apply: open_itvcc_subset.
  near:t'.
  apply: H => //.
  by rewrite inE; apply subset_itv_oo_cc.
- apply/cvgrPdist_le => /= e e0.
  near=>t'.
  have : t' \in `[a,b].
    rewrite inE /= in_itv/=.
    apply/andP; split; near:t'.
      exact: nbhs_right_ge.
    exact: nbhs_right_le.
  near:t'.
  apply : cvg_at_right_filter.
    by apply cvg_id.
  apply: H => //.
  by rewrite inE/= bound_itvE// ltW.
apply/cvgrPdist_le => /= e e0.
near=>t'.
have : t' \in `[a,b].
  rewrite inE /= in_itv/=.
  apply /andP;split;near:t'.
    exact: nbhs_left_ge.
  exact: nbhs_left_le.
near:t'.
apply: cvg_at_left_filter.
  exact: cvg_id.
apply: H => //.
by rewrite inE /= bound_itvE/= ltW.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ F FF Fc :=
  isContinuous.Build (subspace `[a, b]) W
  (@lim_fun F FF Fc : subspace `[a, b] -> W) (@lim_fun_cont F FF Fc).

Fail Check (V : completeType).

Lemma cvg_V_entourageP  (F : set_system V) (FF : Filter F)
    (f : V) :
  F --> f <-> forall A, entourage A ->
              \forall g \near F, {in `[a, b], forall t : R, A (f t, (g : V) t)}.
Proof.
split => [/cvg_entourageP /= Ff A|/=Ff].
  rewrite -entourage_ballE => -[eps eps0 /= H].
  apply: (Ff [set fg : V * V| {in `[a, b], forall t : R, A (fg.1 t, fg.2 t)}]).
  exists eps => //.
  rewrite /pseudoMetric_from_normedZmodType.ball /=.
  move => /= x bx t tab.
  apply H => /=.
  rewrite -ball_normE /ball/=.
  have -> : (x.1 : V) t - (x.2 : V) t = (x.1 - x.2 :V) t.
    rewrite -(reprK x.1) -(reprK x.2)  /GRing.opp /= -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv.
  exact: infty_norm_gt_V.
apply/cvg_entourageP => /= A [e e0 sPA].
have e20 : 0 < e / 2 by rewrite divr_gt0.
have e2 : e / 2 < e by rewrite ltr_pdivrMr// mulrC ltr_pMl //= ltrDr.
near=>g.
apply: sPA.
apply/le_lt_trans/e2/infty_norm_le_V => /= t tab.
have -> : (f - g : V) t = f t - (g : V) t.
  rewrite -(reprK f) -(reprK g)  /GRing.opp /=.
  rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  by rewrite !eval_mod_on_itv.
rewrite ltW //.
suff: ball (f t) (e / 2) (g t).
  by rewrite -ball_normE /ball/=.
move: t tab.
near: g.
exact: (Ff [set xy : W * W | ball xy.1 (PosNum e20)%:num xy.2] (entourage_ball _ _)).
Unshelve. all: by end_near. Qed.

Lemma quot_cont_on_segType_cauchy_cvg (F : set_system V) :
  ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF Fc.
have /(_ _ _)/cauchy_cvg /cvg_app_entourageP cvF :
    forall t : R, t \in `[a,b] ->
    cauchy (fmap (fun (h : V) => h t) (fun x : set V => nbhs F (fun x0 : V => x x0))).
  move=> t tab A /=.
  rewrite -entourage_ballE => -[e e0 ee]; rewrite near_simpl -near2E near_map2.
  apply : Fc.
  exists e => //.
  move => /= [f g].
  move /infty_norm_gt_V => h.
  apply ee => /=.
  rewrite -ball_normE /ball_/=.
  have <- : (f - g : V) t = (f : V) t - (g : V) t.
    rewrite -(reprK f) -(reprK g)  /GRing.opp /=.
    rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
    by rewrite !eval_mod_on_itv.
  exact: h.
apply/cvg_ex; exists (pi V (@lim_fun F FF Fc : continuousFunType `[a, b] [set: W])).
apply /cvg_V_entourageP => /=.
move=> A /= entA.
near=>f.
move => t tab.
near F => g.
apply : (entourage_split (g t)) => //.
  by rewrite eval_mod_on_itv => //; first by near:g;apply: cvF.
move: (t) (tab); near: g; near: f; apply: nearP_dep; apply: Fc.
rewrite /nbhs /=.
have := entourage_split_ent entA.
rewrite -entourage_ballE => -[e e0 ee].
rewrite -entourage_ballE.
exists e => //.
move => [/= x y].
rewrite /pseudoMetric_from_normedZmodType.ball/=.
move /infty_norm_gt_V => h t tab.
apply ee => /=.
rewrite -ball_normE /ball_ /=.
rewrite distrC.
have -> : (x : V) t - (y : V) t = (x - y :V) t.
  rewrite -(reprK y) -(reprK x) /GRing.opp /=.
  rewrite -Quotient.pi_opp /GRing.add /= -Quotient.pi_add.
  by rewrite !eval_mod_on_itv.
exact: h.
Unshelve. all: by end_near. Qed.

HB.instance Definition _ := Uniform_isComplete.Build V
  quot_cont_on_segType_cauchy_cvg.

Check (V : completeType).
End completeness.

(* Section vector_contseg. *)

(* Context {R : realType}. *)
(* Variables  (a b : R). *)
(* Hypothesis ab : a <= b. *)

(* Notation V := (quot_contFunType (seg_nonempty ab) (@segment_compact R _ _)). *)

(* Definition Vn n := {ffun 'I_n -> V}. *)
(* Check V : normedZmodType R. *)
(* Check (V : pseudoMetricType R). *)
(* Check (V : normedModType R). *)
(* Check (Vn 2 : normedZmodType R). *)
(* Check (Vn 2 : pseudoMetricType R). *)
(*  Check (Vn 2 : completeType). *)
(* Fail Check (Vn 2 : normedModType R). *)
(* End vector_contseg. *)
(* (* not neeeded anymore *) *)

(* Section lip_implies_cont. *)
(* Context {R : realType}. *)
(* Local Notation mu := lebesgue_measure. *)
(* Variables (f : R -> R -> R) (t0 t1 : R). *)
(* Hypothesis t01 : t0 < t1. *)
(* Variable k : R. *)
(* Hypothesis k1 : k > 0. *)
(* Variables (u0 : R) (r : {posnum R}). *)
(* Let B := closed_ball u0 r%:num. *)

(* Hypothesis lip2 : {in `[t0, t1]%R, forall x, k.-lipschitz_B (f x)}. *)

(* Lemma cont2 : {in `[t0, t1]%R, forall x, {within B, continuous f x}}. *)
(* Proof. *)
(* move=> x xt01. *)
(* rewrite [B]closed_ball_itv//. *)
(* apply/continuous_within_itvP; first by rewrite ltrD2l gtrN. *)
(* split. *)
(* - move=> y yt01. *)
(*   move: (xt01); have := @lip2 x => /[apply] kfx. *)
(*   rewrite /continuous_at. *)
(*   apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: kfx => /(_ (y, y'))/=. *)
(*     have By : B y. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       exact: subset_itv_oo_cc yt01. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split. *)
(*         near: y'. *)
(*         exists (y - (u0 - r%:num)). *)
(*           by move: yt01; rewrite in_itv/= -subr_gt0 => /andP[]. *)
(*         move=> z/=. *)
(*         rewrite ltr_distlC. *)
(*         by rewrite opprB addrCA subrr addr0 => /andP[/ltW]. *)
(*       near: y'. *)
(*       exists ((u0 + r%:num) - y). *)
(*         by move: yt01; rewrite in_itv/= -(subr_gt0 y) => /andP[]. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC => /andP[_]. *)
(*       by rewrite addrCA subrr addr0 => /ltW. *)
(*    move=> /(_ (conj By By')). *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k). *)
(*     by rewrite divr_gt0//. *)
(*   by move=> z/= => /ltW. *)
(* - apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: (xt01); have := @lip2 x => /[apply]. *)
(*   move=> /(_ (u0 - r%:num, y'))/=. *)
(*     have Bu0r : B (u0 - r%:num). *)
(*       rewrite /B closed_ball_itv//=. *)
(*       by rewrite in_itv/= lexx/= lerD2l gerN. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split => //. *)
(*       near: y'. *)
(*       exists r%:num => //=. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC. *)
(*       rewrite subrK => /andP[_ /ltW + _] => /le_trans; apply. *)
(*       by rewrite lerDl. *)
(*    move=> /(_ (conj Bu0r By')). *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k) => /=. *)
(*     by rewrite divr_gt0//. *)
(*   by move=> z/= => /ltW. *)
(* - apply/cvgrPdist_le => /= e e0. *)
(*   near=> y'. *)
(*   move: (xt01); have := @lip2 x => /[apply]. *)
(*   move=> /(_ (y', u0 + r%:num))/=. *)
(*     have By' : B y'. *)
(*       rewrite /B closed_ball_itv//=. *)
(*       rewrite in_itv/=; apply/andP; split => //. *)
(*       near: y'. *)
(*       exists r%:num => //=. *)
(*       move=> z/=. *)
(*       rewrite ltr_distlC addrK => /andP[/ltW + _ _]. *)
(*       rewrite lerBlDl => /le_trans; apply. *)
(*       by rewrite lerDr. *)
(*     have Bu0r : B (u0 + r%:num). *)
(*       rewrite /B closed_ball_itv//=. *)
(*       by rewrite in_itv/= lexx/= lerD2l andbT gerN. *)
(*   move=> /(_ (conj By' Bu0r)). *)
(*   rewrite distrC. *)
(*   move=> /le_trans; apply. *)
(*   rewrite -ler_pdivlMl// mulrC. *)
(*   near: y'. *)
(*   (* TODO(rei): investigate *) *)
(*   exists (e / k) => /=. *)
(*     by rewrite divr_gt0//. *)
(*   move=> z/= => /ltW. *)
(*   by rewrite distrC. *)
(* Unshelve. all: end_near. Qed. *)

(* End lip_implies_cont. *)
