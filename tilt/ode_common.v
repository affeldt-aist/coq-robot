From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval.
From mathcomp Require Import poly generic_quotient ring_quotient.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets.
From mathcomp Require Import constructive_ereal.
From mathcomp Require Import functions reals interval_inference topology.
From mathcomp Require Import prodnormedzmodule tvs normedtype landau.
From mathcomp Require Import ereal sequences derive numfun measure realfun.
From mathcomp Require Import lebesgue_measure lebesgue_integral ftc.
Require Import tilt_mathcomp.

(**md**************************************************************************)
(* # Preparation steps to ode_contfun.v                                       *)
(*                                                                            *)
(* ```                                                                        *)
(*     contseg a b := pred type for functions continuous on [a; b]            *)
(*   pre_infty_norm f == sup (|f|(K))                                         *)
(*                    f has type {fun K >-> [set: _]}                         *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Lemma in_eq_derive1 {R : numFieldType} {W : normedModType R} (A : set R) (g h : R -> W) :
  open A -> {in A, g =1 h} -> {in A, g^`() =1 h^`()}.
Proof.
move=> oA gh x xcd.
rewrite !derive1E; apply: near_eq_derive => //.
near do apply: gh.
exact: open_in_nearW _ xcd.
Unshelve. all: by end_near. Qed.

(* TODO: PR to MCA *)
Lemma cst_is_fun {T1 T2} (A : set T1) x : @isFun T1 T2 A [set: T2] (cst x).
Proof. by constructor. Qed.

HB.instance Definition _ {T1 T2} (A : set T1) x := @cst_is_fun T1 T2 A x.

Lemma seg_nonempty {R : realType} (c d : R) : c <= d -> `[c, d] !=set0.
Proof.
move => h.
exists c.
by rewrite /=in_itv/= lexx.
Qed.

(* TODO: PR *)
Lemma restrict0 [T : Type] (K : realFieldType) (D : set T) :
  (cst 0 : T -> K) \_ D = cst 0.
Proof.
by apply/funext => x/=; rewrite patchE; case: ifPn.
Qed.

(* TODO: rewrite rmorphD should work declare patch as a morphism:
  erestrictD, erestrictM,  *)
Lemma restrictD [T : pointedType] [R : realFieldType] (D : set T) (f g : T -> R) :
  (f \+ g)%R \_ D = (f \_ D \+ g \_ D)%R.
Proof.
rewrite /patch.
apply/funext => /= x.
case: ifPn => xD.
  by rewrite /GRing.add_fun xD.
by rewrite /GRing.add_fun (negbTE xD)// addr0.
Qed.

Lemma restrictM [T : pointedType] [R : realFieldType] (D : set T) (f g : T -> R) :
  (f \* g)%R \_ D = (f \_ D \* g \_ D)%R.
Proof.
rewrite /patch.
apply/funext => /= x.
case: ifPn => xD.
  by rewrite /GRing.mul_fun xD.
by rewrite /GRing.mul_fun (negbTE xD)// mulr0.
Qed.

(* TODO: now in MathComp-Analysis master *)
Section continuous_within_itvP.
Context {R : realType}.
Context {U : normedModType R}.

Implicit Type f : R -> U.

Let near_at_left (a : itv_bound R) b f eps : (a < BLeft b)%O -> 0 < eps ->
  {within [set` Interval a (BRight b)], continuous f} ->
  \forall t \near b^'-, `|f b - f t| < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/(@cvgrPdist_lt _ _)/(_ _ eps_gt0) : (cf b).
rewrite /dnbhs/= near_withinE !near_simpl /prop_near1 /nbhs/=.
rewrite -nbhs_subspace_in//.
  rewrite /= in_itv/= lexx andbT.
  by move: a ab {cf} => [[a|a]/=|[|]//]; rewrite bnd_simp// => /ltW.
rewrite /within/= near_simpl; apply: filter_app.
move: a ab {cf} => [a0 a/= /[!bnd_simp] ab|[_|//]].
- exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  apply=> //; rewrite ?lt_eqF// !in_itv/= (ltW ac)/= andbT; move: cba => /=.
  rewrite gtr0_norm ?subr_gt0// ltrD2l ltrNr opprK => {}ac.
  by case: a0 => //=; exact/ltW.
- by exists 1%R => //= c cb1 + bc; apply; rewrite ?lt_eqF ?in_itv/= ?ltW.
Qed.

Let near_at_right a (b : itv_bound R) f eps : (BRight a < b)%O -> 0 < eps ->
  {within [set` Interval (BLeft a) b], continuous f} ->
  \forall t \near a^'+, `|f a - f t| < eps.
Proof.
move=> ab eps_gt0 cf.
move/continuous_withinNx/(@cvgrPdist_lt _ _)/(_ _ eps_gt0) : (cf a).
rewrite /dnbhs/= near_withinE !near_simpl// /prop_near1 /nbhs/=.
rewrite -nbhs_subspace_in//.
  rewrite /= in_itv/= lexx//=.
  by move: b ab {cf} => [[b|b]/=|[|]//]; rewrite bnd_simp// => /ltW.
rewrite /within/= near_simpl; apply: filter_app.
move: b ab {cf} => [b0 b/= /[!bnd_simp] ab|[//|_]].
- exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  apply=> //; rewrite ?gt_eqF// !in_itv/= (ltW ac)/=; move: cba => /=.
  rewrite ltr0_norm ?subr_lt0// opprB ltrD2r.
  by case: b0 => //= /ltW.
- by exists 2%R => //= c ca1 + ac; apply; rewrite ?gt_eqF ?in_itv/= ?ltW.
Qed.

(* NB: PR  *)
Lemma continuous_within_itvP_g a b f : a < b ->
  {within `[a, b], continuous f} <->
  [/\ {in `]a, b[, continuous f}, f @ a^'+ --> f a & f @b^'- --> f b].
Proof.
move=> ab; split=> [abf|].
  split; [|apply/(@cvgrPdist_lt _ _) => eps eps_gt0 /=..].
  - rewrite -continuous_open_subspace; first exact: interval_open.
    by move: abf; exact/continuous_subspaceW/subset_itvW.
  - by apply: near_at_right => //; rewrite bnd_simp.
  - by apply: near_at_left => //; rewrite bnd_simp.
case=> ctsoo ctsL ctsR; apply/subspace_continuousP => x /andP[].
rewrite !bnd_simp/= !le_eqVlt => /predU1P[<-{x}|ax] /predU1P[|].
- by move/eqP; rewrite lt_eqF.
- move=> _; apply/(@cvgrPdist_lt _ _) => eps eps_gt0 /=.
  move/(@cvgrPdist_lt _ _)/(_ _ eps_gt0): ctsL; rewrite /at_right !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0// => c cba + ac.
  have : a <= c by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> ->; apply/(@cvgrPdist_lt _ _) => eps eps_gt0 /=.
  move/(@cvgrPdist_lt _ _)/(_ _ eps_gt0): ctsR; rewrite /at_left !near_withinE.
  apply: filter_app; exists (b - a); rewrite /= ?subr_gt0 // => c cba + ac.
  have : c <= b by move: ac => /andP[].
  by rewrite le_eqVlt => /predU1P[->|/[swap] /[apply]//]; rewrite subrr normr0.
- move=> xb; have aboox : x \in `]a, b[ by  rewrite inE /= !in_itv/= ax.
  rewrite within_interior; last exact: ctsoo.
  rewrite inE in aboox.
  suff : `]a, b[ `<=` interior `[a, b] by exact.
  by rewrite -open_subsetE; [exact: interval_open|exact: subset_itvW].
Qed.

End continuous_within_itvP.

Lemma within_continuous_comp_norm {R : realType} {U : normedModType R} (K : set R) (f : R -> U) :
  {within K, continuous fun x => f x} ->
  {within K, continuous fun x => `|f x|}.
Proof.
move=> H.
apply: within_continuous_comp => // y.
rewrite inE/= => -[x Kx <-].
exact: norm_continuous.
Qed.

Lemma lipschitzW {R : realType} {T U W : normedModType R} (A B : set T) C (f : T -> U -> W) k :
  A `<=` B -> {in B, forall x, k.-lipschitz_C (f x)} -> {in A, forall x, k.-lipschitz_C (f x)}.
Proof.
move=> AB H x xA.
apply: H.
by apply/mem_set/AB/set_mem.
Qed.

(* NB: why is in1_subset_itv so specialized?! *)

Section lip_implies_cont.
Context {R : realType}.
Variables (f : R -> R -> R) (a t1 : R).
Hypothesis a1 : a <= t1.
Variable k : R.
Variables (u0 : R) (r : {posnum R}).
Let B := closed_ball u0 r%:num.

Hypothesis lip2 : {in `[a, t1]%R, forall x, k.-lipschitz_B (f x)}.

Lemma lipschitz_within_continuous : {in `[a, t1]%R, forall x, {within B, continuous f x}}.
Proof.
move=> x xa1.
rewrite [B]closed_ball_itv//.
apply/continuous_within_itvP; first by rewrite ltrD2l gtrN.
split.
- move=> y ya1.
  move: (xa1); have := @lip2 x => /[apply] kfx.
  rewrite /continuous_at.
  apply/cvgrPdist_le => /= e e0.
  near=> y'.
  move: kfx => /(_ (y, y'))/=.
  have By : B y.
    rewrite /B closed_ball_itv//=.
    exact: subset_itv_oo_cc ya1.
  have By' : B y'.
    rewrite /B closed_ball_itv//=.
    rewrite in_itv/=; apply/andP; split.
      near: y'.
      exists (y - (u0 - r%:num)).
        by move: ya1; rewrite in_itv/= -subr_gt0 => /andP[].
      move=> z/=.
      by rewrite ltr_distlC opprB addrCA subrr addr0 => /andP[/ltW].
    near: y'.
    exists ((u0 + r%:num) - y).
      by move: ya1; rewrite in_itv/= -(subr_gt0 y) => /andP[].
    move=> z/=.
    rewrite ltr_distlC => /andP[_].
    by rewrite addrCA subrr addr0 => /ltW.
  move=> /(_ (conj By By'))/le_trans; apply.
  near: y'.
  have [k0|k0] := ltP 0 k; last first.
    near=> y'.
    by rewrite (le_trans _ (ltW e0))// mulr_le0_ge0.
  near=> y'.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  exists (e / k).
  by rewrite divr_gt0.
  by move=> z/= => /ltW.
- apply/cvgrPdist_le => /= e e0.
  have [k0|k0] := ltP 0 k; last first.
    (* TODO: clean, bad dup *)
    near=> y'.
    move: (xa1); have := @lip2 x => /[apply].
    move=> /(_ (u0 - r%:num, y'))/=.
      have Bu0r : B (u0 - r%:num).
        rewrite /B closed_ball_itv//=.
        by rewrite bound_itvE lerD2l gerN.
      have By' : B y'.
        rewrite /B closed_ball_itv//=.
        rewrite in_itv/=; apply/andP; split => //.
        near: y'.
        exists r%:num => //=.
        move=> z/=.
        rewrite ltr_distlC.
        rewrite subrK => /andP[_ /ltW + _] => /le_trans; apply.
        by rewrite lerDl.
    move=> /(_ (conj Bu0r By'))/le_trans; apply.
    by rewrite (le_trans _ (ltW e0))// mulr_le0_ge0.
  near=> y'.
  move: (xa1); have := @lip2 x => /[apply].
  move=> /(_ (u0 - r%:num, y'))/=.
    have Bu0r : B (u0 - r%:num).
      rewrite /B closed_ball_itv//=.
      by rewrite bound_itvE lerD2l gerN.
    have By' : B y'.
      rewrite /B closed_ball_itv//=.
      rewrite in_itv/=; apply/andP; split => //.
      near: y'.
      exists r%:num => //=.
      move=> z/=.
      rewrite ltr_distlC.
      rewrite subrK => /andP[_ /ltW + _] => /le_trans; apply.
      by rewrite lerDl.
  move=> /(_ (conj Bu0r By'))/le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  exists (e / k) => /=; first by rewrite divr_gt0.
  by move=> z/= => /ltW.
- apply/cvgrPdist_le => /= e e0.
  have [k0|k0] := ltP 0 k; last first.
    (* TODO: clean, bad dup *)
    near=> y'.
    move: (xa1); have := @lip2 x => /[apply].
    move=> /(_ (y', u0 + r%:num))/=.
      have By' : B y'.
        rewrite /B closed_ball_itv//=.
        rewrite in_itv/=; apply/andP; split => //.
        near: y'.
        exists r%:num => //=.
        move=> z/=.
        rewrite ltr_distlC addrK => /andP[/ltW + _ _].
        rewrite lerBlDl => /le_trans; apply.
        by rewrite lerDr.
      have Bu0r : B (u0 + r%:num).
      rewrite /B closed_ball_itv//=.
      by rewrite bound_itvE lerD2l gerN.
    move=> /(_ (conj By' Bu0r)).
    rewrite distrC.
    move=> /le_trans; apply.
    by rewrite (le_trans _ (ltW e0))// mulr_le0_ge0.
  near=> y'.
  move: (xa1); have := @lip2 x => /[apply].
  move=> /(_ (y', u0 + r%:num))/=.
    have By' : B y'.
      rewrite /B closed_ball_itv//=.
      rewrite in_itv/=; apply/andP; split => //.
      near: y'.
      exists r%:num => //=.
      move=> z/=.
      rewrite ltr_distlC addrK => /andP[/ltW + _ _].
      rewrite lerBlDl => /le_trans; apply.
      by rewrite lerDr.
    have Bu0r : B (u0 + r%:num).
    rewrite /B closed_ball_itv//=.
    by rewrite bound_itvE lerD2l gerN.
  move=> /(_ (conj By' Bu0r)).
  rewrite distrC.
  move=> /le_trans; apply.
  rewrite -ler_pdivlMl// mulrC.
  near: y'.
  exists (e / k) => /=; first by rewrite divr_gt0.
  move=> z/= => /ltW.
  by rewrite distrC.
Unshelve. all: end_near. Qed.

End lip_implies_cont.

(* NB: should this be PRed or is a patch for our development? *)
Section cst_continuous_on_subspace.
Context {R : realType} {W : topologicalType}.
Variable A : set R.

Lemma cst_continuous_subspace (r : W) : {within A, continuous (cst r)}.
Proof. by apply: continuous_subspaceT; exact: cst_continuous. Qed.

HB.instance Definition _ x := isContinuous.Build (subspace A) W
  (@cst _ W x) (@cst_continuous_subspace x).

End cst_continuous_on_subspace.

(* NB: continuousFunType is defined in subspace_topology.v *)

HB.instance Definition _ (R : realType) (V : topologicalType) (A : set R) :=
  gen_eqMixin (continuousSubspaceType A [set: V]).

HB.instance Definition _ (R : realType) (V : topologicalType) (A : set R) :=
  gen_choiceMixin (continuousSubspaceType A [set: V]).

Section contseg_pred.
Context {R : realType} (K : set R) (V : topologicalType).

Definition contseg : {pred R -> V} :=
  mem [set f | squashed (@ContinuousSubspace R V K [set: V] f)].
Definition contseg_key : pred_key contseg. Proof. exact. Qed.
Canonical contseg_keyed := KeyedPred contseg_key.

End contseg_pred.
Arguments contseg {R} K {V}.

Section contseg_sub.
Context {R : realType} (A : set R) {V : topologicalType}.
Notation T := (continuousSubspaceType A [set: V]).

Section Sub.
Context (f : R -> V) (fP : f \in contseg A).

Definition contseg_Sub_subproof := unsquash (set_mem fP).
#[local] HB.instance Definition _ := contseg_Sub_subproof.
Definition contseg_Sub : continuousSubspaceType A [set: V] :=
  {| ContinuousSubspace.sort := f; ContinuousSubspace.class := contseg_Sub_subproof |}.

End Sub.

Lemma contseg_rect (K : T -> Type) :
  (forall f (Pf : f \in contseg A), K (contseg_Sub Pf)) ->
  forall u : T, K u.
Proof.
move=> Ksub [f Pf].
rewrite (_ : K _  = K (contseg_Sub (mem_set (squash Pf))))//.
rewrite /contseg_Sub /contseg_Sub_subproof /= mem_setK.
rewrite /unsquash; case : cid => // /= => x _.
congr (K (ContinuousSubspace.Pack _)).
move : Pf x => [[H1] [H2]] [[K1] [K2]].
by rewrite (Prop_irrelevance H1 K1) (Prop_irrelevance H2 K2).
Qed.

Lemma contseg_valP f (Pf : f \in contseg A) : contseg_Sub Pf = f :> (_ -> _).
Proof. by []. Qed.

HB.instance Definition _ := isSub.Build _ _ T contseg_rect contseg_valP.

Lemma contseg_eqP (f g : continuousSubspaceType A [set: V]) :
  f = g <-> f =1 g.
Proof. by split=> [->//|fg]; exact/val_inj/funext. Qed.

(*
HB.instance Definition _ := [Choice of continuousSubspaceType `[a, b] [set: R] by <:].
*)

End contseg_sub.

(* TODO: generalize to any set? *)
Definition contsegN {R : realType} (K : set R) (g : R -> R) :=
  g \o -%R.
Arguments contsegN {R} _ _.

Section contsegN.
Context {R : realType}.
Variables K : set R.

Let g'fun (g : continuousSubspaceType K [set: R]) :
  set_fun (-%R @` K) setT (contsegN K g).
Proof. by constructor => x/=. Qed.

HB.instance Definition _ (g : continuousSubspaceType K [set: R]) :=
  @isFun.Build (subspace (-%R @` K)) R (-%R @` K) setT (contsegN K g) (g'fun g).

Let cg' (g : continuousSubspaceType K [set: R]) :
  {within (-%R @` K), continuous (contsegN K g)}.
Proof.
move=>/=x.
apply : cvg_comp; last by apply g.
rewrite /nbhs_subspace/=.
case : ifPn;last first.
  rewrite notin_setE /nbhs/= => h A.
  rewrite -(@nbhs_subspace_out _ _ (-x)) /=; last by move => h0 x0 ->; apply h0.
  move : h.
  apply: contra_not.
  move => Kx.
  by exists (-x); rewrite // opprK.
move => h.
have Kx : K (-x).
  move : h.
  by rewrite inE => [[y h <-]]; rewrite opprK.
apply /subspace_cvgP => //.
rewrite withinN.
by rewrite nbhs_subspace_in//=; exists (-x); rewrite // opprK.
Qed.

HB.instance Definition _ (g : continuousSubspaceType K [set: R]) :=
  isContinuous.Build _ _ (contsegN K g : subspace (-%R @` K) -> R) (@cg' g).

End contsegN.

Lemma contseg_zmod_closed {R : realType} (K : set R) (V : normedModType R) :
  zmod_closed (@contseg _ K V).
Proof.
split=> [|f g]; rewrite !inE/=.
- apply: squash.
  do 2 split => //.
  exact: cst_continuous.
- move=> /unsquash cf /unsquash cg.
  apply: squash.
  pose f' : continuousSubspaceType K setT := HB.pack f cf.
  pose g' : continuousSubspaceType K setT := HB.pack g cg.
  rewrite [f]/(f' : _ -> _).
  rewrite [g]/(g' : _ -> _).
  move: {f g cf cg} f' g' => f g.
  have isfun_fg : @isFun _ _ K setT (f \- g) by constructor.
  have iscontfun_fg : @isContinuous _ _ (f \- g).
    constructor => x.
    by apply: continuousB; exact: continuous_fun.
  by split.
Qed.

Lemma contfun_scaler_closed {R : realType} (K : set R) (V : normedModType R) :
  GRing.scaler_closed (@contseg _ K V).
Proof.
move=> r f; rewrite 2!inE/= => /unsquash[[_ cf]].
apply: squash.
split => //.
constructor => x.
apply: continuousZ; first exact: cst_continuous.
by case: cf; exact.
Qed.

Section within_continuous_lipschitz.
Context {R : realType} {U : normedModType R}.
Variables (f : R -> U -> U) (a b : R).
Variable (u0 : U) (r : {posnum R}).

Variable (g : R -> U).
Hypothesis cg : {within `[a, b], continuous g}.

Let B := closed_ball u0 r%:num.

Variable k : R.
Hypothesis k0 : k != 0.
(* properties of the function f defining the differential equation: *)
(* k-lipschitz for all t *)
Hypothesis lip2 : {in `[a, b]%R, forall x, k.-lipschitz_B (f x)}.
(* within-continuous for all y *)
Hypothesis cont1 : {in B, forall y, {within `[a, b], continuous f ^~ y}}.

Hypothesis imageg : g @` `[a, b] `<=` B.

Let within_continuous_lipschitz_at_right (ab : a < b) :
  f x (g x) @[x --> a^'+] --> f a (g a).
Proof.
apply/cvgrPdist_le => /= e e0.
have aab : a \in `[a, b]%R by rewrite bound_itvE ltW.
have e20 : 0 < e / 2 by rewrite divr_gt0.
(* use continuity in first variable *)
have c1_ineq : \forall t \near a^'+, `|f a (g a) - f t (g a)| <= e / 2.
  have : g a \in (B : set U) by apply/mem_set/imageg => /=; exists a.
  move /cont1/continuous_within_itvP_g => /(_ ab).
  move=> [_ + _].
  rewrite cvgrPdist_le /=.
  exact.
have gtd : \forall t \near a^'+, g t \in (B : set U).
  near=> t.
  apply/mem_set/imageg => /=; exists t => //.
  rewrite in_itv/=; apply/andP; split => //.
  by near: t; exact: nbhs_right_le.
(* use continuity of g *)
have cg_ineq : \forall t \near a^'+, `|g a - g t| <= `|k|^-1 * (e / 2).
  have /continuous_within_itvP_g := cg.
  move/(_ ab) => [_ + _].
  move/cvgrPdist_le => /(_  (`|k|^-1 * (e / 2)) ).
  apply.
  by rewrite mulr_gt0// invr_gt0 normr_gt0.
(* use Lipschitz continuity *)
have c2_ineq : \forall t \near a^'+, `|f t (g (a)) - f t (g t)| <= e / 2.
  near=> t.
  have td' : t \in `[a, b]%R.
    by rewrite in_itv /=; apply/andP; split=>//; rewrite ltW.
  have gNdB : B (g a) by apply: imageg => //=; exists a.
  have Bgt : B (g t) by apply: imageg => //=; exists t.
  move: lip2 => /(_ _ td').
  move /(_ (g a, g t) (conj gNdB Bgt)).
  move/le_trans; apply.
  move: k0; rewrite neq_lt => /orP[k_lt0|k_gt0].
    rewrite (@le_trans _ _ 0)//; last by rewrite divr_ge0// ltW.
    by rewrite mulr_le0_ge0// ltW.
  rewrite -ler_pdivlMl//.
  rewrite (_ : k = `|k|).
    by rewrite gtr0_norm.
  by near: t.
near=>t.
rewrite -(subrKA (f t (g a)) (f a (g a))) (le_trans (ler_normD _ _))//.
by rewrite (splitr e) lerD//; near: t.
Unshelve. all: end_near. Qed.

Let within_continuous_lipschitz_at_left (ab : a < b) :
  f x (g x) @[x --> b^'-] --> f b (g b).
Proof.
apply/cvgrPdist_le => /= e e0.
have bbab : b \in `[a, b]%R by rewrite bound_itvE ltW.
have e20 : 0 < e / 2 by rewrite divr_gt0.
have c1_ineq :  \forall t \near b^'-,  `|f b (g b) - f t (g b)| <= e / 2.
  have : g b \in (B : set U) by apply/mem_set/imageg => //=; exists b.
  move /cont1/continuous_within_itvP_g => /(_ ab).
  move=> [_ _ +].
  rewrite cvgrPdist_le /=.
  exact.
have gtd : \forall t \near b^'-, g t \in (B : set U).
  near=>t.
  apply/mem_set/imageg => /=; exists t => //.
  rewrite in_itv/=; apply/andP; split => //.
  by near: t; exact: nbhs_left_ge.
have cg_ineq : \forall t \near (b)^'-, `|g b - g t| <= `|k|^-1 * (e / 2).
  have /continuous_within_itvP_g := cg.
  move/(_ ab) => [_ _ +].
  move/cvgrPdist_le => /(_  (`|k|^-1 * (e / 2))).
  apply.
  by rewrite mulr_gt0// invr_gt0// normr_gt0.
have c2_ineq : \forall t \near (b)^'-,  `|f t (g b) - f t (g t)| <= e / 2.
  near=> t.
  have td' : t \in `[a, b]%R.
    by rewrite in_itv /=; apply/andP; split=> //; rewrite ltW.
  have gNdB : B (g b) by apply: imageg => /=; exists b.
  have Bgt : B (g t) by apply: imageg; exists t.
  move: lip2 => /(_ _  td').
  move /(_ (g b, g t) (conj gNdB Bgt)).
  move/le_trans; apply.
  move: k0; rewrite neq_lt => /orP[k_lt0|k_gt0].
    rewrite (@le_trans _ _ 0)//; last by rewrite divr_ge0// ltW.
    by rewrite mulr_le0_ge0// ltW.
  rewrite -ler_pdivlMl//.
  rewrite (_ : k = `|k|).
    by rewrite gtr0_norm.
  by near: t.
near=>t.
rewrite -(subrKA (f t (g b)) (f b (g b))) (le_trans (ler_normD _ _))//.
by rewrite (splitr e) lerD//; near: t.
Unshelve. all: end_near. Qed.

Lemma within_continuous_lipschitz :
  {within `[a, b], continuous fun x0 : R => f x0 (g x0)}.
Proof.
have [ab|] := ltP a b; last first.
  rewrite le_eqVlt => /predU1P[<-|ab].
    by rewrite set_itv1; exact: continuous_subspace1.
  by rewrite set_itv_ge ?bnd_simp -?ltNge//; exact: continuous_subspace0.
apply/continuous_within_itvP_g; [by [] | split].
- move=> x; rewrite inE /= in_itv/= => /andP[ndx dx].
  rewrite /continuous_at.
  apply/cvgrPdist_le => /= e e0.
  have gxB : g x \in (B : set U).
    apply/mem_set/imageg => /=; exists x => //.
    by rewrite in_itv/= (ltW ndx) (ltW dx).
  have H : r%:num - `|g x - u0| >= 0.
    rewrite subr_ge0 distrC.
    by move: gxB; rewrite /B closed_ballE  /closed_ball_ //= inE.
  near=> t.
  rewrite -(subrKA (f t (g x)) (f x (g x))) (le_trans (ler_normD _ _))//.
  rewrite (splitr e) lerD//.
  + near: t.
    near_simpl.
    have /cont1 : g x \in B.
      apply/mem_set/imageg => /=; exists x => //.
      by rewrite in_itv/= (ltW ndx) (ltW dx).
    move/continuous_within_itvP_g => /(_ ab).
    move=> [+ Htmp1 Htmp2].
    move/(_ x).
    rewrite /continuous_at.
    have e20 : 0 < e / 2 by rewrite divr_gt0.
    rewrite inE /= !in_itv/= ndx dx => /(_ isT).
    move/cvgrPdist_le => /(_ _ e20)[r0 /= r0_gt0 Br0].
    near=> t.
    apply: Br0 => //.
    rewrite -/(ball x r0 t).
    near: t.
    near_simpl.
    exact: (near_ball x _ r0_gt0).
  + have := @lip2 t.
    have tab : t \in `[a, b]%R.
      near: t.
      exists (Num.min (b - x) (x - a)) => /=.
        by rewrite lt_min subr_gt0 dx/= subr_gt0.
      move=> z/=.
      rewrite lt_min => /andP[H1 H2].
      rewrite in_itv/=; apply/andP; split.
        move: H2.
        by rewrite ltr_distlC subKr => /andP[/ltW].
      move: H1.
      by rewrite ltr_distlC (addrC x (b-x)) subrK => /andP[_ /ltW].
    move/(_  tab).
    move/set_mem in gxB.
    have Bgt : B (g t) by apply: (imageg) => /=; exists t.
    move/(_ (g x, g t) (conj gxB Bgt)).
    move=> /le_trans; apply.
    near: t.
    move: k0; rewrite neq_lt => /orP[k_lt0|k_gt0].
      near=> t.
      rewrite (@le_trans _ _ 0)//; last by rewrite divr_ge0// ltW.
      by rewrite mulr_le0_ge0// ltW.
    near=> t.
    rewrite -ler_pdivlMl//.
    near: t.
    move/continuous_within_itvP_g : cg => /(_ ab)[+ _ _] => /(_ x).
    rewrite inE /= in_itv/= ndx dx => /(_ isT).
    rewrite /continuous_at => /cvgrPdist_le.
    apply.
    by rewrite mulr_gt0 ?divr_gt0 ?invr_gt0//.
- exact: within_continuous_lipschitz_at_right.
- exact: within_continuous_lipschitz_at_left.
Unshelve. all: end_near. Qed.

End within_continuous_lipschitz.

Lemma compact_has_ubound {R : realType} (A : set R) : compact A -> has_ubound A.
Proof.
move=> /compact_bounded[u [_ /= uA]].
exists (u + 1) => x Ax.
by rewrite (le_trans (ler_norm x))// uA// ltrDl.
Qed.

(* TODO: PR *)
Lemma cont_within_cont_comp {R : realType} {W : normedModType R} (f : W -> R)
  (K : set R) (g : continuousSubspaceType K [set: W]) : {in g @` K, continuous f} ->
  {within K, continuous (f \o g)}.
Proof.
move=> ctf.
rewrite continuous_subspace_in => /= x Kx.
apply: continuous_comp; first exact: continuous_fun.
apply: ctf.
exact: image_f Kx.
Qed.

Lemma normr_has_sup {R : realType} {K : set R} {W : normedModType R}
    (f : continuousSubspaceType K [set: W]) : compact K ->
  K !=set0 -> has_sup [set (normr \o f) z | z in K ].
Proof.
move=> compactK [c Kc].
split; first by exists `|f c|, c.
apply/compact_has_ubound/continuous_compact => //.
by apply:cont_within_cont_comp => w wK; exact: norm_continuous.
Qed.

Definition pre_infty_norm {R : realType} (K : set R) {W : normedModType R}
  (f : {fun K >-> [set: W]}) := sup ((Num.norm \o f) @` K).

Section pre_infty_norm_lemmas.
Context {R : realType} {W : normedModType R}.
Variable K : set R.
Hypotheses (K0 : K !=set0) (compactK : compact K).
Local Notation T := (continuousSubspaceType K [set: W]).

Lemma pre_infty_norm_le (g : T) (u : R) : {in K, forall x, `| g x | <= u} ->
  pre_infty_norm g <= u.
Proof.
have [c Kc] := K0.
move=> h; rewrite /pre_infty_norm; apply: ge_sup.
  by exists `|g c|; exists c.
by move => _ [x xab] <-; apply h; rewrite inE.
Qed.

Lemma pre_infty_norm_ge (g : T) x : x \in K -> `|g x| <= pre_infty_norm g.
Proof.
move=> xK.
rewrite sup_upper_bound //=.
  by apply: normr_has_sup.
by exists x => //; exact/set_mem.
Qed.

Lemma pre_infty_norm_itv_eq (f g : T) : {in K, f =1 g} ->
  pre_infty_norm f = pre_infty_norm g.
Proof.
move=> inK.
rewrite /pre_infty_norm /=; congr (sup _).
by apply/seteqP; split; move => _ [ y ? <- ]; exists y; rewrite //= inK // inE.
Qed.

End pre_infty_norm_lemmas.

Section intermediate_lemma.
Context {R : realType}.
Variables (a b : R).
Hypothesis ab : a < b.
Variable u0 : R.
Variable r : {posnum R}.
Let B := closed_ball u0 r%:num.

(* NB: not used anymore *)
Local Lemma imageg_closure (g : R -> R) : {within `[a, b], continuous g} ->
  g @` `]a, b[ `<=` interior B -> g @` `[a, b] `<=` B.
Proof.
move => cont_g imageg _ [] x /= + <-.
rewrite in_itv /= => /andP[+ +]/=.
have /continuous_within_itvP := cont_g.
move=> /(_ ab)[]/=.
move => gcont gcontl gcontr.
have closea1 :  closed `[a, b] by exact: interval_closed.
have h0 x0 : g x0 \in (interior B : set R) -> g x0 \in B.
  rewrite /B interior_closed_ballE//.
  rewrite closed_ball_itv//.
  rewrite ball_itv 2!inE.
  exact: subset_itv_oo_cc.
case: ltgtP => [hyd|_|<-] // => _.
  case: ltgtP => [hyd'|_|->] // => _.
  apply/set_mem/h0/mem_set/imageg => /=.
  exists x => //=; rewrite in_itv /= hyd hyd' //.
  apply: (@closed_cvg  _ _ (b^'-) _ g B) => //=.
    exact: closed_ball_closed.
  near=>t.
  apply/set_mem/h0/mem_set/imageg => /=.
  exists t => //=.
  by rewrite !in_itv/=; apply/andP; split.
move => _.
apply: (@closed_cvg  _ _ (a^'+) _ g B) => //=.
  exact: closed_ball_closed.
near=>t.
apply/set_mem/h0/mem_set/imageg; exists t => //=.
by rewrite !in_itv/=; apply/andP; split.
Unshelve. all: end_near. Qed.

End intermediate_lemma.
