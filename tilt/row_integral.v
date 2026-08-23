From HB Require Import structures.
From mathcomp Require Import boot order ssralg ssrnum matrix interval
  poly archimedean generic_quotient ring_quotient interval_inference
  ring_tactic field_tactic.
From mathcomp Require Import mathcomp_extra unstable boolp classical_sets
  contra functions constructive_ereal reals topology prodnormedzmodule
  tvs normedtype landau ereal sequences exp derive numfun measure
  realfun measurable_realfun lebesgue_measure lebesgue_integral ftc.
Require Import tilt_mathcomp tilt_analysis.

(**md**************************************************************************)
(* ```                                                                        *)
(* \vint[]mu_(i in D) F == integral of the function F : R -> 'rV[R]_n         *)
(* ```                                                                        *)
(******************************************************************************)

Reserved Notation "\vint [ mu ]_ ( i 'in' D ) F"
  (at level 36, F at level 36, i, D at level 60,
  format "'[' \vint [ mu ]_ ( i  'in'  D ) '/  '  F ']'").
Reserved Notation "\vint [ mu ]_ i F"
  (F at level 36, i at level 0,
    right associativity, format "'[' \vint [ mu ]_ i '/  '  F ']'").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Open Scope ring_scope.
Open Scope classical_set_scope.

Section row_Rintegral.
Context {R : realType} (d : measure_display) {T : measurableType d}.
Variable (mu : {measure set T -> \bar R}).
Variable (D : set T) (n : nat).

Definition rowRintegral (f : T -> 'rV[R]_n) : 'rV[R]_n :=
  \row_i (\int[mu]_(x in D) (f x) ord0 i).

Local Notation "\vint_ i F" :=
    (rowRintegral (fun i => F)%R) (at level 36, i at level 0,
  format "'[' \vint_ i '/  '  F ']'")  : ring_scope.

Lemma rowRintegralE (f : T -> 'rV[R]_n) i :
  (\vint_x f x) ord0 i = \int[mu]_(x in D) (f x) ord0 i.
Proof. by rewrite /rowRintegral mxE. Qed.

End row_Rintegral.

Notation "\vint [ mu ]_ ( x 'in' D ) f" :=
  (rowRintegral mu D (fun x => f)%R) : ring_scope.
Notation "\vint [ mu ]_ x f" :=
  (rowRintegral mu setT (fun x => f)%R) : ring_scope.

Section rowRintegral.
Context {R : realType}.
Let mu := @lebesgue_measure R.

Lemma rowRintegral_set1 n (f : R -> 'rV[R]_n) (r : R) :
  \vint[mu]_(x in [set r]) f x = 0.
Proof. by apply/rowP => i; rewrite !mxE Rintegral_set1. Qed.

Lemma eq_rowRintegral n (D : set R) (f : R -> 'rV[R]_n) (g : R -> 'rV[R]_n):
 {in D, f =1 g} -> \vint[mu]_(x in D) f x = \vint[mu]_(x in D) g x.
Proof.
move => h.
apply /rowP => i.
rewrite !rowRintegralE.
apply eq_Rintegral => /= x Dx.
by rewrite h.
Qed.

End rowRintegral.

Section rowRintegral_itv_split.
Local Notation mu := lebesgue_measure.

Import MeasurableR.

Lemma rowRintegral_itv_split {R : realType} {n} (F : R -> 'rV[R]_n)
    (a c b : R) :
  a <= c <= b ->
  (forall i, mu.-integrable `[a, b] (EFin \o (fun x : R => F x ord0 i))) ->
  \vint[mu]_(s in `[a, b]) F s =
  \vint[mu]_(s in `[a, c]) F s + \vint[mu]_(s in `[c, b]) F s.
Proof.
move=> /andP[t0t1 t1t2] intF.
apply/rowP=> i.
rewrite !rowRintegralE !mxE.
apply/eqP.
rewrite addrC -subr_eq.
apply/eqP.
rewrite (@Rintegral_itvB _ (fun x => F x ord0 i) (BLeft a) (BRight b) c) //=.
apply Rintegral_itvob_itvcb.
apply (@integrableS _ _ _ lebesgue_measure `[a, b] `]c, b] (EFin \o (fun x => F x ord0 i))) =>//.
exact: subset_itvScc.
Qed.

End rowRintegral_itv_split.
