From mathcomp Require Import boot order algebra ring_tactic.
Require Import ssr_ext euclidean rigid frame skew.

(**md**************************************************************************)
(* # Additions to the MathComp library                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Lemma sqr_inj {R : rcfType} : {in Num.nneg &, injective (fun x : R => x ^+ 2)}.
Proof.
by move=> x y x0 y0 /(congr1 (@Num.sqrt R)); rewrite !sqrtr_sqr! ger0_norm.
Qed.

Lemma gerN {R : numDomainType} (x : R) : 0 <= x -> - x <= x.
Proof. by move=> x0; rewrite ge0_cp. Qed.

Definition And31 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p1.
Definition And32 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p2.
Definition And33 (P1 P2 P3 : Prop) (a : [/\ P1, P2 & P3]) :=
  let: And3 p1 p2 p3 := a in p3.
