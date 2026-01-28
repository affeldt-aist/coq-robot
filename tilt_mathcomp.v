From mathcomp Require Import all_boot all_order all_algebra ring.
Require Import ssr_ext euclidean rigid frame skew.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.

Lemma sqr_inj {R : rcfType} : {in Num.nneg &, injective (fun x : R => x ^+ 2)}.
Proof.
by move=> x y x0 y0 /(congr1 (@Num.sqrt R)); rewrite !sqrtr_sqr! ger0_norm.
Qed.
