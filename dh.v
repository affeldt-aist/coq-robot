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

Require Import aux angle euclidean3 skew vec_angle rot frame.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import Num.Theory.

Local Open Scope ring_scope.

(* NB: should go to euclidean3.v *)
Notation "u _|_ A" := (u <= kermx A^T)%MS (at level 8).
Notation "u _|_ A , B " := (u _|_ (col_mx A B))
 (A at next level, at level 8,
 format "u  _|_  A , B ").

Section TFrame_properties.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := TFrame.t R.

Definition xaxis (f : frame) := mkDline (TFrame.o f) (Frame.i f).
Definition yaxis (f : frame) := mkDline (TFrame.o f) (Frame.j f).
Definition zaxis (f : frame) := mkDline (TFrame.o f) (Frame.k f).

End TFrame_properties.

(* TODO: in progress, [angeles] p.141-142 *)
Section open_chain.

Variable R : rcfType.
Let point := 'rV[R]_3.
Let vector := 'rV[R]_3.
Let frame := TFrame.t R.

Record joint := mkJoint {
  joint_vaxis : vector ;
  norm_joint_vaxis : norm joint_vaxis = 1 ;                  
  joint_angle : angle R (* between to successive X axes *) }.

Record link := mkLink {
  link_length : R ; (* nonnegative, distance between to successive joint axes *)
  link_offset : R ; (* between to successive X axes *)
  link_twist : angle R (* or twist angle, between two successive Z axes *) }.
(* NB: link_offset, joint_angle, link_length, link_twist are called 
   Denavit-Hartenberg parameters *)

Definition same_direction (u v : 'rV[R]_3) : bool := 0 <= cos (vec_angle u v).

(*Definition intersection (o o' : 'rV[R]_3) (v v' : 'rV[R]_3) : option 'rV[R]_3.
Admitted.*)
(* http://math.stackexchange.com/questions/270767/find-intersection-of-two-3d-lines *)
Definition intersection (l1 l2 : line R) : option point :=
  let: (p1, u1) := (line_point l1, line_vector l1) in
  let: (p2, u2) := (line_point l2, line_vector l2) in
  if p1 \in (l2 : pred _) then Some p1
  else if p2 \in (l1 : pred _) then Some p2
  else let w : vector := p2 - p1 in
  let hw := norm (u2 *v w) in
  let h1 := norm (u2 *v u1) in
  if (hw == 0) || (h1 == 0) then
    None
  else
    let k := (hw / h1) *: u1 in
    if same_direction (u2 *v w) (u2 *v u1) then
      Some (p1 + k)
    else 
      Some (p1 - k).

Definition angle_between_lines (u1 u2 w(* direction *) : vector) : angle R :=
  if same_direction w (u1 *v u2) then
    vec_angle u1 u2
  else 
    vec_angle u2 u1.

Variable n' : nat.
Let n := n'.+1.

(* 1. Zi is the axis of the ith joint *)
Definition Z_joint_axis (joints : joint ^ n) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in 
  (joint_vaxis (joints i) == Frame.k (frames i')) ||
  (joint_vaxis (joints i) == - Frame.k (frames i')).

(* 2. Xi is the common perpendicular to Zi-1 and Zi *)
Definition X_Z (frames : frame ^ n.+1) (i : 'I_n) : bool :=
  let i' := widen_ord (leqnSn _) i in 
  let predi : 'I_n.+1 := inord i.-1 in 
  let: (o_predi, z_predi) := let f := frames predi in (TFrame.o f, Frame.k f) in
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, Frame.i f, Frame.k f) in
  if intersects (zaxis (frames predi)) (zaxis (frames i')) then
    x_i == z_predi *v z_i 
  else if colinear z_predi z_i then
    o_predi \in (xaxis (frames i') : pred _)
  else
    (x_i _|_ z_predi, z_i) && (* Xi is the common perpendicular to Zi-1 and Zi *)
    (same_direction x_i (z_i - z_predi)) (* xi is directed from zi-1 to zi *). 

(*Definition common_normal_xz (i : 'I_n) :=
  (framej (frames i.-1)) _|_ (framek (frames i)), (framei (frames i.-1)).*)
(* x_vec (frames i.-1) _|_ plane (z_vec (frames i.-1)),(z_vec (frames i)) *)

(* 3. distance Zi-1<->Zi = link length *)
Definition link_lengthP (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  link_length (links i') = distance_between_lines (zaxis (frames i')) (zaxis (frames succi)).

Definition link_offsetP (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=  
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (o_succi, x_succi) := let f := frames succi in (TFrame.o f, Frame.i f) in 
  let: (o_i, x_i, z_i) := let f := frames i' in (TFrame.o f, Frame.i f, Frame.k f) in 
  if intersection (zaxis (frames i')) (xaxis (frames succi)) is some o'_i then
    (norm (o'_i - o_i)(*the Zi-coordiante of o'_i*) == link_offset (links i')) &&
    (`| link_offset (links i') | == distance_between_lines (xaxis (frames i')) (xaxis (frames succi)))
  else
    false (* should not happen since Zi always intersects Xi.+1 (see condidion 2.) *).

Definition link_twistP (links : link ^ n.+1) (frames : frame ^ n.+1) (i : 'I_n) :=  
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: (x_succi, z_succi) := let f := frames succi in (Frame.i f, Frame.k f) in 
  let z_i := Frame.k (frames i') in 
  link_twist (links i') == angle_between_lines z_i z_succi x_succi.
  (*angle measured about the positive direction of Xi+1*)

Definition joint_angleP (joints : joint ^ n) (frames : frame ^ n.+1) (i : 'I_n) :=
  let i' := widen_ord (leqnSn _) i in
  let succi : 'I_n.+1 := inord i.+1 in
  let: x_succi := Frame.i (frames succi) in 
  let: (x_i, z_i) := let f := frames i' in (Frame.i f, Frame.i f) in 
  joint_angle (joints i) = angle_between_lines x_i x_succi z_i.
  (*angle measured about the positive direction of Zi*)

(* n + 1 links numbered 0,..., n (at least two links: the manipulator base and the end-effector)
   n joints
     the ith joint couples the i-1th and the ith link
   n + 1 frames numbered F_1, F_2, ..., F_n+1 (F_i attached to link i-1)
   *)
Record chain := mkChain {
  links : {ffun 'I_n.+1 -> link} ;
  frames : {ffun 'I_n.+1 -> frame} ;
  joints : {ffun 'I_n -> joint} ;
  (* the six conditions [angeles] p.141-142 *)
  _ : forall i, Z_joint_axis joints frames i ;
  _ : forall i, X_Z frames i ;
  _ : forall i, link_lengthP links frames i ;
  _ : forall i, link_offsetP links frames i ;
  _ : forall i, link_twistP links frames i ;
  _ : forall i, joint_angleP joints frames i 
  (* this leaves the n.+1th frame unspecified (on purpose) *)
  }.

(*
Variables chain : {ffun 'I_n -> frame * link * joint}.
Definition frames := fun i => (chain (insubd ord0 i)).1.1.
Definition links := fun i => (chain (insubd ord0 i)).1.2.
Definition joints := fun i => (chain (insubd ord0 i)).2.
*)

(*
Definition before_after_joint (i : 'I_n) : option (link * link):=
  match ltnP O i with
    | LtnNotGeq H (* 0 < i*) => Some (links i.-1, links i)
    | GeqNotLtn H (* i <= 0*) => None
  end.
 *)

End open_chain.
