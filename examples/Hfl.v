(* Common libraries for HFL without modal operators *)

Local Open Scope nat_scope.

Require Import Omega.

Inductive ty: Set :=
    o: ty
  | arint: ty -> ty
  | ar: ty -> ty -> ty.
		   
Fixpoint dom (t:ty): Type :=
  match t with
     o => Prop
   | arint t' => nat -> dom t'
   | ar t1 t2 => (dom t1) -> (dom t2)
  end. 

Fixpoint ord (t:ty) {struct t}: dom t -> dom t -> Prop :=
  match t with
	    o => fun x: dom o => fun y: dom o => (x -> y)
  | arint t' =>
     fun x: dom (arint t') => fun y: dom (arint t') =>	    
          forall z:nat, ord t' (x z) (y z)
  | ar t1 t2 => 
      fun x: dom (ar t1 t2) => fun y: dom (ar t1 t2) =>	    
       forall z w:dom t1, ord t1 z z -> ord t1 w w ->
       ord t1 z w -> ord t2 (x z) (y w)
  end.
 
Definition mono (t: ty) (f:dom t) :=
    ord t f f.

(* Rewriting rules for unfolding ord just once *)
Lemma ord_exp0:
  forall x y: dom o,
    (ord o x y = (x -> y)).
Proof.
 intros; simpl; auto.
Qed.
Lemma ord_exp1:
  forall t:ty, forall x y: dom (arint t),
   (ord (arint t) x y =  (forall z:nat, ord t (x z) (y z))).
Proof.
simpl. auto.
Qed.
Lemma ord_exp2:
  forall t1 t2: ty, forall x y: dom (ar t1 t2),
   (ord (ar t1 t2) x y =
   (forall z w: dom t1, mono t1 z -> mono t1 w ->
    ord t1 z w -> ord t2 (x z) (y w))).
Proof.
 auto.
Qed.

Lemma mono_exp1:
  forall t:ty, forall x:dom (arint t),
    (mono (arint t) x = (forall z:nat, mono t (x z))).
Proof.
  auto.
Qed.
Lemma mono_exp2:
  forall t1 t2:ty, forall x:dom (ar t1 t2),
    (mono (ar t1 t2) x =
     (forall y z: dom t1, mono t1 y -> mono t1 z -> ord t1 y z ->
           ord t2 (x y) (x z))).
Proof.
  auto.
Qed.
Lemma ord_trans: 
  forall t:ty, forall x y z: dom t,
    ord t x y -> ord t y z -> ord t x z.
Proof.
induction t.
simpl; auto.

intros x y z.
repeat rewrite (ord_exp1 t).
intros. apply (IHt _ (y z0) _); auto.

intros x y z.
repeat rewrite (ord_exp2 t1 t2).
intros.
apply (IHt2 _ (y z0)); auto.
Qed.

