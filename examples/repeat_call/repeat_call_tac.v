(*
({
repeat  f x = call(if <=(x, 0) then fin else d(((f x) (repeat f)), ((repeat f) x - 1)));
fin  = c(fin);
sub  x y k = call((k y - x));
g  z x = call(((repeat (sub x)) z));
input  x k = a((k x), ((input x + 1) k));
main  n = call(((input 0) (g n)));
}, (main n))

{
{q0}
{(a -> 2), (c -> 1), (d -> 2), (call -> 1)}
q0
{(q0, a) => {{(1, q0)}, {(2, q0)}},
(q0, d) => {{(1, q0), (2, q0)}},
(q0, c) => {{}},
(q0, call) => {{(1, q0)}}}
{(q0 -> 1)}
}
*)

Add LoadPath "../".
Require Import HflTactics.
Section repeat_call.
  
  Definition main_q0_0 :=
    (fun repeat'_q0_1:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) => (fun sub'_q0_1:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun g'_q0_1:(((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) -> ((nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) -> (nat -> (nat -> dom o)))) => (fun input'_q0_1:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun n_:nat => (((input'_q0_1  0)  (((g'_q0_1  repeat'_q0_1)  sub'_q0_1)  n_))  (((g'_q0_1  repeat'_q0_1)  sub'_q0_1)  n_))))))).
  Definition g_q0_1 :=
    (fun repeat'_q0_1:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) => (fun sub'_q0_1:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun z_:nat => (fun x_:nat => (((repeat'_q0_1  (sub'_q0_1  x_))  (sub'_q0_1  x_))  z_))))).
  Definition sub_q0_1 :=
    (fun x_:nat => (fun y_:nat => (fun k_q0_0:(nat -> dom o) => (fun k_q0_1:(nat -> dom o) => (k_q0_1  (y_ - x_)))))).
  Definition fin_q0_1 :=
    True.
  Definition input_q0_1t :=
    (arint (ar (arint o) (ar (arint o) o))).
  Definition input_q0_1gen :=
    (fun input_q0_1:(dom  input_q0_1t) => (fun x_:nat => (fun k_q0_0:(nat -> dom o) => (fun k_q0_1:(nat -> dom o) => ((k_q0_1  x_) \/ (((input_q0_1  (x_ + 1))  k_q0_1)  k_q0_1)))))).
  Variable input_q0_1 : 
    (dom  input_q0_1t).
  Variable Minput_q0_1 : 
    mono input_q0_1t input_q0_1.
  Variable Minput_q0_1gen : 
    mono (ar input_q0_1t input_q0_1t) input_q0_1gen.
  Variable FPinput_q0_1 : 
    forall arg1: nat, forall arg2: (nat -> dom o), forall arg3: (nat -> dom o), ((input_q0_1  arg1 arg2 arg3) <-> (input_q0_1gen  input_q0_1 arg1 arg2 arg3)).
  Variable LFPinput_q0_1 : 
    forall arg4: (dom  input_q0_1t),  mono input_q0_1t arg4
                                    -> ord input_q0_1t (input_q0_1gen arg4) arg4
                                    -> ord input_q0_1t input_q0_1 arg4.
  Definition repeat_q0_1t :=
    (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o))).
  Definition repeat_q0_1gen :=
    (fun repeat_q0_1:(dom  repeat_q0_1t) => (fun f_q0_0:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun f_q0_1:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun x_:nat => (((x_ <= 0) /\ fin_q0_1) \/ (~(x_ <= 0) /\ ((((f_q0_1  x_)  ((repeat_q0_1  f_q0_1)  f_q0_1))  ((repeat_q0_1  f_q0_1)  f_q0_1)) /\ (((repeat_q0_1  f_q0_1)  f_q0_1)  (x_ - 1))))))))).
  Variable repeat_q0_1 : 
    (dom  repeat_q0_1t).
  Variable Mrepeat_q0_1 : 
    mono repeat_q0_1t repeat_q0_1.
  Variable Mrepeat_q0_1gen : 
    mono (ar repeat_q0_1t repeat_q0_1t) repeat_q0_1gen.
  Variable FPrepeat_q0_1 : 
    forall arg5: (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))), forall arg6: (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))), forall arg7: nat, ((repeat_q0_1  arg5 arg6 arg7) <-> (repeat_q0_1gen  repeat_q0_1 arg5 arg6 arg7)).
  Variable LFPrepeat_q0_1 : 
    forall arg8: (dom  repeat_q0_1t),  mono repeat_q0_1t arg8
                                    -> ord repeat_q0_1t (repeat_q0_1gen arg8) arg8
                                    -> ord repeat_q0_1t repeat_q0_1 arg8.
  Load "repeat_call_split.v". 

  Theorem repeat_call:
     forall n_, (((((main_q0_0  repeat_q0_1)  sub_q0_1)  g_q0_1)  input_q0_1)  n_).
  Proof.
    intro.
    repeat hred.
    right.
    hred.
    left.
    hred.
    induction n_.
    * hauto.
    * hred.
      right.
      split.
      ** hauto.
      ** split.
         *** hred.
             hsubst (n_ - 0 = n_).
             hauto.
         *** hsubst (n_ - 0 = n_).
             hauto.
  Qed.
End repeat_call.
