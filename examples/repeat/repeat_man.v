(*
({
repeat  f x = if <=(x, 0) then fin else d[((f x) (repeat f)), ((repeat f) x - 1)];
fin  = c[fin];
sub  x y k = (k y - x);
g  z x = ((repeat (sub x)) z);
input  x k = a[(k x), ((input x + 1) k)];
main  n = ((input 0) (g n));
}, (main n))

{
{q0}
{(a -> 2), (c -> 1), (d -> 2)}
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
Section repeat.
  
  Definition main_q0_0 :=
    (fun repeat'_q0_1:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) => (fun sub'_q0_1:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun g'_q0_1:(((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) -> ((nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) -> (nat -> (nat -> dom o)))) => (fun input'_q0_1:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun repeat'_q0_0:(((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o)))) => (fun sub'_q0_0:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun g'_q0_0:(((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) -> ((nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) -> ((((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o)))) -> ((nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) -> (nat -> (nat -> dom o)))))) => (fun input'_q0_0:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun n_:nat => ((((input'_q0_0  input'_q0_1)  0)  (((((g'_q0_0  repeat'_q0_1)  sub'_q0_1)  repeat'_q0_0)  sub'_q0_0)  n_))  (((g'_q0_1  repeat'_q0_1)  sub'_q0_1)  n_))))))))))).
  Definition input_q0_0 :=
    (fun input'_q0_1:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun x_:nat => (fun k_q0_0:(nat -> dom o) => (fun k_q0_1:(nat -> dom o) => ((k_q0_1  x_) \/ (((input'_q0_1  (x_ + 1))  k_q0_1)  k_q0_1)))))).
  Definition g_q0_0 :=
    (fun repeat'_q0_1:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) => (fun sub'_q0_1:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun repeat'_q0_0:(((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o)))) => (fun sub'_q0_0:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun z_:nat => (fun x_:nat => ((((repeat'_q0_0  repeat'_q0_1)  (sub'_q0_0  x_))  (sub'_q0_1  x_))  z_))))))).
  Definition sub_q0_0 :=
    (fun x_:nat => (fun y_:nat => (fun k_q0_0:(nat -> dom o) => (fun k_q0_1:(nat -> dom o) => (k_q0_0  (y_ - x_)))))).
  Definition fin_q0_0 :=
    True.
  Definition sub_q0_1 :=
    (fun x_:nat => (fun y_:nat => (fun k_q0_0:(nat -> dom o) => (fun k_q0_1:(nat -> dom o) => (k_q0_0  (y_ - x_)))))).
  Definition repeat_q0_0t :=
    (ar (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o))) (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o)))).
  Definition repeat_q0_0gen :=
    (fun repeat_q0_0:(dom  repeat_q0_0t) => (fun repeat'_q0_1:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) => (fun f_q0_0:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun f_q0_1:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun x_:nat => (((x_ <= 0) /\ fin_q0_0) \/ (~(x_ <= 0) /\ ((((f_q0_1  x_)  ((repeat'_q0_1  f_q0_1)  f_q0_1))  ((repeat'_q0_1  f_q0_1)  f_q0_1)) /\ (((repeat'_q0_1  f_q0_1)  f_q0_1)  (x_ - 1)))))))))).
  Variable repeat_q0_0 : 
    (dom  repeat_q0_0t).
  Variable Mrepeat_q0_0 : 
    mono repeat_q0_0t repeat_q0_0.
  Variable Mrepeat_q0_0gen : 
    mono (ar repeat_q0_0t repeat_q0_0t) repeat_q0_0gen.
  Variable FPrepeat_q0_0 : 
    forall arg1: ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))), forall arg2: (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))), forall arg3: (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))), forall arg4: nat, ((mono  (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o))) arg1) -> ((mono  (arint (ar (arint o) (ar (arint o) o))) arg2) -> ((mono  (arint (ar (arint o) (ar (arint o) o))) arg3) -> ((repeat_q0_0  arg1 arg2 arg3 arg4) <-> (repeat_q0_0gen  repeat_q0_0 arg1 arg2 arg3 arg4))))).
  Variable GFPrepeat_q0_0 : 
    forall arg5: (dom  repeat_q0_0t),  mono repeat_q0_0t arg5
                                    -> ord repeat_q0_0t arg5 (repeat_q0_0gen arg5)
                                    -> ord repeat_q0_0t arg5 repeat_q0_0.
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
    forall arg6: nat, forall arg7: (nat -> dom o), forall arg8: (nat -> dom o), ((mono  (arint o) arg7) -> ((mono  (arint o) arg8) -> ((input_q0_1  arg6 arg7 arg8) <-> (input_q0_1gen  input_q0_1 arg6 arg7 arg8)))).
  Variable LFPinput_q0_1 : 
    forall arg9: (dom  input_q0_1t),  mono input_q0_1t arg9
                                    -> ord input_q0_1t (input_q0_1gen arg9) arg9
                                    -> ord input_q0_1t input_q0_1 arg9.
  Definition g_q0_1t :=
    (ar (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o))) (ar (arint (arint (ar (arint o) (ar (arint o) o)))) (arint (arint o)))).
  Definition g_q0_1gen :=
    (fun g_q0_1:(dom  g_q0_1t) => (fun repeat'_q0_1:((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))) => (fun sub'_q0_1:(nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))) => (fun z_:nat => (fun x_:nat => ((((repeat_q0_0  repeat'_q0_1)  (sub_q0_0  x_))  (sub'_q0_1  x_))  z_)))))).
  Variable g_q0_1 : 
    (dom  g_q0_1t).
  Variable Mg_q0_1 : 
    mono g_q0_1t g_q0_1.
  Variable Mg_q0_1gen : 
    mono (ar g_q0_1t g_q0_1t) g_q0_1gen.
  Variable FPg_q0_1 : 
    forall arg10: ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> ((nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) -> (nat -> dom o))), forall arg11: (nat -> (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o)))), forall arg12: nat, forall arg13: nat, ((mono  (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o))) arg10) -> ((mono  (arint (arint (ar (arint o) (ar (arint o) o)))) arg11) -> ((g_q0_1  arg10 arg11 arg12 arg13) <-> (g_q0_1gen  g_q0_1 arg10 arg11 arg12 arg13)))).
  Variable LFPg_q0_1 : 
    forall arg14: (dom  g_q0_1t),  mono g_q0_1t arg14
                                    -> ord g_q0_1t (g_q0_1gen arg14) arg14
                                    -> ord g_q0_1t g_q0_1 arg14.
  Definition repeat_q0_1t :=
    (ar (arint (ar (arint o) (ar (arint o) o))) (ar (arint (ar (arint o) (ar (arint o) o))) (arint o))).
  Definition repeat_q0_1gen :=
    (fun repeat_q0_1:(dom  repeat_q0_1t) => (fun f_q0_0:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun f_q0_1:(nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))) => (fun x_:nat => (((x_ <= 0) /\ fin_q0_0) \/ (~(x_ <= 0) /\ ((((f_q0_1  x_)  ((repeat_q0_1  f_q0_1)  f_q0_1))  ((repeat_q0_1  f_q0_1)  f_q0_1)) /\ (((repeat_q0_1  f_q0_1)  f_q0_1)  (x_ - 1))))))))).
  Variable repeat_q0_1 : 
    (dom  repeat_q0_1t).
  Variable Mrepeat_q0_1 : 
    mono repeat_q0_1t repeat_q0_1.
  Variable Mrepeat_q0_1gen : 
    mono (ar repeat_q0_1t repeat_q0_1t) repeat_q0_1gen.
  Variable FPrepeat_q0_1 : 
    forall arg15: (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))), forall arg16: (nat -> ((nat -> dom o) -> ((nat -> dom o) -> dom o))), forall arg17: nat, ((mono  (arint (ar (arint o) (ar (arint o) o))) arg15) -> ((mono  (arint (ar (arint o) (ar (arint o) o))) arg16) -> ((repeat_q0_1  arg15 arg16 arg17) <-> (repeat_q0_1gen  repeat_q0_1 arg15 arg16 arg17)))).
  Variable LFPrepeat_q0_1 : 
    forall arg18: (dom  repeat_q0_1t),  mono repeat_q0_1t arg18
                                    -> ord repeat_q0_1t (repeat_q0_1gen arg18) arg18
                                    -> ord repeat_q0_1t repeat_q0_1 arg18.

  Theorem repeat:
     forall n_, (((((((((main_q0_0  repeat_q0_1)  sub_q0_1)  g_q0_1)  input_q0_1)  repeat_q0_0)  sub_q0_0)  g_q0_0)  input_q0_0)  n_).
  Proof. 
    intro.
    repeat red.
    right.
    apply FPinput_q0_1.

    unfold mono.
    simpl.
    intro.
    simpl.
    auto.
     
    unfold mono.
    simpl.
    intro.
    auto.

    red.
    left.
    simpl.
    apply FPg_q0_1.
    
    unfold repeat_q0_1t in Mrepeat_q0_1.
    auto.

    unfold sub_q0_1.
    unfold mono.
    simpl.
    auto.

    red.
    assert (mono (arint (ar (arint o) (ar (arint o) o))) (sub_q0_0 1)).
    { unfold mono.
      unfold sub_q0_0.
      rewrite ord_exp1.
      intro.
      rewrite ord_exp2.
      intros.
      rewrite ord_exp2.
      auto. }
    
    assert (mono (arint (ar (arint o) (ar (arint o) o))) (sub_q0_1 1)).
    { unfold mono.
      unfold sub_q0_1.
      rewrite ord_exp1.
      intro.
      rewrite ord_exp2.
      intros.
      rewrite ord_exp2.
      auto. }
    
    induction n_.
    * apply FPrepeat_q0_0; auto.
      red.
      left.
      split; auto.
      red.
      auto.
    * apply FPrepeat_q0_0.
      auto.
      auto.
      auto.
      red.
      right.
      split.
      ** omega.
      ** assert (forall n, S n - 1 = n).
         { intro.
           omega. }
         assert (forall n, repeat_q0_1 (sub_q0_1 1) (sub_q0_1 1) n).
         { induction n.
           * apply FPrepeat_q0_1; auto.
             red.
             left.
             split; auto.
             red.
             auto.
           * apply FPrepeat_q0_1; auto.
             red.
             right.
             split.
             ** omega.
             ** split.
                *** red.
                    rewrite H1.
                    auto.
                *** rewrite H1.
                    auto. }
         split.
         red.
         auto.
         rewrite H1.
         auto. 
  Qed.
End repeat.
