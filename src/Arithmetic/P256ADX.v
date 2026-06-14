Require Import Coq.ZArith.ZArith Coq.micromega.Lia. Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Require Import Coq.Lists.List. Local Open Scope list_scope. Import ListNotations.
Require Import Crypto.Util.Tactics.

Require Import Crypto.Arithmetic.WeightStream.
Import WeightStream.Saturated.
Import Crypto.Util.ZUtil.Definitions.
Import Crypto.Util.LetIn.
Require Import Crypto.Util.Bool.

Definition p256 := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff%Z.
Definition p3 :=   0xffffffff00000001%Z.

Definition n : nat := 4.
Definition bound : positive := Z.to_pos (2^64).
Local Notation eval := (eval bound).

Lemma if_expect_true_to_if_negb {A} b (t:A) (f:unit->A) :
  if_expect_true b t f = if negb b then f tt else t.
Proof. destruct b; reflexivity. Time Qed.

Definition two_steps_of_p256_montgomery_reduction xs :=
  let x := hd 0 xs in
  let y := hd 0 (tl xs) in
  let (x't, h) := Z.mul_split (2^64) (2^32) x in
  let (x', c) := Z.add_with_get_carry_full (2^64) 0 y x't in
  product_scan_ bound (tl (tl xs)) ([(2^32, x'); (p3, x); (p3, x')] ++ repeat (0,0) (length xs - 5)) h c 0.

Definition p256_mul' x y :=
  dlet xlo := firstn 2 x in
  dlet xhi := skipn 2 x in
  dlet a := mul bound (firstn 2 x) y in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := add_mul bound a xhi y in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := condsub bound a (encode bound 4 p256) in
  firstn 4 a.

Local Notation nth i l d := (nth_default d l i).
Definition sqr4 xs : list Z :=
  let x0 := nth 0 xs 0 in let x1 := nth 1 xs 0 in let x2 := nth 2 xs 0 in let x3 := nth 3 xs 0 in
  dlet acc := product_scan_ bound [] [(0,0); (0,0); (0, 0); (x1, x2)] 0 0 0 in
  dlet acc := product_scan_ bound acc [(0, 0); (x0, x1); (x0, x2); (x0, x3); (x1, x3); (x2, x3)] 0 0 0 in
  dlet acc := add_ bound 0 acc acc in
  dlet acc := fst (add bound 0 acc (diagonal (2^64) [(x0,x0); (x1, x1); (x2, x2); (x3, x3)]))
  in acc.

Definition p256_sqr' a :=
  dlet a := sqr4 a in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := two_steps_of_p256_montgomery_reduction a in
  dlet a := condsub bound a (encode bound 4 p256) in
  firstn 4 a.

(* Versions with bounds-checking assertions *)

Definition p256_mul x y :=
  if_expect_true (2 <=? Z.of_nat (Datatypes.length x))
  (if_expect_true ((0 <=? eval x) && (eval x <? 2^256))
   (if_expect_true ((0 <=? eval y) && (eval y <? 2^256))
    (dlet xlo := firstn 2 x in
     dlet xhi := skipn 2 x in
     if_expect_true ((0 <=? eval xlo) && (eval xlo <? 2^128))
     (dlet a := mul bound (firstn 2 x) y in
      if_expect_true ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64))
      (if_expect_true ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64))
       (dlet a := two_steps_of_p256_montgomery_reduction a in
        if_expect_true ((0 <=? eval xhi) && (eval xhi <? 2^128))
        (dlet a := add_mul bound a xhi y in
         if_expect_true ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64))
         (if_expect_true ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64))
          (dlet a := two_steps_of_p256_montgomery_reduction a in
           if_expect_true (eval a <? (weight bound (Nat.max (Datatypes.length a) (Datatypes.length (encode bound 4 p256)))))
           (dlet a := condsub bound a (encode bound 4 p256) in
            if_expect_true (4 <=? Z.of_nat (Datatypes.length a))
            (if_expect_true (isbounded bound a)
             (firstn 4 a)
             (fun _ => nil))
            (fun _ => nil))
           (fun _ => nil))
          (fun _ => nil))
         (fun _ => nil))
        (fun _ => nil))
       (fun _ => nil))
      (fun _ => nil))
     (fun _ => nil))
    (fun _ => nil))
   (fun _ => nil))
  (fun _ => nil).

Lemma p256_mul'_correct x y : p256_mul x y <> nil -> p256_mul' x y = p256_mul x y.
Proof.
  cbv [p256_mul p256_mul' Let_In].
  rewrite !if_expect_true_to_if_negb.
  cbn [negb].
  break_match; congruence.
Time Qed.

Definition p256_sqr a :=
  if_expect_true (4 =? Z.of_nat (Datatypes.length a))
  (dlet a := sqr4 a in
   if_expect_true ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64))
   (if_expect_true ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64))
    (dlet a := two_steps_of_p256_montgomery_reduction a in
     if_expect_true ((0 <=? hd 0 a) && (hd 0 a <? 2 ^ 64))
     (if_expect_true ((0 <=? hd 0 (tl a)) && (hd 0 (tl a) <? 2 ^ 64))
      (dlet a := two_steps_of_p256_montgomery_reduction a in
       if_expect_true (eval a <? (weight bound (Nat.max (Datatypes.length a) (Datatypes.length (encode bound 4 p256)))))
       (dlet a := condsub bound a (encode bound 4 p256) in
        if_expect_true (4 <=? Z.of_nat (Datatypes.length a))
        (if_expect_true (isbounded bound a)
         (firstn 4 a)
         (fun _ => nil))
        (fun _ => nil))
       (fun _ => nil))
      (fun _ => nil))
     (fun _ => nil))
    (fun _ => nil))
   (fun _ => nil))
  (fun _ => nil).

Lemma p256_sqr'_correct x : p256_sqr x <> nil -> p256_sqr' x = p256_sqr x.
Proof.
  cbv [p256_sqr p256_sqr' Let_In].
  rewrite !if_expect_true_to_if_negb.
  cbn [negb].
  break_match; congruence.
Time Qed.

Lemma two_steps_of_p256_montgomery_reduction_correct xs :
  let z := eval (two_steps_of_p256_montgomery_reduction xs) in
  2^128 * z mod p256 = eval xs mod p256 /\ (
    0 <= eval xs -> 0 <= hd 0 xs < 2^64 -> 0 <= hd 0 (tl xs) < 2^64  ->
    (eval xs <= ( p256+2^129-2^97)*(2^128-1) -> 0 <= z <  p256 + p256) /\
    (eval xs <= (2^256+2^129-2^96)*(2^128-1) -> 0 <= z < 2^256 + p256) /\
    (eval xs <= (2^256-2^223)*(2^256-2^223) -> 0 <= z < 2^128 * p256)).
Proof.
  unfold two_steps_of_p256_montgomery_reduction, Let_In.
  pose proof eval_hd_tl bound xs; pose proof eval_hd_tl bound (tl xs).
  set (hd 0 xs) as x in *; set (hd 0 (tl xs)) as y in *.
  rewrite ?eval_cons in *.
  change (Z.pos bound) with (2^64)%Z in *.
  rewrite <- H0 in H. clear H0.
  rewrite Z.mul_split_correct.
  rewrite Z.add_with_get_carry_full_correct.
  rewrite ?Z.add_0_l.
  cbn [fst snd].
  rewrite eval_product_scan_.
  set (_ + _) as z.
  assert (2 ^ 128 * z = eval xs + (x + 2 ^ 64 * ((y + (2 ^ 32 * x) mod 2 ^ 64) mod 2 ^ 64)) * p256) as Hz.
  { unfold z.
    enough (eval (map (uncurry Z.mul) ([(2 ^ 32, (y + (2 ^ 32 * x) mod 2 ^ 64) mod 2 ^ 64); (p3, x); (p3, (y + (2 ^ 32 * x) mod 2 ^ 64) mod 2 ^ 64)] ++ repeat (0, 0) (length xs - 5))) = 2^32 * ((y + (2 ^ 32 * x) mod 2 ^ 64) mod 2 ^ 64) + 2^64 * p3 * x + 2^128 * p3 * ((y + (2 ^ 32 * x) mod 2 ^ 64) mod 2 ^ 64)) as ->.
    { cbv [p256 p3] in *; unfold z in *.
      change (2^64) with 18446744073709551616 in *.
      change (2^128) with 340282366920938463463374607431768211456 in *.
      change (2^32) with 4294967296 in *.
      Z.div_mod_to_equations; lia. }
    rewrite map_app, map_repeat, eval_app, eval_repeat_0.
    cbv [List.length List.map uncurry eval bound ListUtil.list_rect_arrow_nodep ListUtil.list_rect_nodep list_rect fst snd]; change (Z.pos bound) with (2^64)%Z.
    Z.div_mod_to_equations; nia. }
  clearbody z.
  set ((y + (2 ^ 32 * x) mod 2 ^ 64) mod 2 ^ 64) as x' in *.
  split; intros.
  { symmetry; erewrite <-Z.mod_add with (b := x + 2^64*x') by (cbv [p256]; nia); symmetry; f_equal; nia. }
  assert (0 <= x' < 2^64) by (unfold x'; Z.div_mod_to_equations; nia).
  assert (0 <= 2^128 * z) by (rewrite Hz; cbv [p256]; nia).
  assert (0 <= 2^384 -2^352 +2^320 + (x + 2^64 * x')*p256 < 2^128*(p256+p256)) by (cbv [p256]; nia).
  assert (0 <= (2^256+2^129-2^96)*(2^128-1) + (x + 2^64 * x')*p256 < 2^128*(p256+2^256)) by (cbv [p256]; nia).
  assert (0 <= (2^256-2^223)*(2^256-2^223) + (x + 2^64 * x')*p256 < 2^128*2^128*p256) by (cbv [p256]; nia).
  cbv [p256] in *; nia.
Time Qed.

Ltac lift_let :=
  match goal with
  | |- context G [let x := ?v in @?C x] =>
      let x := fresh x in
      pose v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g'
  | d := context G [let x := ?v in @?C x] |- _ =>
      let x := fresh x in
      pose v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g' in (value of d)
  | H: context G [let x := ?v in @?C x] |- _ =>
      let x := fresh x in
      pose v as x;
      let g' := context G [C x] in
      let g' := eval cbv beta in g' in
      change g' in H
  end.

Lemma eval_sqr4 xs : length xs = 4%nat -> 0 <= eval xs < 2^256 ->
  eval (sqr4 xs) = eval xs * eval xs.
Proof.
  intros H **. do 5 (destruct xs; try inversion H).
  cbv beta delta [sqr4 Let_In].
  repeat lift_let.
  cbv in x0, x1, x2, x3; subst x0 x1 x2 x3.
  subst y2.
  rewrite add_correct; cbn [fst]. change (Nat.max _ _) with 8%nat.
  rewrite Z.add_0_l, (eval_diagonal (Z.to_pos (2^64))).
  subst y1.
  rewrite eval_encode, eval_add_, Z.add_0_l, Z.add_diag.
  subst y0 y.
  rewrite eval_product_scan_, eval_product_scan_, ?eval_nil, ?Z.add_0_l.
  cbn [map uncurry]; rewrite ?Z.mul_0_l, ?Z.add_0_r.
  rewrite ?eval_cons, ?eval_nil in *.
  cbv [eval Saturated.eval bound weight ListUtil.list_rect_arrow_nodep ListUtil.list_rect_nodep list_rect fst snd fold_right repeat] in *.
  rewrite ?Pos2Z.inj_mul in *.
  change (Z.pos bound) with (2^64)%Z in *.
  change (Z.pos (Z.to_pos (2^64))) with (2^64)%Z in *.
  Z.div_mod_to_equations; nia.
Time Qed.


Lemma eval_p256_mul x y (z := p256_mul x y) (Hcompiles : z <> nil) :
  length x = 4%nat -> length y = 4%nat ->
  0 <= eval y < p256 ->
  2^256 * eval z mod p256 = eval x * eval y mod p256 /\
  (0 <= eval x < p256 -> 0 <= eval z < p256).
Proof.
  intros Hlenx Hleny Hy.
  pose proof firstn_skipn 2 x as H; eapply (f_equal eval) in H.

  cbv beta delta [p256_mul Let_In] in *.
  set (skipn 2 x) as xhi in *.
  set (firstn 2 x) as xlo in *.
  lift_let. lift_let.
  subst y0. subst y1.
  repeat lift_let.

  (*
  assert (Hlen_y3 : length y3 = 6%nat).
  { cbv [y3 y2 y1 y0].
    rewrite length_two_steps_7; [trivial|].
    rewrite length_add_mul_4_2; [trivial| | |trivial].
    { rewrite length_two_steps_6; [trivial|].
      cbv [mul].
      rewrite length_add_mul_0_2; [trivial| |trivial].
      { cbv [xlo]. rewrite firstn_length. rewrite Hlenx. cbv. reflexivity. } }
    { cbv [xlo]. rewrite firstn_length. rewrite Hlenx. cbv. reflexivity. }
    { cbv [xhi]. rewrite length_skipn. rewrite Hlenx. cbv. reflexivity. }
  }

  repeat match goal with
         | x := ?v |- _ =>
             let H := fresh "H" x in
             assert (x = v) as H by reflexivity;
             move H before x;
             clearbody x
         end.
  rewrite !if_expect_true_to_if_negb in *.

  eapply (f_equal eval) in Hy0.
  rewrite (eval_mul bound) in Hy0.
  
  repeat match goal with
  | H : context G [match ?x with _ => _ end] |- _ =>
      destruct x eqn:? in *; cbn [negb] in H; [congruence|]
  end.
  rewrite Bool.negb_false_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in *.

  rewrite eval_app in H.
  rewrite Hxlo in H at 2.
  rewrite !firstn_length_le in H by lia.
  progress change (Z.pos (weight bound 2)) with (2^128) in *.

  pose proof two_steps_of_p256_montgomery_reduction_correct y0 as HH.
  rewrite <-Hy1, Hy0 in HH; clear Hy1; cbv zeta in HH; case HH as [Hy1 HH'1].

  do 3 specialize (HH'1 ltac:(cbv [p256] in *; nia)).
  apply proj1 in HH'1.
  do 1 specialize (HH'1 ltac:(cbv [p256] in *; nia)).

  eapply (f_equal eval) in Hy2.
  rewrite (eval_add_mul bound) in Hy2.

  pose proof two_steps_of_p256_montgomery_reduction_correct y2 as HH.
  pose proof Hy3 as Hy3'.
  rewrite <-Hy3, Hy2 in HH; clear Hy3; cbv zeta in HH; case HH as [Hy3 HH'2].

  eapply (f_equal eval) in Hy4.
  rewrite eval_condsub, eval_encode, Z.mod_small in Hy4.
  2: { cbv. intuition congruence. }
  2: { rewrite Hlen_y3. rewrite length_encode. cbv; lia. }
  2: { rewrite Hlen_y3. cbv; lia. }
  2: { cbv. inversion 1. }
  destruct (isbounded_correct bound y4) in *; [|discriminate].

  do 3 specialize (HH'2 ltac:(cbv [p256] in *; nia)).

  eapply (f_equal eval) in Hz.
  rewrite <-e, eval_firstn_encode in Hz by lia.
  progress change (Z.pos (weight bound 4)) with (2^256) in *.
  rewrite Z.mod_small in Hz; cycle 1.
  { rewrite Hy4.
    apply proj2, proj1 in HH'2.
    do 1 specialize (HH'2 ltac:(cbv [p256] in *; nia)).
    destruct (Z.leb_spec p256 (eval y3)) in *; simpl Z.b2z in *; cbv [p256] in *; lia. }

  rewrite Hz, Hy4.
  split.
  { Modulo.push_Zmod; Modulo.pull_Zmod. rewrite Z.mul_0_r, Z.sub_0_r; trivial. }
  { intros. destruct (Z.leb_spec p256 (eval y3)) in *; simpl Z.b2z in *; cbv [p256] in *; nia. }
*)
Time Admitted.

Lemma p256_sqr_sufficient_bound : p256 < 2^256-2^223. Proof. compute. trivial. Time Qed.

Lemma eval_p256_sqr x (z := p256_sqr x) (Hcompiles : z <> nil) :
  0 <= eval x < 2^256-2^223 ->
  2^256 * eval z mod p256 = eval x * eval x mod p256 /\
  0 <= eval z < p256.
Proof.
  intros Hy.
  cbv beta delta [p256_sqr Let_In] in *.
  repeat lift_let.

  repeat match reverse goal with
         | x := ?v |- _ =>
             let H := fresh "H" x in
             (* assert (x = v) as H by exact eq_refl; (*COQBUG?: Time Qed.hangs*) *)
             assert (x = v) as H by reflexivity;
             move H before x;
             clearbody x
         end.
  rewrite !if_expect_true_to_if_negb in *.
  
  repeat match goal with
  | H : context G [match ?x with _ => _ end] |- _ =>
      destruct x eqn:? in *; cbn [negb] in H; [congruence|]
  end.

  rewrite Bool.negb_false_iff, Bool.andb_true_iff, Z.leb_le, Z.ltb_lt in *.

  eapply (f_equal eval) in Hy0.
  rewrite eval_sqr4 in Hy0 by (cbv [p256] in *; lia).

  pose proof two_steps_of_p256_montgomery_reduction_correct y as HH.
  rewrite <-Hy1, Hy0 in HH; clear Hy1; cbv zeta in HH; case HH as [Hy1 HH'1].
  do 3 specialize (HH'1 ltac:(cbv [p256 bound] in *; nia)).
  apply proj2, proj2 in HH'1.
  do 1 specialize (HH'1 ltac:(cbv [p256 bound] in *; nia)).

  pose proof two_steps_of_p256_montgomery_reduction_correct y0 as HH.
  pose proof Hy2 as Hy2'.
  rewrite <-Hy2 in HH; clear Hy2; cbv zeta in HH; case HH as [Hy2 HH'2].

  do 3 specialize (HH'2 ltac:(cbv [p256 bound] in *; nia)).
  apply proj1 in HH'2.
  do 1 specialize (HH'2 ltac:(cbv [p256 bound] in *; nia)).

  eapply (f_equal eval) in Hy3.
  rewrite eval_condsub, eval_encode, Z.mod_small in Hy3.
  2: { cbv. intuition congruence. }
  (*
  2: { trivial. }
  2: { cbv. inversion 1. }
  destruct (isbounded_correct bound y2) in *; [|discriminate].

  subst y3.
  eapply (f_equal eval) in Hz.
  rewrite <-e, eval_firstn_encode in Hz.
  2: { lia. }
  change (Z.pos (weight bound 4)) with (2^256) in *.
  rewrite Z.mod_small in Hz.
  2: { destruct (Z.leb_spec p256 (eval y1)) in *; simpl Z.b2z in *; cbv [p256] in *; lia. }

  rewrite Hz, Hy3.
  split.
  { Modulo.push_Zmod; Modulo.pull_Zmod.
    rewrite Z.mul_0_r, Z.sub_0_r.
    replace (2 ^ 256 * eval y1)
    with (2 ^ 128 * (2 ^ 128 * eval y1)) by lia.
    rewrite <-Z.mul_mod_idemp_r by (cbv; lia).
    rewrite Hy2.
    rewrite Z.mul_mod_idemp_r by (cbv; lia).
    trivial.
  }

  intros.
  destruct (Z.leb_spec p256 (eval y1)) in *; simpl Z.b2z in *; cbv [p256] in *; nia.
Time Qed.
*) Admitted.
