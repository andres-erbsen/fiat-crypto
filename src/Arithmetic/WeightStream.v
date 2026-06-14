Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Import ListNotations. Local Open Scope list_scope. Local Open Scope Z_scope.

Require Import Crypto.Language.PreExtra.
Require Import Crypto.Arithmetic.Core.

Module Pos.
  Local Open Scope positive_scope.
  Lemma prod_init x ys : fold_right Pos.mul x ys = fold_right Pos.mul 1 ys * x.
  Proof.
    revert dependent x; induction ys; cbn [fold_right]; intros; try lia.
    rewrite IHys; lia.
  Qed.
End Pos.


Module Z.
  Lemma prod_init x ys : fold_right Z.mul x ys = fold_right Z.mul 1 ys * x.
  Proof.
    revert dependent x; induction ys; cbn [fold_right]; intros; try ring.
    rewrite IHys; ring.
  Qed.

  Lemma prod_pos xs : Forall (fun x => 0 < x) xs -> 0 < fold_right Z.mul 1 xs.
  Proof. induction 1; cbn; lia. Qed.

  (* TODO: move *)
  Lemma mul_split_correct s x y :
    Z.mul_split s x y = (x * y mod s, x * y / s).
  Proof.
    rewrite (surjective_pairing (Z.mul_split _ _ _)).
    rewrite Z.mul_split_mod, Z.mul_split_div; trivial.
  Qed.

  Lemma add_with_get_carry_full_correct s c x y :
    Z.add_with_get_carry_full s c x y = ((c + x + y) mod s, (c + x + y) / s).
  Proof.
    rewrite (surjective_pairing (Z.add_with_get_carry_full _ _ _ _)).
    rewrite Z.add_with_get_carry_full_mod, Z.add_with_get_carry_full_div; trivial.
  Qed.
End Z.

Module Nat.
  Lemma max_S_r a b : Nat.max a (S b) = S (Nat.max (a-1) b). Proof. lia. Qed.
  Lemma max_S_l a b : Nat.max (S a) b = S (Nat.max a (b-1)). Proof. lia. Qed.
End Nat.

Module stream.
  Local Open Scope nat_scope.
  Notation stream := (fun T => nat -> T).
  Definition hd {T} (xs : stream T) : T := xs O.
  Definition tl {T} (xs : stream T) : stream T := fun i => xs (S i).
  Definition skipn {T} n (xs : stream T) : stream T := fun i => xs (n+i).
  Definition firstn {T} n (xs : stream T) : list T := map xs (seq 0 n).
  Definition cons {T} x (xs : stream T) : stream T :=
    fun i => match i with O => x | S i => xs i end.
  Definition prefixes {T} (xs : stream T) : stream (list T) :=
    fun i => firstn i xs.
  Definition map {A B} (f : A -> B) (xs : stream A) : stream B :=
    fun i => f (xs i).

  Lemma hd_const {T} (x : T) : hd (fun _ => x) = x. trivial. Qed.
  Lemma tl_const {T} (x : T) i : tl (fun _ => x) i = x. trivial. Qed.
  Lemma skipn_const {T} n (x : T) i : skipn n (fun _ => x) i = x. trivial. Qed.

  Definition firstn_S {T} n (xs : stream T) :
    firstn (S n) xs = List.cons (xs O) (firstn n (tl xs)).
  Proof.
    cbv [firstn]; rewrite <-cons_seq, <-seq_shift, map_cons, map_map; trivial.
  Qed.

  Definition firstn_S' {T} n (xs : stream T) :
    firstn (S n) xs = firstn n xs ++ [xs n].
  Proof. cbv [firstn]. rewrite seq_snoc, map_app; trivial. Qed.

  Lemma firstn_tl {T} n (xs : stream T) : firstn n (tl xs) = List.tl (firstn (S n) xs).
  Proof. cbn. rewrite <-seq_shift, map_map; trivial. Qed.

  Lemma firstn_add {T} i j xs : @firstn T (i + j) xs = firstn i xs ++ firstn j (skipn i xs).
  Proof.
    cbv [firstn skipn].
    rewrite seq_add, map_app; apply f_equal, eq_sym, map_seq_ext; intros; f_equal; lia.
  Qed.

  Lemma skipn_tl {T} n (xs : stream T) i : skipn n (tl xs) i = skipn (S n) xs i.
  Proof. trivial. Qed.

  Lemma skipn_skipn {T} n (xs : stream T) : skipn (S n) xs = skipn 1 (skipn n xs).
  Proof. extensionality j; cbv [skipn]; f_equal; lia. Qed.

  Lemma tl_map {A B} f xs i : tl (@map A B f xs) i = map f (tl xs) i.
  Proof. exact eq_refl. Qed.

  Lemma tl_prefixes {T} xs i :
    tl (@prefixes T xs) i = map (List.cons (hd xs)) (prefixes (tl xs)) i.
  Proof. cbv [tl prefixes map]. rewrite firstn_S; trivial. Qed.
End stream. Notation stream := stream.stream.

Module Saturated.
  Import List ListNotations.
  Import stream Coq.Init.Datatypes Coq.Lists.List List.

  Implicit Types (bound : positive).
  Local Open Scope positive_scope.

  Definition weight bound n := fold_right Pos.mul 1 (repeat bound n).

  Lemma weight_0 bound : weight bound O = 1. Proof. trivial. Qed.

  Lemma weight_1 bound : weight bound 1%nat = bound. Proof. cbn. lia. Qed.

  Lemma weight_S bound n : weight bound (S n) = bound * weight bound n.
  Proof. reflexivity. Qed.

  Lemma weight_add bound i j : weight bound (i+j) = weight bound i * weight bound j.
  Proof.
    induction i; [cbn; symmetry; apply Pos.mul_1_l|].
    replace (S i + j)%nat with (S (i + j))%nat by lia.
    rewrite !weight_S, IHi; apply Pos.mul_assoc.
  Qed.

  Lemma weight_mono_le bound i j : Nat.le i j -> weight bound i <= weight bound j.
  Proof. intros. replace j with (i+(j-i))%nat by lia; rewrite weight_add. nia. Qed.

  Local Open Scope Z_scope.
  Local Coercion Z.pos : positive >-> Z.

  Lemma mod_weight_le bound i j : Nat.le i j -> weight bound j mod weight bound i = 0.
  Proof.
    intros.
    replace j with (i+(j-i))%nat by lia; rewrite weight_add.
    rewrite Pos.mul_comm, Pos2Z.inj_mul, Z.mod_mul; lia.
  Qed.

  Definition eval bound (xs : list Z) : Z :=
    list_rect (fun _ => Z) 0 (fun x _ rec =>
      x + Z.pos bound * rec
    ) xs.

  Lemma eval_nil bound : eval bound [] = 0.
  Proof. reflexivity. Qed.

  Lemma eval_cons bound x xs :
    eval bound (cons x xs) =
    x + Z.pos bound * eval bound xs.
  Proof. reflexivity. Qed.

  Import Morphisms.

  Global Instance Proper_eval : Proper (eq==>eq==>eq)%signature eval.
  Proof. repeat intro; subst; reflexivity. Qed.

  Lemma eval_hd_tl bound xs : eval bound (hd 0 xs :: tl xs) = eval bound xs.
  Proof. case xs; intros; cbn [hd tl]; rewrite ?eval_cons, ?eval_nil; lia. Qed.

  Lemma eval_app bound xs ys :
    eval bound (xs ++ ys) =
      eval bound xs +
      weight bound (length xs) * eval bound ys.
  Proof.
    revert ys; induction xs; cbn [length app]; intros;
      rewrite ?eval_nil, ?eval_cons.
    { rewrite weight_0; ring. }
    rewrite IHxs, weight_S, Pos2Z.inj_mul; ring.
  Qed.

  Lemma eval_firstn bound n xs :
    eval bound (firstn n xs) mod weight bound n =
    eval bound xs mod weight bound n.
  Proof.
    epose proof eval_app bound _ _ as H; rewrite (firstn_skipn n xs) in H.
    rewrite H; clear H.
    rewrite firstn_length.
    case (Nat.min_dec n (length xs)) as [e|e]; rewrite e.
    { rewrite Z.mul_comm, Z.mod_add; lia. }
    rewrite ListUtil.skipn_all, eval_nil, Z.mul_0_r, Z.add_0_r by lia; trivial.
  Qed.

  Definition encode bound n (x : Z) :=
    NatUtil.nat_rect_arrow_nodep
      (fun _ : Z => @nil Z)
      (fun _ rec x_cur =>
         x_cur mod Z.pos bound :: rec (x_cur / Z.pos bound)
      ) n x.

  Lemma encode_O bound x : encode bound O x = nil. Proof. trivial. Qed.

  Lemma encode_S bound n x : encode bound (S n) x =
    x mod (Z.pos bound) :: encode bound n (x / Z.pos bound).
  Proof. reflexivity. Qed.

  Lemma length_encode bound n x : length (encode bound n x) = n.
  Proof.
    revert x; induction n; intros;
    rewrite ?encode_O, ?encode_S; cbn [length]; erewrite ?IHn; trivial.
  Qed.

  Lemma eval_encode bound n x : eval bound (encode bound n x) = x mod weight bound n.
  Proof.
    revert x; induction n; intros;
      rewrite ?encode_O, ?encode_S, ?eval_nil, ?eval_cons.
    { rewrite ?weight_0, Z.mod_1_r; trivial. }
    rewrite IHn, weight_S, Pos2Z.inj_mul.
    set (Z.pos bound) as B in *.
    symmetry; rewrite (Z.div_mod x B), Z.add_comm at 1 by lia.
    rewrite <-Z.add_mod_idemp_r, Zmult_mod_distr_l by lia.
    apply Z.mod_small; Z.div_mod_to_equations; nia.
  Qed.

  Lemma encode_add_l bound n m x :
    encode bound (n+m) x = encode bound n x ++ encode bound m (x / weight bound n).
  Proof.
    revert x; induction n; cbn [Nat.add nat_rect]; intros;
      rewrite ?encode_O, ?encode_S.
    { rewrite weight_0, Z.div_1_r. reflexivity. }
    rewrite IHn; cbn [app]; f_equal.
    f_equal; rewrite Z.div_div, weight_S, Pos2Z.inj_mul by lia; f_equal; ring.
  Qed.

  Definition forallb [A : Type] (f : A -> bool) (xs : list A) : bool :=
    list_rect (fun _ => bool) true (fun x _ rec => andb (f x) rec) xs.
  
  Lemma forallb_cons [A] f x xs : @forallb A f (cons x xs) = andb (f x) (forallb f xs).
  Proof. trivial. Qed.
  
  Definition isbounded bound x :=
    forallb
      (fun xi => (0 <=? xi) && (xi <? Z.pos bound))%bool
      x.
  
  Import Crypto.Util.ListUtil Crypto.Util.ZUtil.Modulo.
  Lemma isbounded_correct' bound x : isbounded bound x = ListUtil.list_beq _ Z.eqb (encode bound (length x) (eval bound x)) x.
  Proof.
    cbv [isbounded].
    induction x; intros; trivial.
    rewrite length_cons, encode_S, eval_cons, forallb_cons; cbn [ListUtil.list_beq].
    rewrite IHx; clear IHx.
    rewrite Z.mod_add'_full.
    rewrite Z.mul_comm, Z.div_add by lia.
    pose proof Z.mod_small_iff a bound ltac:(lia).
    destruct (Z.eqb_spec (a mod bound) a); cbn [andb];
      destruct (Z.leb_spec 0 a) as [L|L]; cbn [andb]; try lia;
      destruct (Z.ltb_spec a bound) as [R|R]; cbn [andb]; try lia.
    assert (a / bound = 0) as -> by (Z.div_mod_to_equations; nia); rewrite ?Z.add_0_l; trivial.
  Qed.
  
  Lemma isbounded_correct bound x : Bool.reflect (encode bound (length x) (eval bound x) = x) (isbounded bound x).
  Proof.
    rewrite isbounded_correct'.
    destruct ListUtil.list_beq eqn:?; constructor; [|intro HX].
    apply (ListUtil.internal_list_dec_bl _ Z.eqb ltac:(lia) (encode bound (length x) (eval bound x)) x); trivial.
    apply (ListUtil.internal_list_dec_lb _ Z.eqb ltac:(lia) (encode bound (length x) (eval bound x)) x) in HX.
    congruence.
  Qed.

  Lemma firstn_encode bound i n x (H : Nat.le i n) :
    firstn i (encode bound n x) = encode bound i x.
  Proof.
    replace n with (i + (n-i))%nat by lia; set (n-i)%nat as m; clearbody m.
    rewrite encode_add_l, firstn_app_sharp; auto using length_encode.
  Qed.

  Lemma skipn_encode bound i n x (H : Nat.le i n) :
    skipn i (encode bound n x) = encode bound (n-i) (x / weight bound i).
  Proof.
    replace n with (i + (n-i))%nat by lia; set (n-i)%nat as m; clearbody m.
    rewrite encode_add_l, skipn_app_sharp; auto using length_encode; f_equal; lia.
  Qed.

  Lemma eval_firstn_encode bound i n x (H : Nat.le i n) :
    eval bound (firstn i (encode bound n x)) = x mod weight bound i.
  Proof. rewrite firstn_encode, eval_encode; trivial. Qed.

  Lemma eval_skipn_encode bound i n x (H : Nat.le i n) :
    eval bound (skipn i (encode bound n x)) = x mod weight bound n / weight bound i.
  Proof.
    rewrite skipn_encode, eval_encode; trivial.
    rewrite Z.mod_pull_div by lia; f_equal; f_equal.
    rewrite <-Pos2Z.inj_mul; f_equal.
    replace n with (i+(n-i))%nat at 2 by lia; rewrite weight_add; lia.
  Qed.

  Lemma eval_repeat_0 n : forall bound, eval bound (repeat 0 n) = 0.
  Proof. induction n; trivial; cbn [repeat]; intros. rewrite eval_cons, IHn; lia. Qed.

  Lemma eval_app_repeat_0_r n xs bound : eval bound (xs ++ repeat 0 n) = eval bound xs.
  Proof. rewrite eval_app, eval_repeat_0; nia. Qed.

  Definition add' bound (c0 : Z) (xs ys : list Z) : list Z * Z :=
    ListUtil.list_rect_arrow_nodep
      (fun ys_c : list Z * Z => (@nil Z, snd ys_c))
      (fun x _ rec ys_c =>
        let ys_cur := fst ys_c in
        let c_cur  := snd ys_c in
        let (z, c') := Z.add_with_get_carry_full bound c_cur x (hd 0 ys_cur) in
        let (zs, C) := rec (tl ys_cur, c') in
        (z :: zs, C)
      ) xs (ys, c0).

  Lemma add'_nil bound c ys : add' bound c [] ys = ([], c). Proof. trivial. Qed.

  Lemma add'_cons bound c x xs ys : add' bound c (cons x xs) ys =
    let (z, c') := Z.add_with_get_carry_full bound c x (hd 0 ys) in
    let (zs, C) := add' bound c' xs (tl ys) in
    (z::zs, C).
  Proof. reflexivity. Qed.

  Lemma add'_correct : forall bound xs ys c
    (Hlength : (length ys <= length xs)%nat),
    let s := c + eval bound xs + eval bound ys in
    add' bound c xs ys = (encode bound (length xs) s, s / weight bound (length xs)).
  Proof.
    intros until xs; induction xs as [|x xs];
      cbn [length]; intros; rewrite ?add'_nil, ?add'_cons.
    { case ys in *; [|inversion Hlength]. cbn. f_equal. Z.div_mod_to_equations; lia. }
    rewrite <-?(eval_hd_tl _ ys), ?eval_cons, ?encode_S; cbn [hd tl].
    rewrite Z.add_with_get_carry_full_correct.
    rewrite IHxs by (rewrite length_tl; lia); clear IHxs.
    repeat (apply (f_equal2 pair) || apply (f_equal2 cons)).
    { push_Zmod; pull_Zmod. f_equal. rewrite Z.mul_0_l, Z.add_0_r. lia. }
    { f_equal. Z.div_mod_to_equations; nia. }
    { rewrite weight_S.
      rewrite <-2Z.div_add, Z.div_div; f_equal; lia. }
  Qed.

  Definition add bound c (xs ys : list Z) :=
    if (Z.of_nat (length ys) <=? Z.of_nat (length xs))
    then add' bound c xs ys
    else add' bound c ys xs.

  Lemma add_correct : forall bound xs ys c,
    let s := c + eval bound xs + eval bound ys in
    let n := Nat.max (length xs) (length ys) in
    add bound c xs ys = (encode bound n s, s / weight bound n).
  Proof.
    cbv [add]; intros.
    match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end;
    rewrite ?add'_correct; repeat (lia || f_equal).
  Qed.

  Definition product_scan' bound (acc : list Z) (pps : list (Z*Z)) h0 c0 o0 : list Z * (Z*Z*Z) :=
    ListUtil.list_rect_arrow_nodep
      (fun state : (list Z * (Z * (Z * Z))) =>
        let h := fst (snd state) in
        let c := fst (snd (snd state)) in
        let o := snd (snd (snd state)) in
        (@nil Z, (h, c, o)))
      (fun x_y _ rec state =>
        let x := fst x_y in
        let y := snd x_y in
        let acc_cur := fst state in
        let h := fst (snd state) in
        let c := fst (snd (snd state)) in
        let o := snd (snd (snd state)) in
        let (p, h') := Z.mul_split bound x y in
        let (z, c') := Z.add_with_get_carry_full bound c (hd 0 acc_cur) h in
        let (z0, o') := Z.add_with_get_carry_full bound o z p in
        let (zs, C) := rec (tl acc_cur, (h', (c', o'))) in
        (z0::zs, C)
    ) pps (acc, (h0, (c0, o0))).

  Lemma product_scan'_nil bound acc h c o :
    product_scan' bound acc [] h c o = ([], (h, c, o)).
  Proof. trivial. Qed.

  Lemma hd_firstn_S {A} d n l : @hd A d (firstn (S n) l) = hd d l.
  Proof. case l; trivial. Qed.

  Lemma tl_firstn_S {A} n l : @tl A (firstn (S n) l) = firstn n (tl l).
  Proof. case l; cbn; rewrite ?firstn_nil; trivial. Qed.

  Lemma product_scan'_cons bound acc x y pps h c o :
    product_scan' bound acc ((x, y)::pps) h c o =
      let (p, h') := Z.mul_split bound x y in
      let (z, c) := Z.add_with_get_carry_full bound c (hd 0 acc) h in
      let (z0, o) := Z.add_with_get_carry_full bound o z p in
      let (zs, C) := product_scan' bound (tl acc) pps h' c o in
      (z0::zs, C).
  Proof. reflexivity. Qed.

  Lemma product_scan'_correct : forall bound acc pps h c o,
    let n := length pps in
    let z := eval bound (firstn n acc) + h + c + o + eval bound (map (uncurry Z.mul) pps) in
    exists h' c' o',
    product_scan' bound acc pps h c o = (encode bound n z, (h', c', o')) /\
    h' + c' + o' = z / weight bound n.
  Proof.
    intros ? ? ?; revert acc; induction pps as [|[x y] pps];
      cbn [length]; intros; rewrite ?product_scan'_nil, ?product_scan'_cons.
    { eexists _, _, _; split; trivial. cbn. Z.div_mod_to_equations; lia. }
    edestruct IHpps as (h'&c'&o'&Hlo&Hhi).
    eexists _, _, _.
    repeat rewrite <-?(eval_hd_tl _ (firstn _ acc)), ?Z.mul_split_correct, ?Z.add_with_get_carry_full_correct, ?map_cons, ?eval_cons, ?Hlo, ?Hhi, ?length_tl, ?hd_firstn_S, ?tl_firstn_S, ?Nat.max_S_r, ?encode_S; clear IHpps Hhi Hlo; cbn [uncurry].
    split.
    1: f_equal; f_equal.
    all : push_Zmod; pull_Zmod.
    rewrite ?Z.mul_0_l, ?Z.add_0_r.
    { f_equal; Z.div_mod_to_equations; nia. }
    { f_equal; Z.div_mod_to_equations; nia. }
    cbn [length]; rewrite weight_S, Pos2Z.inj_mul.
    rewrite <-Z.div_div by (pose proof (Pos2Z.is_pos (weight bound (length pps))); lia).
    f_equal.
    Z.div_mod_to_equations; nia.
  Qed.

  Definition product_scan bound acc (pps : list (Z*Z)) h c o : list Z * Z :=
    let z := eval bound (firstn (length pps) acc) + h + c + o + eval bound (map (uncurry Z.mul) pps) in
    let '(lo, (h, c, o)) := product_scan' bound acc pps h c o in
    (lo, 
      let zc := z / weight bound (length lo) in
      if_expect_true ((0 <=? zc) && (zc <? Z.pos bound))%bool
      (dlet h := fst (Z.add_with_get_carry_full bound c h 0) in
       dlet h := fst (Z.add_with_get_carry_full bound o h 0) in
       h)
      (fun _ => h+c+o)).

  Lemma eval_map_mul bound x ys : eval bound (map (Z.mul x) ys) = x * eval bound ys.
  Proof.
    induction ys;
      rewrite ?map_cons, ?eval_nil, ?eval_cons, ?IHys; ring.
  Qed.

  Lemma product_scan_correct bound acc pps h c o :
    let n := length pps in
    let z := eval bound (firstn n acc) + h + c + o + eval bound (map (uncurry Z.mul) pps) in
    product_scan bound acc pps h c o = (encode bound n z, z / weight bound n).
  Proof.
    cbv [product_scan if_expect_true Let_In].
    edestruct product_scan'_correct as (h'&c'&o'&Hlo&Hhi); rewrite Hlo, Hhi; clear Hlo.
    rewrite ?map_map, ?map_length, ?eval_app, ?eval_encode, ?length_encode, ?eval_cons, ?eval_nil, ?Z.add_with_get_carry_full_mod in *.
    cbn [uncurry] in *; rewrite ?eval_map_mul, ?Z.mul_0_r ,?Z.add_0_r in *; f_equal.
    match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; trivial.
    match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end; trivial; cbn [andb].
    push_Zmod; pull_Zmod; rewrite Z.mod_small; [lia|]. lia.
  Qed.

  Lemma length_add_mul_limb' bound acc pps :
    length (fst (product_scan bound acc pps 0 0 0)) = length pps.
  Proof. rewrite product_scan_correct; apply length_encode. Qed.

  Definition add_ bound c xs ys : list Z :=
    let (lo, hi) := add bound c xs ys in lo ++ [hi].

  Lemma eval_add_ bound c xs ys :
    eval bound (add_ bound c xs ys) = c + eval bound xs + eval bound ys.
  Proof.
    cbv [add_].
    break_match; Prod.inversion_prod; subst;
    rewrite add_correct, eval_app, eval_cons, eval_nil by lia; cbn [fst snd]; ring_simplify.
    rewrite eval_encode, length_encode; Z.div_mod_to_equations; nia.
  Qed.

  Definition product_scan_ bound acc pps h c o :=
    let '(l, h) := product_scan bound acc pps h c o in
    dlet r := l ++ if_expect_true (Z.of_nat (length pps) <? Z.of_nat (length acc))
                   (add_ bound 0 (skipn (length pps) acc) [h])
                   (fun _ => [h]) in
    r.

  Lemma eval_product_scan_ bound acc pps h c o :
    eval bound (product_scan_ bound acc pps h c o)
    = eval bound acc + h + c + o + eval bound (map (uncurry Z.mul) pps).
  Proof.
    cbv [product_scan_ if_expect_true Let_In].
    rewrite product_scan_correct, eval_app, eval_encode, length_encode.
    case (Z.ltb_spec (Z.of_nat (length pps)) (Z.of_nat (length acc))) as [H|H]; cycle 1;
      repeat rewrite ?eval_cons, ?eval_nil, ?Z.mul_0_r, ?eval_add_, ?Z.add_0_l, ?Z.add_0_r.
    { rewrite <-!Z.add_assoc, <-Z.add_mod_idemp_l, eval_firstn, Z.add_mod_idemp_l, !Z.add_assoc by lia.
      rewrite ?firstn_all2 by lia. Z.div_mod_to_equations; nia. }
    pose proof firstn_skipn (length pps) acc as Hacc.
    eapply (f_equal (eval bound)) in Hacc; erewrite eval_app in Hacc.
    rewrite firstn_length, Nat.min_l in * by lia.
    Z.div_mod_to_equations; nia.
  Qed.

  Definition add_mul_small bound acc x ys : list Z * Z :=
    let '(lo, (h, c, o)) := product_scan' bound acc (map (pair x) ys) 0 0 0 in
    dlet hi := h + c + o in
    if (Z.of_nat (length acc) <=? Z.of_nat (length ys))
    then (lo, hi)
    else
      let (mid, hi) := add bound 0 (skipn (length ys) acc) [hi] in
      (lo ++ mid, hi).

  Lemma add_mul_small_correct bound acc x ys :
    let z := eval bound acc + x * eval bound ys in
    let n := Nat.max (length acc) (length ys) in
    add_mul_small bound acc x ys = (encode bound n z, z / weight bound n).
  Proof.
  Admitted.

  Definition add_mul_limb_ bound acc x ys : list Z :=
    product_scan_ bound acc (map (pair x) ys) 0 0 0.

  Lemma eval_add_mul_limb_ bound acc x ys :
    eval bound (add_mul_limb_ bound acc x ys) = eval bound acc + x * eval bound ys.
  Proof.
    cbv [add_mul_limb_].
    rewrite eval_product_scan_, map_map.
    cbv [uncurry]. rewrite eval_map_mul.
    nia.
  Qed.

  Definition add_mul bound (acc xs ys : list Z) : list Z :=
    ListUtil.list_rect_arrow_nodep
      (fun acc => acc)
      (fun x _ rec acc =>
        dlet acc' := add_mul_limb_ bound acc x ys in
        hd 0 acc' :: rec (tl acc')
      ) xs acc.

  Definition add_mul_nil bound acc ys : add_mul bound acc [] ys = acc.
  Proof. trivial. Qed.

  Definition add_mul_cons bound acc x xs ys :
    add_mul bound acc (x::xs) ys =
      let acc := add_mul_limb_ bound acc x ys in
      hd 0 acc :: add_mul bound (tl acc) xs ys.
  Proof. reflexivity. Qed.

  Lemma eval_add_mul bound acc xs ys :
    eval bound (add_mul bound acc xs ys) =
    eval bound acc + eval bound xs * eval bound ys.
  Proof.
    revert ys; revert acc; induction xs; intros;
      rewrite ?add_mul_nil, ?add_mul_cons, ?eval_nil, ?eval_cons, ?IHxs.
    { ring. }
    pose proof eval_add_mul_limb_ bound acc a ys as HH.
    rewrite <-eval_hd_tl, eval_cons in HH.
    rewrite Z.mul_add_distr_r, Z.add_assoc, <-HH; ring_simplify.
    ring.
  Qed.

  Definition mul bound := add_mul bound [].

  Lemma eval_mul bound xs ys :
    eval bound (mul bound xs ys) = eval bound xs * eval bound ys.
  Proof. cbv [mul]. rewrite eval_add_mul, ?firstn_nil, ?eval_nil. ring. Qed.
  
  Lemma length_mul bound xs ys : ys <> [] -> length (mul bound xs ys) = (length xs + length ys)%nat.
  Admitted.

  Definition diagonal b (pps : list (Z * Z)) :=
    flat_map (fun '(x, y) =>
      let '(lo, hi) := Z.mul_split b x y in
      [lo; hi]
    ) pps.

  Lemma eval_diagonal b pps :
    eval b (diagonal b pps) =
    eval (Pos.mul b b) (map (uncurry Z.mul) pps).
  Proof.
    induction pps as [|[x y] ]; [trivial|].
    unfold diagonal at 1; cbn [flat_map map fst snd uncurry].
    destruct (Z.mul_split b x y) as [lo hi] eqn:E.
    rewrite Z.mul_split_correct in E; inversion E; subst.
    cbn [app]; fold (diagonal b pps).
    rewrite !eval_cons.
    rewrite IHpps, Pos2Z.inj_mul, Z.mul_add_distr_l, <-Z.mul_assoc, Z.add_assoc.
    pose proof (Z.div_mod (x * y) (Z.pos b) ltac:(lia)); lia.
  Qed.

  Definition select' c a b := map (uncurry (Z.zselect c)) (combine a b).

  Lemma select'_correct c a b : length a = length b -> select' c a b = if dec (c = 0) then a else b.
  Proof.
    revert b; induction a, b; cbn; try inversion 1; rewrite ?Z.zselect_correct;
      break_match; f_equal; eauto.
  Qed.

  Lemma length_select' c a b : length (select' c a b) = Nat.min (length a) (length b).
  Proof. cbv [select']. rewrite map_length, combine_length; lia. Qed.

  Definition select c a b : list Z :=
    dlet a := a in
    dlet b := b in
    select' c (a ++ repeat 0 (length b - length a)%nat) (b ++ repeat 0 (length a - length b)%nat).

  Lemma eval_select bound c a b : eval bound (select c a b) = eval bound (if dec (c = 0) then a else b).
  Proof.
    cbv [select Let_In].
    rewrite select'_correct by (rewrite ?app_length, ?repeat_length; lia).
    break_match; rewrite eval_app_repeat_0_r; trivial.
  Qed.

  Lemma length_select c a b : length (select c a b) = Nat.max (length a) (length b).
  Proof. cbv [select Let_In]. rewrite length_select', ?app_length, ?repeat_length; lia. Qed.

  Definition cswap' c a b := (select' c a b, select' c b a).

  Lemma cswap_correct c a b : length a = length b -> cswap' c a b = if dec (c = 0) then (a, b) else (b, a).
  Proof. cbv [cswap']; intros; rewrite !select'_correct; break_match; congruence. Qed.

  Definition condsub bound a b := let '(lo, hi) := add' bound 0 a (map Z.opp b) in select (-hi) lo a.

  Lemma eval_map_opp bound xs : eval bound (map Z.opp xs) = - eval bound xs.
  Proof. induction xs; trivial; intros; rewrite ?map_cons, ?eval_cons, ?IHxs; lia. Qed.

  Lemma Z__opp_zero_iff z : Z.opp z = 0 <-> z = 0. Proof. lia. Qed.

  Lemma eval_condsub' bound a b (Hlen : (length b <= length a)%nat) :
    eval bound (condsub bound a b) =
    eval bound a - Z.b2z (((eval bound a - eval bound b) / weight bound (length a) =? 0)) * eval bound b.
  Proof.
    cbv [condsub Let_In].
    destruct (add' bound 0 a (map Z.opp b)) as [lo hi] eqn:H.
    pose proof (add'_correct bound a (map Z.opp b) 0 ltac:(rewrite map_length; assumption)) as Hc.
    cbn [Z.add] in Hc.
    rewrite H in Hc; inversion Hc; subst lo hi; clear H Hc.
    rewrite eval_map_opp, eval_select.
    rewrite Z.add_opp_r in *.
    break_match.
    { match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; try lia.
      simpl Z.b2z; rewrite Z.mul_1_l.
      rewrite eval_encode.
      pose proof (Z.div_mod (eval bound a - eval bound b) (weight bound (length a)) ltac:(lia)).
      lia. }
    { match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; try lia.
      simpl Z.b2z; rewrite Z.mul_0_l, Z.sub_0_r; trivial. }
  Qed.

  Lemma eval_condsub bound a b
    (Hlen : (length b <= length a)%nat)
    (Ha : eval bound a < weight bound (length a))
    (Hb : 0 <= eval bound b) :
    eval bound (condsub bound a b) =
    eval bound a - Z.b2z (eval bound b <=? eval bound a) * eval bound b.
  Proof.
    rewrite eval_condsub' by assumption. f_equal. f_equal. f_equal. eapply Bool.eq_true_iff_eq.
    rewrite Z.eqb_eq, Z.div_small_iff, Z.leb_le by lia.
    intuition try lia.
  Qed.

  Lemma length_condsub bound a b (Hlen : (length b <= length a)%nat) : length (condsub bound a b) = length a.
  Proof.
    cbv [condsub Let_In].
    rewrite add'_correct by (rewrite map_length; assumption).
    rewrite length_select, length_encode; lia.
  Qed.
End Saturated.
