(*! TODO: merge with Word.v !*)

Require Import ZArith Eqdep.
Require Import Lib.CommonTactics Lib.NatLib Lib.Word.

Set Implicit Arguments.

(* some more manipulation on [word] *)

Definition extz {sz} (w: word sz) (n: nat) := combine (wzero n) w.

Definition rtrunc1 sz (w: word (S sz)): word sz:=
  match w with
  | WO => idProp
  | WS _ w' => w'
  end.

Definition rtrunc2 sz (w: word (S (S sz))): word sz :=
  match w with
  | WO => idProp
  | WS _ w' =>
    match w' with
    | WO => idProp
    | WS _ w'' => w''
    end
  end.

Definition wlsb sz (w: word (S sz)) :=
  match w with
  | WO => idProp
  | WS b _ => b
  end.

(* some more facts *)

Lemma wordToZ_wzero':
  forall sz, wordToZ (wzero' sz) = 0%Z.
Proof.
Admitted.

Lemma wtl_combine:
  forall (x: word 1) sz (y: word sz),
    wtl (combine x y) = y.
Proof.
Admitted.

Lemma combine_wplus:
  forall sl (w1: word sl) su (w2 w3: word su),
    combine w1 (w2 ^+ w3) = combine w1 w2 ^+ extz w3 sl.
Proof.
Admitted.

Lemma existT_wplus:
  forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
    existT word _ w1 = existT word _ w3 ->
    existT word _ w2 = existT word _ w4 ->
    existT word _ (w1 ^+ w2) = existT word _ (w3 ^+ w4).
Proof.
  intros.
  rewrite eq_sigT_sig_eq in H; destruct H as [Hsz1 ?].
  rewrite eq_sigT_sig_eq in H0; destruct H0 as [Hsz2 ?].
  subst; do 2 rewrite <-eq_rect_eq.
  reflexivity.
Qed.

Lemma wrshifta_wplus:
  forall sz (w1 w2: word sz) n,
    wrshifta (w1 ^+ w2) n = wrshifta w1 n ^+ wrshifta w2 n.
Proof.
Admitted.

Lemma combine_wrshifta_rtrunc1_sext:
  forall s (w: word s) sl (wl: word (S (S sl))) su (wu: word su),
    existT word s w =
    existT word ((S (S sl)) + su) (combine wl wu) ->
    existT word s (wrshifta w 1) =
    existT word ((S sl) + (su + 1)) (combine (rtrunc1 wl) (sext wu 1)).
Proof.
Admitted.

Lemma combine_wrshifta_rtrunc2_sext:
  forall s (w: word s) sl (wl: word (S (S (S sl)))) su (wu: word su),
    existT word s w =
    existT word ((S (S (S sl))) + su) (combine wl wu) ->
    existT word s (wrshifta w 2) =
    existT word ((S sl) + (su + 2)) (combine (rtrunc2 wl) (sext wu 2)).
Proof.
Admitted.

Lemma wrshifta_extz_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (wrshifta (extz w (n1 + n2)) n1) =
    existT word _ (sext (extz w n2) n1).
Proof.
Admitted.

Lemma wlshift_sext_extz:
  forall sz (w: word sz) n,
    existT word _ (wlshift (sext w n) n) =
    existT word _ (extz w n).
Proof.
Admitted.

Lemma wlshift_combine_sext_extz:
  forall sz' (w': word sz') sz (w: word sz) n,
    existT word _ (wlshift (combine w' (sext w n)) n) =
    existT word _ (combine w' (extz w n)).
Proof.
Admitted.

Lemma extz_sext:
  forall sz (w: word sz) n1 n2,
    existT word _ (extz (sext w n1) n2) =
    existT word _ (sext (extz w n2) n1).
Proof.
Admitted.

Lemma extz_sext_eq_rect:
  forall sz (w: word sz) n1 n2 nsz Hnsz1,
  exists Hnsz2,
    eq_rect (n2 + (sz + n1)) word (extz (sext w n1) n2) nsz Hnsz1 =
    eq_rect (n2 + sz + n1) word (sext (extz w n2) n1) nsz Hnsz2.
Proof.
  intros; subst; simpl.
  assert (Hsz: n2 + sz + n1 = n2 + (sz + n1)) by omega.
  exists Hsz.
  pose proof (extz_sext w n1 n2).
  pose proof (eq_sigT_snd H).
  rewrite <-H0.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma existT_sext:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (sext w1 n) = existT word _ (sext w2 n).
Proof.
  intros; inv H; reflexivity.
Qed.

Lemma existT_extz:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (extz w1 n) = existT word _ (extz w2 n).
Proof.
  intros; inv H; reflexivity.
Qed.

Lemma existT_wrshifta:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wrshifta w1 n) = existT word _ (wrshifta w2 n).
Proof.
  intros; inv H; reflexivity.
Qed.

Lemma existT_wlshift:
  forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
    existT word _ w1 = existT word _ w2 ->
    existT word _ (wlshift w1 n) = existT word _ (wlshift w2 n).
Proof.
  intros; inv H; reflexivity.
Qed.

Lemma extz_extz:
  forall sz (w: word sz) n1 n2,
    existT word _ (extz (extz w n1) n2) =
    existT word _ (extz w (n2 + n1)).
Proof.
Admitted.

Lemma sext_wplus_wordToZ_distr:
  forall sz (w1 w2: word sz) n,
    n <> 0 -> wordToZ (sext w1 n ^+ sext w2 n) =
              (wordToZ (sext w1 n) + wordToZ (sext w2 n))%Z.
Proof.
Admitted.

Lemma sext_wordToZ:
  forall sz (w: word sz) n,
    wordToZ (sext w n) = wordToZ w.
Proof.
Admitted.

Lemma split1_combine_existT:
  forall sz n (w: word (n + sz)) sl (wl: word (n + sl)) su (wu: word su),
    existT word _ w = existT word _ (combine wl wu) ->
    split1 n _ w = split1 n _ wl.
Proof.
Admitted.

Lemma extz_pow2_wordToZ:
  forall sz (w: word sz) n,
    wordToZ (extz w n) = (wordToZ w * Z.of_nat (pow2 n))%Z.
Proof.
Admitted.

Lemma extz_wneg:
  forall sz (w: word sz) n,
    extz (wneg w) n = wneg (extz w n).
Proof.
Admitted.

Lemma wneg_wordToZ:
  forall sz (w: word sz),
    wordToZ (wneg w) = (- wordToZ w)%Z.
Proof.
Admitted.

Lemma wneg_wordToZ':
  forall sz (w: word sz) z,
    (z + wordToZ (wneg w))%Z = (z - wordToZ w)%Z.
Proof.
  intros; rewrite wneg_wordToZ; omega.
Qed.

Lemma wrshifta_zero:
  forall sz n, wrshifta (natToWord sz 0) n = wzero _.
Proof.
Admitted.

Lemma extz_zero:
  forall sz n, extz (natToWord sz 0) n = wzero _.
Proof.
Admitted.

Lemma existT_eq_rect:
  forall (X: Type) (P: X -> Type) (x1 x2: X) (H1: P x1) (Hx: x1 = x2),
    existT P x2 (eq_rect x1 P H1 x2 Hx) =
    existT P x1 H1.
Proof.
  intros; subst.
  rewrite <-eq_rect_eq; reflexivity.
Qed.

Lemma sext_eq_rect:
  forall sz (w: word sz) n nsz Hsz1,
  exists Hsz2,
    eq_rect (sz + n) word (sext w n) (nsz + n) Hsz1 =
    sext (eq_rect sz word w nsz Hsz2) n.
Proof.
  intros.
  assert (Hsz: sz = nsz) by omega.
  exists Hsz.
  subst; simpl.
  eq_rect_simpl.
  reflexivity.
Qed.

Lemma wordToZ_eq_rect:
  forall sz (w: word sz) nsz Hsz,
    wordToZ (eq_rect _ word w nsz Hsz) = wordToZ w.
Proof.
  intros; subst; simpl; reflexivity.
Qed.

Lemma pow2_S_z:
  forall n, Z.of_nat (pow2 (S n)) = (2 * Z.of_nat (pow2 n))%Z.
Proof.
  intros.
  replace (2 * Z.of_nat (pow2 n))%Z with
      (Z.of_nat (pow2 n) + Z.of_nat (pow2 n))%Z by omega.
  simpl.
  repeat rewrite Nat2Z.inj_add.
  ring.
Qed.

