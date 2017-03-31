Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Fetch AbstractIsa.

Set Implicit Arguments.

(** Let's merge [fetch] and [btb] by inlining *)
Section FetchBtb.
  Variables addrSize dataBytes rfIdx: nat.
  Variables indexSize tagSize: nat.
  Hypothesis (Haddr: indexSize + tagSize = addrSize).
  Variable f2iName: string.

  Definition fetchBtb :=
    (fetch addrSize dataBytes f2iName ++ btb indexSize tagSize Haddr)%kami.
  Hint Unfold fetchBtb: ModuleDefs.

  Lemma fetchBtb_ModEquiv: ModPhoasWf fetchBtb.
  Proof. kequiv. Qed.

  Definition fetchBtbInl: sigT (fun m: Modules => fetchBtb <<== m).
  Proof.
    pose proof (inlineF_refines
                  (fetchBtb_ModEquiv type typeUT)
                  (Reflection.noDupStr_NoDup (Struct.namesOf (getDefsBodies fetchBtb)) eq_refl))
      as Him.
    unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him.
    match goal with
    | [H: context[inlineF ?m] |- _] => set m as origm in H at 2
    end.
    kinline_compute_in Him.
    unfold origm in *.
    specialize (Him eq_refl).
    exact (existT _ _ Him).
  Defined.

End FetchBtb.

