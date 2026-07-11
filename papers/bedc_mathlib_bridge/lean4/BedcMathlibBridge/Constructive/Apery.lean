import BedcMathlibBridge.Constructive.Binomial
import BEDC.Derived.AperyUp
import Mathlib.Data.Nat.Choose.Basic

namespace BedcMathlibBridge.Constructive.Apery

private def mathlibChooseProvenanceAnchor : Unit :=
  let _ : forall n k : Nat, Nat.choose n k = Nat.choose n k := fun _ _ => rfl
  ()

def readbackA (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.AperyUp.aperyA n

def readbackB (n : Nat) : Nat :=
  let _ := mathlibChooseProvenanceAnchor
  BEDC.Derived.AperyUp.aperyB n

theorem readbackA_apply (n : Nat) :
    readbackA n = BEDC.Derived.AperyUp.aperyA n := by
  rfl

theorem readbackB_apply (n : Nat) :
    readbackB n = BEDC.Derived.AperyUp.aperyB n := by
  rfl

private theorem C_eq_nat_choose (n k : Nat) :
    BEDC.Derived.AperyUp.C n k = Nat.choose n k := by
  unfold BEDC.Derived.AperyUp.C
  change BEDC.Derived.LucasTheoremUp.bedcChooseNat n k = Nat.choose n k
  exact BedcMathlibBridge.Constructive.Binomial.bedcChoose_eq_nat_choose n k

private theorem natListSum_congr
    {f g : Nat -> Nat} (h : forall k : Nat, f k = g k) :
    forall xs : List Nat,
      BEDC.Derived.AperyUp.natListSum xs f =
        BEDC.Derived.AperyUp.natListSum xs g
  | [] => rfl
  | x :: rest => by
      change
        f x + BEDC.Derived.AperyUp.natListSum rest f =
          g x + BEDC.Derived.AperyUp.natListSum rest g
      rw [h x, natListSum_congr h rest]

theorem aperyATerm_eq_nat_choose_term (n k : Nat) :
    BEDC.Derived.AperyUp.aperyATerm n k =
      (Nat.choose n k * Nat.choose n k) *
        (Nat.choose (n + k) k * Nat.choose (n + k) k) := by
  unfold BEDC.Derived.AperyUp.aperyATerm BEDC.Derived.AperyUp.natSquare
  rw [C_eq_nat_choose n k, C_eq_nat_choose (n + k) k]

theorem aperyBTerm_eq_nat_choose_term (n k : Nat) :
    BEDC.Derived.AperyUp.aperyBTerm n k =
      (Nat.choose n k * Nat.choose n k) * Nat.choose (n + k) k := by
  unfold BEDC.Derived.AperyUp.aperyBTerm BEDC.Derived.AperyUp.natSquare
  rw [C_eq_nat_choose n k, C_eq_nat_choose (n + k) k]

theorem readbackA_eq_nat_choose_sum (n : Nat) :
    readbackA n =
      BEDC.Derived.AperyUp.natListSum (BEDC.Derived.AperyUp.aperyIndexList n)
        (fun k =>
          (Nat.choose n k * Nat.choose n k) *
            (Nat.choose (n + k) k * Nat.choose (n + k) k)) := by
  rw [readbackA_apply, BEDC.Derived.AperyUp.aperyA_sum_definition n]
  exact natListSum_congr (fun k => aperyATerm_eq_nat_choose_term n k)
    (BEDC.Derived.AperyUp.aperyIndexList n)

theorem readbackB_eq_nat_choose_sum (n : Nat) :
    readbackB n =
      BEDC.Derived.AperyUp.natListSum (BEDC.Derived.AperyUp.aperyIndexList n)
        (fun k =>
          (Nat.choose n k * Nat.choose n k) * Nat.choose (n + k) k) := by
  rw [readbackB_apply, BEDC.Derived.AperyUp.aperyB_sum_definition n]
  exact natListSum_congr (fun k => aperyBTerm_eq_nat_choose_term n k)
    (BEDC.Derived.AperyUp.aperyIndexList n)

end BedcMathlibBridge.Constructive.Apery
