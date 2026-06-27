import BEDC.Derived.RationalUp.MetricOrder

namespace BEDC.Derived.RHRoute.AlternatingTailBound

open BEDC.Derived.RationalUp

def altPartialSum (a : Nat -> RatNum) (N : Nat) : Nat -> RatNum
  | 0 => ratZero
  | Nat.succ M => ratAdd (a N) (ratNeg (altPartialSum a (N + 1) M))

theorem alternating_tail_sandwich
    (a : Nat -> RatNum)
    (nonneg : forall n : Nat, ratLe ratZero (a n))
    (antitone : forall n : Nat, ratLe (a (n + 1)) (a n))
    (N M : Nat) :
    ratLe ratZero (altPartialSum a N M) ∧
      ratLe (altPartialSum a N M) (a N) := by
  induction M generalizing N with
  | zero =>
      unfold altPartialSum
      exact ⟨ratLe_refl ratZero, nonneg N⟩
  | succ M ih =>
      unfold altPartialSum
      have tailSandwich :=
        ih (N := N + 1)
      have tailLeNext :
          ratLe (altPartialSum a (N + 1) M) (a (N + 1)) :=
        tailSandwich.right
      have nextLeHead : ratLe (a (N + 1)) (a N) :=
        antitone N
      have tailLeHead :
          ratLe (altPartialSum a (N + 1) M) (a N) :=
        ratLe_trans tailLeNext nextLeHead
      exact
        ⟨ratSub_nonneg_of_le tailLeHead,
          ratSub_le_left_of_nonneg tailSandwich.left⟩

theorem alternating_tail_le_head
    (a : Nat -> RatNum)
    (nonneg : forall n : Nat, ratLe ratZero (a n))
    (antitone : forall n : Nat, ratLe (a (n + 1)) (a n))
    (N M : Nat) :
    ratLe (ratAbs (altPartialSum a N M)) (a N) := by
  have sandwich :=
    alternating_tail_sandwich a nonneg antitone N M
  exact ratAbs_le_of_nonneg_le sandwich.left sandwich.right

end BEDC.Derived.RHRoute.AlternatingTailBound
