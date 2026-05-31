import BEDC.Derived.NatUp

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem UnaryBridgeCutBoundary {h k tail : BHist} :
    UnaryHistory h →
      UnaryHistory k →
        UnaryHistory tail →
          Cont h tail k →
            (tail = BHist.Empty ∧ hsame h k) ∨
              ((tail = BHist.Empty → False) ∧ NatUnaryStrictPrefix h k) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro _hUnary _kUnary tailUnary htail
  cases tail with
  | Empty =>
      have sameKH : hsame k h := cont_deterministic htail (cont_right_unit h)
      exact Or.inl ⟨rfl, hsame_symm sameKH⟩
  | e0 tail =>
      exact False.elim (unary_no_zero_extension tailUnary)
  | e1 tail =>
      exact Or.inr
        ⟨(fun empty => by cases empty),
          ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), htail⟩⟩

end BEDC.Derived.NatUp
