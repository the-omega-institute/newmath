import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RiemannZeroCountLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

inductive RiemannZeroCountLedgerUp : Type where
  | mk (T Z U M E H C P N : BHist) (count_unary : UnaryHistory U) :
      RiemannZeroCountLedgerUp

theorem RiemannZeroCountLedgerCarrier_namecert_obligations
    (x : RiemannZeroCountLedgerUp) :
    ∃ T Z U M E H C P N : BHist,
      (∃ count_unary : UnaryHistory U,
        x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary) ∧
        hsame T T ∧ UnaryHistory U ∧ Cont H C (append H C) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  cases x with
  | mk T Z U M E H C P N count_unary =>
      exact
        ⟨T, Z, U, M, E, H, C, P, N, ⟨count_unary, rfl⟩, hsame_refl T,
          count_unary, rfl⟩

end BEDC.Derived.RiemannZeroCountLedgerUp
