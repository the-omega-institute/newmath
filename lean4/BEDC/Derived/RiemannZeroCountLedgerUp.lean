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

theorem RiemannZeroCountLedger_window_exhaustion
    (x : RiemannZeroCountLedgerUp) :
    ∃ T Z U M E H C P N : BHist,
      (∃ count_unary : UnaryHistory U,
        x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary) ∧
        UnaryHistory U ∧ Cont H C (append H C) ∧ Cont C P (append C P) ∧
          hsame T T ∧ hsame Z Z ∧ hsame M M ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  cases x with
  | mk T Z U M E H C P N count_unary =>
      exact
        ⟨T, Z, U, M, E, H, C, P, N, ⟨count_unary, rfl⟩, count_unary, rfl, rfl,
          hsame_refl T, hsame_refl Z, hsame_refl M, hsame_refl E⟩

theorem RiemannZeroCountLedgerCarrier_window_exhaustion
    (x : RiemannZeroCountLedgerUp) :
    ∃ T Z U M E H C P N : BHist,
      (∃ count_unary : UnaryHistory U,
        x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary) ∧
        UnaryHistory U ∧ hsame T T ∧ hsame Z Z ∧ hsame U U ∧
          Cont H C (append H C) ∧ hsame (append H C) (append H C) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  cases x with
  | mk T Z U M E H C P N count_unary =>
      exact
        ⟨T, Z, U, M, E, H, C, P, N, ⟨count_unary, rfl⟩, count_unary,
          hsame_refl T, hsame_refl Z, hsame_refl U, rfl, hsame_refl (append H C)⟩

theorem RiemannZeroCountLedgerCarrier_comparison_error_nonescape
    {T Z U M E H C P N comparisonRead exportRead : BHist}
    (count_unary : UnaryHistory U)
    (m_unary : UnaryHistory M)
    (e_unary : UnaryHistory E)
    (comparisonRoute : Cont M E comparisonRead)
    (exportRoute : Cont comparisonRead U exportRead) :
    ∃ x : RiemannZeroCountLedgerUp,
      x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary ∧
        UnaryHistory comparisonRead ∧
          UnaryHistory exportRead ∧
            Cont M E comparisonRead ∧
              Cont comparisonRead U exportRead ∧ hsame M M ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed m_unary e_unary comparisonRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed comparisonUnary count_unary exportRoute
  exact
    ⟨RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary, rfl,
      comparisonUnary, exportUnary, comparisonRoute, exportRoute,
      hsame_refl M, hsame_refl E⟩

end BEDC.Derived.RiemannZeroCountLedgerUp
