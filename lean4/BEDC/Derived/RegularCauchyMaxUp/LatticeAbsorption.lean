import BEDC.Derived.RegularCauchyMaxUp.SumAbsFactorization

namespace BEDC.Derived.RegularCauchyMaxUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem RegularCauchyMaxCarrier_lattice_absorption
    {A B WA WB DA DB S Delta V T Q R E H C P N innerSource innerSum innerAbs innerScaled
      innerRead outerSource outerSum outerAbs outerScaled outerRead : BHist} :
    regularCauchyMaxFields (RegularCauchyMaxUp.mk A B WA WB DA DB S Delta V T Q R E H C P N) =
        [A, B, WA, WB, DA, DB, S, Delta, V, T, Q, R, E, H, C, P, N] →
      UnaryHistory A →
      UnaryHistory B →
      UnaryHistory S →
      UnaryHistory V →
      UnaryHistory Q →
      UnaryHistory R →
      Cont A B innerSource →
      Cont innerSource S innerSum →
      Cont innerSum V innerAbs →
      Cont innerAbs Q innerScaled →
      Cont innerScaled R innerRead →
      Cont A innerRead outerSource →
      Cont outerSource S outerSum →
      Cont outerSum V outerAbs →
      Cont outerAbs Q outerScaled →
      Cont outerScaled R outerRead →
      UnaryHistory innerSource ∧
        UnaryHistory innerRead ∧
          UnaryHistory outerSource ∧
            UnaryHistory outerRead ∧
              Cont A B innerSource ∧ Cont A innerRead outerSource := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro hfields hA hB hS hV hQ hR hInnerSource hInnerSum hInnerAbs hInnerScaled
    hInnerRead hOuterSource hOuterSum hOuterAbs hOuterScaled hOuterRead
  have hInner :
      UnaryHistory innerSource ∧
        UnaryHistory innerSum ∧
          UnaryHistory innerAbs ∧
            UnaryHistory innerScaled ∧
              UnaryHistory innerRead ∧
                Cont A B innerSource ∧
                  Cont innerSource S innerSum ∧
                    Cont innerSum V innerAbs ∧
                      Cont innerAbs Q innerScaled ∧ Cont innerScaled R innerRead :=
    RegularCauchyMaxCarrier_sum_abs_factorization hfields hA hB hS hV hQ hR
      hInnerSource hInnerSum hInnerAbs hInnerScaled hInnerRead
  have hInnerSourceUnary : UnaryHistory innerSource := hInner.left
  have hInnerReadUnary : UnaryHistory innerRead := hInner.right.right.right.right.left
  have hOuterSourceUnary : UnaryHistory outerSource :=
    unary_cont_closed hA hInnerReadUnary hOuterSource
  have hOuterSumUnary : UnaryHistory outerSum :=
    unary_cont_closed hOuterSourceUnary hS hOuterSum
  have hOuterAbsUnary : UnaryHistory outerAbs :=
    unary_cont_closed hOuterSumUnary hV hOuterAbs
  have hOuterScaledUnary : UnaryHistory outerScaled :=
    unary_cont_closed hOuterAbsUnary hQ hOuterScaled
  have hOuterReadUnary : UnaryHistory outerRead :=
    unary_cont_closed hOuterScaledUnary hR hOuterRead
  exact
    ⟨hInnerSourceUnary,
      hInnerReadUnary,
      hOuterSourceUnary,
      hOuterReadUnary,
      hInnerSource,
      hOuterSource⟩

end BEDC.Derived.RegularCauchyMaxUp
