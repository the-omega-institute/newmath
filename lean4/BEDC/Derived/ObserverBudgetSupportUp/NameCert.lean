import BEDC.Derived.ObserverBudgetSupportUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.ObserverBudgetSupportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem ObserverBudgetSupportNameCert_obligations [AskSetup] [PackageSetup]
    {F S X B T H C P N replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] →
      Cont F S T →
        Cont X B C →
          Cont T C replay →
            PkgSig bundle N pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row replay ∧
                    ∃ packet : ObserverBudgetSupportUp,
                      packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                        FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
                (fun row : BHist => Cont F S T ∧ Cont X B C ∧ Cont T C row)
                (fun row : BHist => hsame row replay ∧ PkgSig bundle N pkg ∧ hsame H H)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact observerRoute causalRoute replayRoute packageName
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨replay, hsame_refl replay,
            ObserverBudgetSupportUp.mk F S X B T H C P N, rfl, fieldsExact⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        exact hsame_trans leftSame rightSame
      carrier_respects_equiv := by
        intro _row _row' same source
        cases same
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left
      exact ⟨observerRoute, causalRoute, replayRoute⟩
    ledger_sound := by
      intro row source
      exact ⟨source.left, packageName, hsame_refl H⟩
  }

end BEDC.Derived.ObserverBudgetSupportUp
