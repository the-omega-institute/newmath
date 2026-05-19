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

theorem ObserverBudgetSupportFieldFaithfulness [AskSetup] [PackageSetup]
    {F S X B T H C P N supportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont F S T →
      Cont X B C →
        Cont T C supportRead →
          PkgSig bundle supportRead pkg →
            FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
                [F, S, X, B, T, H, C, P, N] ∧
              SemanticNameCert
                (fun row : BHist =>
                  hsame row supportRead ∧
                    ∃ packet : ObserverBudgetSupportUp,
                      packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                        FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
                (fun row : BHist =>
                  Cont F S T ∧ Cont X B C ∧ Cont T C row ∧
                    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
                      [F, S, X, B, T, H, C, P, N])
                (fun row : BHist =>
                  hsame row supportRead ∧ PkgSig bundle supportRead pkg ∧
                    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
                      [F, S, X, B, T, H, C, P, N])
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro observerRoute causalRoute supportRoute packageSupport
  have fieldsExact :
      FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] := by
    rfl
  have sourceSupport :
      (fun row : BHist =>
        hsame row supportRead ∧
          ∃ packet : ObserverBudgetSupportUp,
            packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
              FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
        supportRead := by
    exact
      ⟨hsame_refl supportRead, ObserverBudgetSupportUp.mk F S X B T H C P N, rfl,
        fieldsExact⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row supportRead ∧
            ∃ packet : ObserverBudgetSupportUp,
              packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
        (fun row : BHist =>
          Cont F S T ∧ Cont X B C ∧ Cont T C row ∧
            FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
              [F, S, X, B, T, H, C, P, N])
        (fun row : BHist =>
          hsame row supportRead ∧ PkgSig bundle supportRead pkg ∧
            FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
              [F, S, X, B, T, H, C, P, N])
        hsame := {
    core := {
      carrier_inhabited := Exists.intro supportRead sourceSupport
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
      exact ⟨observerRoute, causalRoute, supportRoute, fieldsExact⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, packageSupport, fieldsExact⟩
  }
  exact ⟨fieldsExact, cert⟩

end BEDC.Derived.ObserverBudgetSupportUp
