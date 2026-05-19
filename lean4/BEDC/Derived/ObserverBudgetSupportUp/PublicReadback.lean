import BEDC.Derived.ObserverBudgetSupportUp.RouteTotality

namespace BEDC.Derived.ObserverBudgetSupportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem ObserverBudgetSupportPublicReadback [AskSetup] [PackageSetup]
    {F S X B T H C P N observerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] →
      Cont F S T →
        Cont X B C →
          Cont T C observerRead →
            Cont observerRead H publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    hsame row publicRead ∧
                      ∃ packet : ObserverBudgetSupportUp,
                        packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                          FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
                  (fun row : BHist =>
                    Cont F S T ∧ Cont X B C ∧ Cont T C observerRead ∧
                      Cont observerRead H row)
                  (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame FieldFaithful
  intro fieldsExact observerRoute causalRoute observerRouteRead publicReadRoute publicPkg
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨publicRead, hsame_refl publicRead,
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
      exact ⟨observerRoute, causalRoute, observerRouteRead, publicReadRoute⟩
    ledger_sound := by
      intro row source
      cases source.left
      exact ⟨hsame_refl publicRead, publicPkg⟩
  }

end BEDC.Derived.ObserverBudgetSupportUp
