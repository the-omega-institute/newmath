import BEDC.Derived.ObserverBudgetSupportUp.PublicReadback

namespace BEDC.Derived.ObserverBudgetSupportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem ObserverBudgetSupportObligationClosurePackage [AskSetup] [PackageSetup]
    {F S X B T H C P N observerRead publicRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] →
      Cont F S T →
        Cont X B C →
          Cont T C observerRead →
            Cont observerRead H publicRead →
              Cont publicRead P closureRead →
                PkgSig bundle N pkg →
                  PkgSig bundle closureRead pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row closureRead ∧
                          ∃ packet : ObserverBudgetSupportUp,
                            packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                              FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
                      (fun row : BHist =>
                        Cont F S T ∧ Cont X B C ∧ Cont T C observerRead ∧
                          Cont observerRead H publicRead ∧ Cont publicRead P row)
                      (fun row : BHist =>
                        hsame row closureRead ∧ PkgSig bundle closureRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame FieldFaithful
  intro fieldsExact observerRoute causalRoute observerRouteRead publicReadRoute closureRoute
    _namePkg closurePkg
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨closureRead, hsame_refl closureRead,
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
      exact
        ⟨observerRoute, causalRoute, observerRouteRead, publicReadRoute, closureRoute⟩
    ledger_sound := by
      intro row source
      cases source.left
      exact ⟨hsame_refl closureRead, closurePkg⟩
  }

end BEDC.Derived.ObserverBudgetSupportUp
