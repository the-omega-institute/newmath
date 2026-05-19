import BEDC.Derived.ObserverBudgetSupportUp.RouteTotality

namespace BEDC.Derived.ObserverBudgetSupportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem ObserverBudgetSupport_bridge_surface [AskSetup] [PackageSetup]
    {F S X B T H C P N observerRead publicRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] →
      Cont F S T →
        Cont X B C →
          Cont T C observerRead →
            Cont observerRead H publicRead →
              Cont publicRead P bridgeRead →
                PkgSig bundle N pkg →
                  PkgSig bundle bridgeRead pkg →
                    SemanticNameCert
                      (fun row : BHist =>
                        hsame row bridgeRead ∧
                          ∃ packet : ObserverBudgetSupportUp,
                            packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                              FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
                      (fun row : BHist =>
                        Cont F S T ∧ Cont X B C ∧ Cont T C observerRead ∧
                          Cont observerRead H publicRead ∧ Cont publicRead P row)
                      (fun row : BHist =>
                        hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
                      hsame ∧
                    PkgSig bundle N pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame FieldFaithful
  intro fieldsExact observerRoute causalRoute observerReadRoute publicReadRoute bridgeRoute
    namePkg bridgePkg
  have bridgeSelf : hsame bridgeRead bridgeRead := hsame_refl bridgeRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row bridgeRead ∧
            ∃ packet : ObserverBudgetSupportUp,
              packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
        (fun row : BHist =>
          Cont F S T ∧ Cont X B C ∧ Cont T C observerRead ∧
            Cont observerRead H publicRead ∧ Cont publicRead P row)
        (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
        hsame := {
      core := {
        carrier_inhabited := by
          exact
            ⟨bridgeRead, bridgeSelf,
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
        exact ⟨observerRoute, causalRoute, observerReadRoute, publicReadRoute, bridgeRoute⟩
      ledger_sound := by
        intro row source
        cases source.left
        exact ⟨hsame_refl bridgeRead, bridgePkg⟩
    }
  exact ⟨cert, namePkg, bridgePkg⟩

end BEDC.Derived.ObserverBudgetSupportUp
