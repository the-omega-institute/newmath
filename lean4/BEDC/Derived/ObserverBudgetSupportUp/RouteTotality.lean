import BEDC.Derived.ObserverBudgetSupportUp.NameCert

namespace BEDC.Derived.ObserverBudgetSupportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem ObserverBudgetSupportRouteTotality [AskSetup] [PackageSetup]
    {F S X B T H C P N observerRead causalRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] →
      Cont F S T →
        Cont X B C →
          Cont T C observerRead →
            Cont observerRead H publicRead →
              PkgSig bundle N pkg →
                PkgSig bundle publicRead pkg →
                  hsame publicRead publicRead ∧ Cont F S T ∧ Cont X B C ∧
                    Cont T C observerRead ∧ Cont observerRead H publicRead ∧
                      PkgSig bundle N pkg ∧ PkgSig bundle publicRead pkg ∧
                        SemanticNameCert
                          (fun row : BHist =>
                            hsame row publicRead ∧
                              ∃ packet : ObserverBudgetSupportUp,
                                packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                                  FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
                          (fun row : BHist =>
                            Cont F S T ∧ Cont X B C ∧ Cont T C observerRead ∧
                              Cont observerRead H row)
                          (fun row : BHist =>
                            hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro fieldsExact observerRoute causalRoute observerReadRoute publicReadRoute namePkg
    publicPkg
  have _causalReadAnchor : BHist := causalRead
  have publicSelf : hsame publicRead publicRead := hsame_refl publicRead
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row publicRead ∧
            ∃ packet : ObserverBudgetSupportUp,
              packet = ObserverBudgetSupportUp.mk F S X B T H C P N ∧
                FieldFaithful.fields packet = [F, S, X, B, T, H, C, P, N])
        (fun row : BHist =>
          Cont F S T ∧ Cont X B C ∧ Cont T C observerRead ∧ Cont observerRead H row)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := {
      core := {
        carrier_inhabited := by
          exact
            ⟨publicRead, publicSelf,
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
        exact ⟨observerRoute, causalRoute, observerReadRoute, publicReadRoute⟩
      ledger_sound := by
        intro row source
        cases source.left
        exact ⟨hsame_refl publicRead, publicPkg⟩
    }
  exact
    ⟨publicSelf, observerRoute, causalRoute, observerReadRoute, publicReadRoute, namePkg,
      publicPkg, cert⟩

theorem ObserverBudgetSupportLedgerExactness [AskSetup] [PackageSetup]
    {F S X B T H C P N supportBudget causalBudget ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FieldFaithful.fields (ObserverBudgetSupportUp.mk F S X B T H C P N) =
        [F, S, X, B, T, H, C, P, N] ->
      Cont S B supportBudget ->
        Cont X B causalBudget ->
          Cont supportBudget T ledgerRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle ledgerRead pkg ->
                hsame ledgerRead ledgerRead ∧ Cont S B supportBudget ∧
                  Cont X B causalBudget ∧ Cont supportBudget T ledgerRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame FieldFaithful
  intro _fieldsExact supportRoute causalRoute ledgerRoute provenancePkg ledgerPkg
  exact
    ⟨hsame_refl ledgerRead, supportRoute, causalRoute, ledgerRoute, provenancePkg,
      ledgerPkg⟩

end BEDC.Derived.ObserverBudgetSupportUp
