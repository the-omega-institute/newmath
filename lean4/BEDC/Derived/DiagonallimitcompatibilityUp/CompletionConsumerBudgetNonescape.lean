import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_completion_consumer_budget_nonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector locked endpoint completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal windows selector →
        Cont selector readback locked →
          Cont locked realSeal endpoint →
            Cont endpoint cert completion →
              PkgSig bundle endpoint pkg →
                PkgSig bundle completion pkg →
                  UnaryHistory diagonal ∧ UnaryHistory windows ∧ UnaryHistory readback ∧
                    UnaryHistory realSeal ∧ UnaryHistory selector ∧ UnaryHistory locked ∧
                      UnaryHistory endpoint ∧ UnaryHistory completion ∧
                        Cont diagonal windows selector ∧ Cont selector readback locked ∧
                          Cont locked realSeal endpoint ∧ Cont endpoint cert completion ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg ∧
                              PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalWindowsSelector selectorReadbackLocked lockedRealSealEndpoint
    endpointCertCompletion endpointPkg completionPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed selectorUnary readbackUnary selectorReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed endpointUnary certUnary endpointCertCompletion
  exact
    ⟨diagonalUnary, windowsUnary, readbackUnary, realSealUnary, selectorUnary,
      lockedUnary, endpointUnary, completionUnary, diagonalWindowsSelector,
      selectorReadbackLocked, lockedRealSealEndpoint, endpointCertCompletion,
      provenancePkg, endpointPkg, completionPkg⟩

theorem DiagonalLimitCompatibilityCompletionConsumerBudgetNonescape
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selectorBudget completionConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic selectorBudget ->
        Cont selectorBudget readback completionConsumer ->
          PkgSig bundle completionConsumer pkg ->
            UnaryHistory diagonal ∧ UnaryHistory dyadic ∧ UnaryHistory selectorBudget ∧
              UnaryHistory readback ∧ UnaryHistory completionConsumer ∧
                Cont diagonal dyadic selectorBudget ∧
                  Cont selectorBudget readback completionConsumer ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle completionConsumer pkg ∧
                      SemanticNameCert
                        (fun row : BHist => hsame row completionConsumer ∧ UnaryHistory row)
                        (fun _row : BHist =>
                          Cont diagonal dyadic selectorBudget ∧
                            Cont selectorBudget readback completionConsumer)
                        (fun row : BHist =>
                          hsame row completionConsumer ∧
                            PkgSig bundle completionConsumer pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier diagonalDyadicSelector selectorReadbackConsumer completionConsumerPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, _windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have selectorBudgetUnary : UnaryHistory selectorBudget :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSelector
  have completionConsumerUnary : UnaryHistory completionConsumer :=
    unary_cont_closed selectorBudgetUnary readbackUnary selectorReadbackConsumer
  have sourceCompletion :
      (fun row : BHist => hsame row completionConsumer ∧ UnaryHistory row)
        completionConsumer := by
    exact ⟨hsame_refl completionConsumer, completionConsumerUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row completionConsumer ∧ UnaryHistory row)
        (fun _row : BHist =>
          Cont diagonal dyadic selectorBudget ∧
            Cont selectorBudget readback completionConsumer)
        (fun row : BHist =>
          hsame row completionConsumer ∧ PkgSig bundle completionConsumer pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro completionConsumer sourceCompletion
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row _source
        exact ⟨diagonalDyadicSelector, selectorReadbackConsumer⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, completionConsumerPkg⟩
    }
  exact
    ⟨diagonalUnary, dyadicUnary, selectorBudgetUnary, readbackUnary,
      completionConsumerUnary, diagonalDyadicSelector, selectorReadbackConsumer, provenancePkg,
      completionConsumerPkg, cert⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
