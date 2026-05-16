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

theorem DiagonalLimitCompatibilitySelectorBudgetClassifierPullback [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      selector request sealBudget tail sync locked endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory request ->
        UnaryHistory tail ->
          Cont diagonal windows selector ->
            Cont selector request sealBudget ->
              Cont sealBudget tail sync ->
                Cont sync readback locked ->
                  Cont locked realSeal endpoint ->
                    PkgSig bundle endpoint pkg ->
                      SemanticNameCert
                        (fun row : BHist =>
                          DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic
                            windows readback realSeal transport route provenance cert bundle pkg /\
                              hsame row endpoint)
                        (fun row : BHist =>
                          Cont diagonal windows selector /\
                            Cont selector request sealBudget /\
                              Cont sealBudget tail sync /\
                                Cont sync readback locked /\
                                  Cont locked realSeal row /\ PkgSig bundle endpoint pkg)
                        (fun row : BHist => UnaryHistory row /\ PkgSig bundle endpoint pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier requestUnary tailUnary diagonalWindowsSelector selectorRequestSealBudget
    sealBudgetTailSync syncReadbackLocked lockedRealSealEndpoint endpointPkg
  have carrierWitness := carrier
  obtain
    ⟨diagonalUnary, _triangleUnary, _sealRowUnary, _dyadicUnary, windowsUnary,
      readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
      _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
      _routeCertTransport, _provenancePkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed diagonalUnary windowsUnary diagonalWindowsSelector
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed selectorUnary requestUnary selectorRequestSealBudget
  have syncUnary : UnaryHistory sync :=
    unary_cont_closed sealBudgetUnary tailUnary sealBudgetTailSync
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed syncUnary readbackUnary syncReadbackLocked
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed lockedUnary realSealUnary lockedRealSealEndpoint
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrierWitness (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      exact
        ⟨diagonalWindowsSelector, selectorRequestSealBudget, sealBudgetTailSync,
          syncReadbackLocked, cont_result_hsame_transport lockedRealSealEndpoint
            (hsame_symm source.right), endpointPkg⟩
    ledger_sound := by
      intro row source
      exact And.intro (unary_transport endpointUnary (hsame_symm source.right)) endpointPkg
  }

end BEDC.Derived.DiagonallimitcompatibilityUp
