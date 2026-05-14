import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCompletionConsumerGate [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      source mesh locked budgetPrefix sealBudget completion : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      Cont diagonal dyadic source ->
        Cont source windows mesh ->
          Cont mesh triangle locked ->
            Cont dyadic windows budgetPrefix ->
              Cont budgetPrefix sealRow sealBudget ->
                Cont readback realSeal completion ->
                  PkgSig bundle locked pkg ->
                    PkgSig bundle sealBudget pkg ->
                      PkgSig bundle completion pkg ->
                        UnaryHistory source ∧ UnaryHistory mesh ∧ UnaryHistory locked ∧
                          UnaryHistory budgetPrefix ∧ UnaryHistory sealBudget ∧
                            UnaryHistory completion ∧ Cont diagonal dyadic source ∧
                              Cont source windows mesh ∧ Cont mesh triangle locked ∧
                                Cont dyadic windows budgetPrefix ∧
                                  Cont budgetPrefix sealRow sealBudget ∧
                                    Cont readback realSeal completion ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle locked pkg ∧
                                          PkgSig bundle sealBudget pkg ∧
                                            PkgSig bundle completion pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro carrier diagonalDyadicSource sourceWindowsMesh meshTriangleLocked
    dyadicWindowsBudgetPrefix budgetPrefixSealRow readbackRealSealCompletion lockedPkg
    sealBudgetPkg completionPkg
  obtain ⟨diagonalUnary, triangleUnary, sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have sourceUnary : UnaryHistory source :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicSource
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed sourceUnary windowsUnary sourceWindowsMesh
  have lockedUnary : UnaryHistory locked :=
    unary_cont_closed meshUnary triangleUnary meshTriangleLocked
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed dyadicUnary windowsUnary dyadicWindowsBudgetPrefix
  have sealBudgetUnary : UnaryHistory sealBudget :=
    unary_cont_closed budgetPrefixUnary sealRowUnary budgetPrefixSealRow
  have completionUnary : UnaryHistory completion :=
    unary_cont_closed readbackUnary realSealUnary readbackRealSealCompletion
  exact
    ⟨sourceUnary, meshUnary, lockedUnary, budgetPrefixUnary, sealBudgetUnary,
      completionUnary, diagonalDyadicSource, sourceWindowsMesh, meshTriangleLocked,
      dyadicWindowsBudgetPrefix, budgetPrefixSealRow, readbackRealSealCompletion,
      provenancePkg, lockedPkg, sealBudgetPkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
