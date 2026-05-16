import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_terminal_modulus_budget_comparison
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      uniformSource uniformModulus uniformTail uniformSeal refinementMeet refinementExtract
      refinementBudget refinementWindow refinementReadback refinementSeal terminal commonConsumer :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg ->
      UnaryHistory uniformSeal ->
        UnaryHistory refinementExtract ->
          UnaryHistory refinementWindow ->
            UnaryHistory refinementSeal ->
              Cont uniformSource uniformModulus uniformTail ->
                Cont uniformTail windows readback ->
                  Cont readback uniformSeal commonConsumer ->
                    Cont diagonal dyadic refinementMeet ->
                      Cont refinementMeet refinementExtract refinementBudget ->
                        Cont refinementBudget refinementWindow refinementReadback ->
                          Cont refinementReadback refinementSeal terminal ->
                            PkgSig bundle commonConsumer pkg ->
                              PkgSig bundle terminal pkg ->
                                UnaryHistory windows ∧ UnaryHistory readback ∧
                                  UnaryHistory uniformTail ∧
                                    UnaryHistory commonConsumer ∧
                                      UnaryHistory refinementMeet ∧
                                        UnaryHistory refinementBudget ∧
                                          UnaryHistory refinementReadback ∧
                                            UnaryHistory terminal ∧
                                              Cont uniformTail windows readback ∧
                                                Cont readback uniformSeal commonConsumer ∧
                                                  Cont refinementBudget refinementWindow
                                                    refinementReadback ∧
                                                    Cont refinementReadback refinementSeal terminal ∧
                                                      PkgSig bundle commonConsumer pkg ∧
                                                        PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier uniformSealUnary refinementExtractUnary refinementWindowUnary refinementSealUnary
    _uniformSourceModulusTail uniformTailWindowsReadback
    readbackUniformSealConsumer diagonalDyadicRefinementMeet refinementMeetExtractBudget
    refinementBudgetWindowReadback refinementReadbackSealTerminal commonConsumerPkg terminalPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, _realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, _provenancePkg⟩ := carrier
  have uniformTailUnary : UnaryHistory uniformTail :=
    unary_cont_left_factor uniformTailWindowsReadback readbackUnary
  have commonConsumerUnary : UnaryHistory commonConsumer :=
    unary_cont_closed readbackUnary uniformSealUnary readbackUniformSealConsumer
  have refinementMeetUnary : UnaryHistory refinementMeet :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicRefinementMeet
  have refinementBudgetUnary : UnaryHistory refinementBudget :=
    unary_cont_closed refinementMeetUnary refinementExtractUnary refinementMeetExtractBudget
  have refinementReadbackUnary : UnaryHistory refinementReadback :=
    unary_cont_closed refinementBudgetUnary refinementWindowUnary refinementBudgetWindowReadback
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed refinementReadbackUnary refinementSealUnary refinementReadbackSealTerminal
  exact
    ⟨windowsUnary, readbackUnary, uniformTailUnary, commonConsumerUnary, refinementMeetUnary,
      refinementBudgetUnary, refinementReadbackUnary, terminalUnary, uniformTailWindowsReadback,
      readbackUniformSealConsumer, refinementBudgetWindowReadback, refinementReadbackSealTerminal,
      commonConsumerPkg, terminalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
