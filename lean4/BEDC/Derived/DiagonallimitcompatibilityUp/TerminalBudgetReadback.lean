import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_terminal_budget_readback
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      budgetPrefix budgetWindow budgetRead terminalRead envelopeRead refinementRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      Cont diagonal dyadic budgetPrefix →
        Cont budgetPrefix windows budgetWindow →
          Cont budgetWindow readback budgetRead →
            Cont budgetRead realSeal terminalRead →
              Cont terminalRead route envelopeRead →
                Cont terminalRead cert refinementRead →
                  PkgSig bundle terminalRead pkg →
                    PkgSig bundle envelopeRead pkg →
                      PkgSig bundle refinementRead pkg →
                        UnaryHistory budgetPrefix ∧ UnaryHistory budgetWindow ∧
                          UnaryHistory budgetRead ∧ UnaryHistory terminalRead ∧
                            UnaryHistory envelopeRead ∧ UnaryHistory refinementRead ∧
                              Cont diagonal dyadic budgetPrefix ∧
                                Cont budgetPrefix windows budgetWindow ∧
                                  Cont budgetWindow readback budgetRead ∧
                                    Cont budgetRead realSeal terminalRead ∧
                                      Cont terminalRead route envelopeRead ∧
                                        Cont terminalRead cert refinementRead ∧
                                          PkgSig bundle provenance pkg ∧
                                            PkgSig bundle terminalRead pkg ∧
                                              PkgSig bundle envelopeRead pkg ∧
                                                PkgSig bundle refinementRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier diagonalDyadicPrefix prefixWindowsBudget budgetWindowRead
    budgetRealTerminal terminalRouteEnvelope terminalCertRefinement terminalPkg envelopePkg
    refinementPkg
  obtain ⟨diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, routeUnary, _provenanceUnary, certUnary,
    _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := carrier
  have budgetPrefixUnary : UnaryHistory budgetPrefix :=
    unary_cont_closed diagonalUnary dyadicUnary diagonalDyadicPrefix
  have budgetWindowUnary : UnaryHistory budgetWindow :=
    unary_cont_closed budgetPrefixUnary windowsUnary prefixWindowsBudget
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed budgetWindowUnary readbackUnary budgetWindowRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed budgetReadUnary realSealUnary budgetRealTerminal
  have envelopeReadUnary : UnaryHistory envelopeRead :=
    unary_cont_closed terminalReadUnary routeUnary terminalRouteEnvelope
  have refinementReadUnary : UnaryHistory refinementRead :=
    unary_cont_closed terminalReadUnary certUnary terminalCertRefinement
  exact
    ⟨budgetPrefixUnary, budgetWindowUnary, budgetReadUnary, terminalReadUnary,
      envelopeReadUnary, refinementReadUnary, diagonalDyadicPrefix, prefixWindowsBudget,
      budgetWindowRead, budgetRealTerminal, terminalRouteEnvelope, terminalCertRefinement,
      provenancePkg, terminalPkg, envelopePkg, refinementPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
