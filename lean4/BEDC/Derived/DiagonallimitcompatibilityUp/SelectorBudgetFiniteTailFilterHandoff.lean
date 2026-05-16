import BEDC.Derived.DiagonallimitcompatibilityUp
import BEDC.Derived.FiniteTailFilterUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.Derived.FiniteTailFilterUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityCarrier_selector_budget_finite_tail_filter_handoff
    [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert :
      BHist}
    {S D R B Q E Hf Cf Pf Nf finiteSeal realRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      FiniteTailFilterCarrier S D R B Q E Hf Cf Pf Nf →
        hsame S windows →
          hsame D dyadic →
            hsame R readback →
              hsame E realSeal →
                UnaryHistory Hf →
                  UnaryHistory Cf →
                    Cont Q E finiteSeal →
                      Cont finiteSeal Hf realRead →
                        Cont realRead Cf completionRead →
                          PkgSig bundle completionRead pkg →
                            UnaryHistory windows ∧ UnaryHistory dyadic ∧
                              UnaryHistory readback ∧ UnaryHistory realSeal ∧
                                UnaryHistory finiteSeal ∧ UnaryHistory realRead ∧
                                  UnaryHistory completionRead ∧
                                    FiniteTailFilterCarrier S D R B Q E Hf Cf Pf Nf ∧
                                      PkgSig bundle provenance pkg ∧
                                        PkgSig bundle completionRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame
  intro diagonalCarrier filterCarrier sameSWindows sameDDyadic sameRReadback sameERealSeal
    unaryHf unaryCf finiteSealRoute realReadRoute completionReadRoute completionPkg
  obtain ⟨_diagonalUnary, _triangleUnary, _sealRowUnary, dyadicUnary, windowsUnary,
    readbackUnary, realSealUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _certUnary, _diagonalTriangleSeal, _dyadicWindowsReadback, _readbackRealSealRoute,
    _routeCertTransport, provenancePkg⟩ := diagonalCarrier
  obtain ⟨unaryS, unaryD, unaryB, unaryE, _unaryCarrierHf, unaryCarrierPf, routeR,
    routeQ, sameNE⟩ := filterCarrier
  have unaryR : UnaryHistory R :=
    unary_cont_closed unaryS unaryD routeR
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryR unaryB routeQ
  have finiteSealUnary : UnaryHistory finiteSeal :=
    unary_cont_closed unaryQ unaryE finiteSealRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed finiteSealUnary unaryHf realReadRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed realReadUnary unaryCf completionReadRoute
  have filterPacket : FiniteTailFilterCarrier S D R B Q E Hf Cf Pf Nf :=
    ⟨unaryS, unaryD, unaryB, unaryE, unaryHf, unaryCarrierPf, routeR, routeQ, sameNE⟩
  exact
    ⟨windowsUnary, dyadicUnary, readbackUnary, realSealUnary, finiteSealUnary,
      realReadUnary, completionReadUnary, filterPacket, provenancePkg, completionPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
