import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverStandardBridgePremise [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead coverRead sealRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory L ∧ UnaryHistory U ∧ UnaryHistory M ∧ UnaryHistory R ∧
      UnaryHistory V ∧ UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory A ∧
        UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
          PkgSig bundle P pkg) →
      Cont L U endpointRead →
        Cont M R coverRead →
          Cont coverRead A sealRead →
            Cont endpointRead sealRead bridgeRead →
              PkgSig bundle bridgeRead pkg →
                UnaryHistory endpointRead ∧ UnaryHistory coverRead ∧
                  UnaryHistory sealRead ∧ UnaryHistory bridgeRead ∧ Cont L U endpointRead ∧
                    Cont M R coverRead ∧ Cont coverRead A sealRead ∧
                      Cont endpointRead sealRead bridgeRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro rows endpointRoute coverRoute sealRoute bridgeRoute bridgePkg
  obtain ⟨lUnary, uUnary, mUnary, rUnary, _vUnary, _wUnary, _qUnary, aUnary,
    _hUnary, _cUnary, _pUnary, _nUnary, pPkg⟩ := rows
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed mUnary rUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed endpointUnary sealUnary bridgeRoute
  exact
    ⟨endpointUnary, coverUnary, sealUnary, bridgeUnary, endpointRoute, coverRoute,
      sealRoute, bridgeRoute, pPkg, bridgePkg⟩

end BEDC.Derived.DyadicIntervalCoverUp
