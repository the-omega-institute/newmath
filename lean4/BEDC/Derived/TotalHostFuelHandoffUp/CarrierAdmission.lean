import BEDC.Derived.TotalHostFuelHandoffUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TotalHostFuelHandoffUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotalHostFuelHandoffCarrierAdmission [AskSetup] [PackageSetup]
    {host fuel substrate trace readback refusal transport route provenance name terminalRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory host →
      UnaryHistory fuel →
        UnaryHistory substrate →
          UnaryHistory trace →
            UnaryHistory readback →
              UnaryHistory name →
                Cont host fuel substrate →
                  Cont substrate trace terminalRead →
                    Cont terminalRead readback namedRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle namedRead pkg →
                          UnaryHistory terminalRead ∧ UnaryHistory namedRead ∧
                            Cont host fuel substrate ∧ Cont substrate trace terminalRead ∧
                              Cont terminalRead readback namedRead ∧
                                PkgSig bundle provenance pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro hostUnary fuelUnary substrateUnary traceUnary readbackUnary _nameUnary hostFuelRoute
    substrateTraceRoute terminalReadRoute provenancePkg namedReadPkg
  have refusedBoundaryRow : BHist := refusal
  have transportBoundaryRow : BHist := transport
  have routeBoundaryRow : BHist := route
  have _boundaryRows : BHist × BHist × BHist :=
    (refusedBoundaryRow, transportBoundaryRow, routeBoundaryRow)
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed substrateUnary traceUnary substrateTraceRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed terminalReadUnary readbackUnary terminalReadRoute
  exact
    ⟨terminalReadUnary, namedReadUnary, hostFuelRoute, substrateTraceRoute,
      terminalReadRoute, provenancePkg, namedReadPkg⟩

end BEDC.Derived.TotalHostFuelHandoffUp
