import BEDC.Derived.AxisBoundaryLimitRefusalUp.TasteGate
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisBoundaryLimitRefusalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisBoundaryLimitRefusalCarrier [AskSetup] [PackageSetup]
    (axis boundary limitRefusal realRefusal completenessRefusal transport route provenance
      name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory axis ∧ UnaryHistory boundary ∧ UnaryHistory limitRefusal ∧
    UnaryHistory realRefusal ∧ UnaryHistory completenessRefusal ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont axis boundary limitRefusal ∧ Cont limitRefusal realRefusal completenessRefusal ∧
          Cont completenessRefusal transport route ∧ Cont route provenance name ∧
            PkgSig bundle name pkg

theorem AxisBoundaryLimitRefusalCarrier_nonescape [AskSetup] [PackageSetup]
    {axis boundary limitRefusal realRefusal completenessRefusal transport route provenance name
      readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisBoundaryLimitRefusalCarrier axis boundary limitRefusal realRefusal completenessRefusal
        transport route provenance name bundle pkg →
      Cont name route readback →
        PkgSig bundle readback pkg →
          UnaryHistory axis ∧ UnaryHistory boundary ∧ UnaryHistory limitRefusal ∧
            UnaryHistory name ∧ UnaryHistory readback ∧
              Cont axis boundary limitRefusal ∧
                Cont limitRefusal realRefusal completenessRefusal ∧
                  Cont completenessRefusal transport route ∧ Cont route provenance name ∧
                    Cont name route readback ∧ PkgSig bundle name pkg ∧
                      PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier nameRouteReadback readbackPkg
  obtain ⟨axisUnary, boundaryUnary, limitRefusalUnary, _realRefusalUnary,
    _completenessRefusalUnary, _transportUnary, routeUnary, _provenanceUnary,
    nameUnary, axisBoundaryLimitRefusal, limitRealCompleteness,
    completenessTransportRoute, routeProvenanceName, namePkg⟩ := carrier
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed nameUnary routeUnary nameRouteReadback
  exact
    ⟨axisUnary, boundaryUnary, limitRefusalUnary, nameUnary, readbackUnary,
      axisBoundaryLimitRefusal, limitRealCompleteness, completenessTransportRoute,
      routeProvenanceName, nameRouteReadback, namePkg, readbackPkg⟩

end BEDC.Derived.AxisBoundaryLimitRefusalUp
