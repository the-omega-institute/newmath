import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StableManifoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StableManifoldCarrier [AskSetup] [PackageSetup]
    (equilibrium flow ode chart contraction tangent transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory equilibrium ∧ UnaryHistory flow ∧ UnaryHistory ode ∧ UnaryHistory chart ∧
    UnaryHistory contraction ∧ UnaryHistory tangent ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem StableManifoldCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {equilibrium flow ode chart contraction tangent transport replay provenance localName
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StableManifoldCarrier equilibrium flow ode chart contraction tangent transport replay provenance
        localName bundle pkg →
      Cont flow chart endpointRead →
        PkgSig bundle endpointRead pkg →
          UnaryHistory equilibrium ∧ UnaryHistory flow ∧ UnaryHistory ode ∧
            UnaryHistory chart ∧ UnaryHistory contraction ∧ UnaryHistory tangent ∧
              Cont flow chart endpointRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointRoute endpointPkg
  obtain ⟨equilibriumUnary, flowUnary, odeUnary, chartUnary, contractionUnary, tangentUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    _localNamePkg⟩ := carrier
  exact
    ⟨equilibriumUnary, flowUnary, odeUnary, chartUnary, contractionUnary, tangentUnary,
      endpointRoute, provenancePkg, endpointPkg⟩

theorem StableManifoldFlowInvariance [AskSetup] [PackageSetup]
    {equilibrium flow ode chart contraction tangent transport replay provenance localName
      endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StableManifoldCarrier equilibrium flow ode chart contraction tangent transport replay provenance
        localName bundle pkg →
      Cont flow chart endpointRead →
        Cont transport replay provenance →
          PkgSig bundle endpointRead pkg →
            UnaryHistory flow ∧ UnaryHistory chart ∧ UnaryHistory tangent ∧
              Cont flow chart endpointRead ∧ Cont transport replay provenance ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle endpointRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier endpointRoute replayRoute endpointPkg
  obtain ⟨_equilibriumUnary, flowUnary, _odeUnary, chartUnary, _contractionUnary, tangentUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, provenancePkg,
    _localNamePkg⟩ := carrier
  exact
    ⟨flowUnary, chartUnary, tangentUnary, endpointRoute, replayRoute, provenancePkg,
      endpointPkg⟩

end BEDC.Derived.StableManifoldUp
