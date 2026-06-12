import BEDC.Derived.AxisUnarySpineNormalizerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisUnarySpineNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisUnarySpineNormalizerCarrier [AskSetup] [PackageSetup]
    (nat axis length boundary transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory nat ∧ UnaryHistory axis ∧ UnaryHistory length ∧
    UnaryHistory boundary ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont nat axis length ∧
        Cont length boundary route ∧ Cont transport route provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem AxisUnarySpineNormalizerCarrier_source_boundary [AskSetup] [PackageSetup]
    {nat axis length boundary transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisUnarySpineNormalizerCarrier nat axis length boundary transport route provenance
        localName bundle pkg →
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont nat axis length ∧ Cont length boundary route ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier
  obtain ⟨_natUnary, _axisUnary, lengthUnary, boundaryUnary, transportUnary, routeUnary,
    _provenanceUnary, localNameUnary, natAxisLength, lengthBoundaryRoute,
    transportRouteProvenance, provenancePkg, localNamePkg⟩ := carrier
  have derivedRouteUnary : UnaryHistory route :=
    unary_cont_closed lengthUnary boundaryUnary lengthBoundaryRoute
  have derivedProvenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary routeUnary transportRouteProvenance
  exact
    ⟨derivedRouteUnary, derivedProvenanceUnary, localNameUnary, natAxisLength,
      lengthBoundaryRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.AxisUnarySpineNormalizerUp
