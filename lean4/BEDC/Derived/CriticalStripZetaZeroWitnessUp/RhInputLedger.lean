import BEDC.Derived.CriticalStripZetaZeroWitnessUp

namespace BEDC.Derived.CriticalStripZetaZeroWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CriticalStripZetaZeroWitnessCarrier_rh_input_ledger
    [AskSetup] [PackageSetup]
    {strip zero line boundary transport route provenance name rhInput : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CriticalStripZetaZeroWitnessCarrier strip zero line boundary transport route provenance name
        bundle pkg ->
      Cont line boundary rhInput ->
        PkgSig bundle rhInput pkg ->
          UnaryHistory line ∧ UnaryHistory boundary ∧ UnaryHistory rhInput ∧
            Cont line boundary rhInput ∧ Cont strip route provenance ∧
              Cont zero route provenance ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle rhInput pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier rhRoute rhPkg
  obtain ⟨_stripUnary, _zeroUnary, lineUnary, boundaryUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, stripRoute, zeroRoute, provenancePkg⟩ := carrier
  have rhUnary : UnaryHistory rhInput :=
    unary_cont_closed lineUnary boundaryUnary rhRoute
  exact
    ⟨lineUnary, boundaryUnary, rhUnary, rhRoute, stripRoute, zeroRoute, provenancePkg, rhPkg⟩

end BEDC.Derived.CriticalStripZetaZeroWitnessUp
