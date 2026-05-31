import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealSpectrumUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealSpectrumCarrier [AskSetup] [PackageSetup]
    (algebra element operator realSeal regseq windows resolvent radius readback transport replay
      provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory algebra ∧ UnaryHistory element ∧ UnaryHistory operator ∧
    UnaryHistory realSeal ∧ UnaryHistory regseq ∧ UnaryHistory windows ∧
      UnaryHistory resolvent ∧ UnaryHistory radius ∧ UnaryHistory readback ∧
        UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
          UnaryHistory nameRow ∧ Cont windows regseq realSeal ∧
            Cont resolvent radius readback ∧ Cont readback realSeal replay ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg

theorem RealSpectrumCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {algebra element operator realSeal regseq windows resolvent radius readback transport replay
      provenance nameRow endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealSpectrumCarrier algebra element operator realSeal regseq windows resolvent radius
        readback transport replay provenance nameRow bundle pkg ->
      Cont windows regseq realSeal ->
        Cont resolvent radius readback ->
          Cont readback realSeal endpoint ->
            PkgSig bundle endpoint pkg ->
              UnaryHistory algebra ∧ UnaryHistory element ∧ UnaryHistory realSeal ∧
                UnaryHistory regseq ∧ UnaryHistory windows ∧ UnaryHistory resolvent ∧
                  UnaryHistory radius ∧ UnaryHistory readback ∧ UnaryHistory endpoint ∧
                    Cont windows regseq realSeal ∧ Cont resolvent radius readback ∧
                      Cont readback realSeal endpoint ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier scalarWindowRoute resolventRadiusRoute readbackEndpointRoute endpointPkg
  obtain ⟨algebraUnary, elementUnary, _operatorUnary, realSealUnary, regseqUnary,
    windowsUnary, resolventUnary, radiusUnary, readbackUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameRowUnary, _carrierScalarWindowRoute,
    _carrierResolventRadiusRoute, _carrierReadbackReplayRoute, provenancePkg, _nameRowPkg⟩ :=
      carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed readbackUnary realSealUnary readbackEndpointRoute
  exact
    ⟨algebraUnary, elementUnary, realSealUnary, regseqUnary, windowsUnary, resolventUnary,
      radiusUnary, readbackUnary, endpointUnary, scalarWindowRoute, resolventRadiusRoute,
      readbackEndpointRoute, provenancePkg, endpointPkg⟩

end BEDC.Derived.RealSpectrumUp
