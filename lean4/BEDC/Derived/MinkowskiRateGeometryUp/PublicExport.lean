import BEDC.Derived.MinkowskiRateGeometryUp.Carrier

namespace BEDC.Derived.MinkowskiRateGeometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MinkowskiRateGeometry_public_export_route [AskSetup] [PackageSetup]
    {G X R L D H C P N geometryRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinkowskiRateGeometryCarrier G X R L D H C P N bundle pkg →
      Cont L D geometryRead →
        Cont geometryRead P publicRead →
          PkgSig bundle geometryRead pkg →
            PkgSig bundle publicRead pkg →
              UnaryHistory geometryRead ∧ UnaryHistory publicRead ∧
                Cont L D geometryRead ∧ Cont geometryRead P publicRead ∧
                  PkgSig bundle geometryRead pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier frameDistanceGeometry geometryPublic geometryPkg publicPkg
  obtain ⟨_configUnary, _causalUnary, _rateUnary, frameUnary, distanceUnary,
    _transportUnary, _replayUnary, provenanceUnary, _localNameUnary, _configCausalRate,
    _rateFrameDistance, _distanceTransportReplay, _distancePkg, _provenancePkg,
    _localNamePkg⟩ := carrier
  have geometryUnary : UnaryHistory geometryRead :=
    unary_cont_closed frameUnary distanceUnary frameDistanceGeometry
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed geometryUnary provenanceUnary geometryPublic
  exact
    ⟨geometryUnary, publicUnary, frameDistanceGeometry, geometryPublic, geometryPkg,
      publicPkg⟩

end BEDC.Derived.MinkowskiRateGeometryUp
