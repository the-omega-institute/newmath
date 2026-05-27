import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_downstream_coverage_surface [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported netRead coverRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory netRead ->
        Cont dyadic netRead coverRead ->
          Cont sealRow coverRead modulusRead ->
            PkgSig bundle modulusRead pkg ->
              UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory dyadic ∧
                UnaryHistory sealRow ∧ UnaryHistory coverRead ∧ UnaryHistory modulusRead ∧
                  Cont dyadic netRead coverRead ∧ Cont sealRow coverRead modulusRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet netReadUnary coverRoute modulusRoute modulusPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, dyadicUnary,
    _streamUnary, _readbackUnary, sealRowUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _exportedUnary, _endpointRoute,
    _containmentRoute, _sealRoute, _replayRoute, _nameRoute, provenancePkg,
    _localNamePkg⟩ := packet
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed dyadicUnary netReadUnary coverRoute
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sealRowUnary coverReadUnary modulusRoute
  exact
    ⟨lowerUnary, upperUnary, dyadicUnary, sealRowUnary, coverReadUnary,
      modulusReadUnary, coverRoute, modulusRoute, provenancePkg, modulusPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
