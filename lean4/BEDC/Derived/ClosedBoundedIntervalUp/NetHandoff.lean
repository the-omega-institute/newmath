import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_net_handoff [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported mesh coverage : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream mesh ->
        Cont mesh exported coverage ->
          PkgSig bundle coverage pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory mesh ∧
                UnaryHistory coverage ∧ Cont lower upper order ∧ Cont order rational dyadic ∧
                  Cont dyadic stream mesh ∧ Cont mesh exported coverage ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                      PkgSig bundle coverage pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet dyadicStreamMesh meshExportedCoverage coveragePkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, endpointRoute, containmentRoute, _sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have meshUnary : UnaryHistory mesh :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamMesh
  have coverageUnary : UnaryHistory coverage :=
    unary_cont_closed meshUnary exportedUnary meshExportedCoverage
  exact
    ⟨lowerUnary, upperUnary, orderUnary, dyadicUnary, streamUnary, meshUnary, coverageUnary,
      endpointRoute, containmentRoute, dyadicStreamMesh, meshExportedCoverage, provenancePkg,
      localNamePkg, coveragePkg⟩

end BEDC.Derived.ClosedboundedintervalUp
