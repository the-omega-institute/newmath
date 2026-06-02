import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_real_cauchy_modulus_handoff [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont order dyadic modulusRead ->
        PkgSig bundle modulusRead pkg ->
          UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
            UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
              UnaryHistory sealRow ∧ UnaryHistory modulusRead ∧ Cont order dyadic modulusRead ∧
                Cont stream readback sealRow ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle modulusRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet modulusRoute modulusPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed orderUnary dyadicUnary modulusRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, dyadicUnary, streamUnary, readbackUnary,
      sealRowUnary, modulusUnary, modulusRoute, sealRoute, provenancePkg, modulusPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
