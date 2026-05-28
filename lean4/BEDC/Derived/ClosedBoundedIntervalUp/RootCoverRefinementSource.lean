import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_root_cover_refinement_source [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported refinement : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic sealRow refinement ->
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
          UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
            UnaryHistory sealRow ∧ UnaryHistory refinement ∧ Cont order rational dyadic ∧
              Cont dyadic sealRow refinement ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet refinementRoute
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, dyadicRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have refinementUnary : UnaryHistory refinement :=
    unary_cont_closed dyadicUnary sealRowUnary refinementRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, refinementUnary, dyadicRoute, refinementRoute,
      provenancePkg, localNamePkg⟩

end BEDC.Derived.ClosedboundedintervalUp
