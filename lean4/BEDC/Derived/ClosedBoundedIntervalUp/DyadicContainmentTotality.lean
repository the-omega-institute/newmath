import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedBoundedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.ClosedboundedintervalUp

theorem ClosedBoundedIntervalPacket_dyadic_containment_totality [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported containmentRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont rational dyadic containmentRead →
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
          UnaryHistory dyadic ∧ UnaryHistory containmentRead ∧
            Cont rational dyadic containmentRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro packet containmentRoute
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, _streamUnary,
    _readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _carrierContainmentRoute,
    _sealRowRoute, _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have containmentUnary : UnaryHistory containmentRead :=
    unary_cont_closed rationalUnary dyadicUnary containmentRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, containmentUnary,
      containmentRoute, provenancePkg⟩

end BEDC.Derived.ClosedBoundedIntervalUp
