import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_cantor_intersection_handoff [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported nestedRead cantorRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont dyadic stream nestedRead →
        Cont nestedRead sealRow cantorRead →
          PkgSig bundle cantorRead pkg →
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory dyadic ∧
              UnaryHistory stream ∧ UnaryHistory nestedRead ∧ UnaryHistory cantorRead ∧
                Cont lower upper order ∧ Cont dyadic stream nestedRead ∧
                  Cont nestedRead sealRow cantorRead ∧ Cont transport replay provenance ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle cantorRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet nestedRoute cantorRoute cantorPkg
  obtain ⟨lowerUnary, upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    _readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, endpointRoute, _containmentRoute, _sealRoute,
    replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed dyadicUnary streamUnary nestedRoute
  have cantorUnary : UnaryHistory cantorRead :=
    unary_cont_closed nestedUnary sealRowUnary cantorRoute
  exact
    ⟨lowerUnary, upperUnary, dyadicUnary, streamUnary, nestedUnary, cantorUnary,
      endpointRoute, nestedRoute, cantorRoute, replayRoute, provenancePkg, cantorPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
