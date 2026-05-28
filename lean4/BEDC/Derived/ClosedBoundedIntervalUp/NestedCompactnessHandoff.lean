import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_nested_compactness_handoff [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported nestedRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont dyadic stream nestedRead →
        Cont nestedRead sealRow compactRead →
          PkgSig bundle compactRead pkg →
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory nestedRead ∧
                  UnaryHistory compactRead ∧ Cont dyadic stream nestedRead ∧
                    Cont nestedRead sealRow compactRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet nestedRoute compactRoute compactPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, _endpointRoute, _containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have nestedUnary : UnaryHistory nestedRead :=
    unary_cont_closed dyadicUnary streamUnary nestedRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed nestedUnary sealRowUnary compactRoute
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, nestedUnary, compactUnary, nestedRoute, compactRoute,
      provenancePkg, compactPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
