import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_source_cover_boundary [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported finiteCover coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg →
      Cont dyadic stream finiteCover →
        Cont finiteCover sealRow coverRead →
          PkgSig bundle coverRead pkg →
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory finiteCover ∧
                  UnaryHistory coverRead ∧ Cont lower upper order ∧
                    Cont order rational dyadic ∧ Cont stream readback sealRow ∧
                      Cont dyadic stream finiteCover ∧ Cont finiteCover sealRow coverRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle coverRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet dyadicStream finiteCoverSeal coverPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, endpointRoute, containmentRoute, sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have finiteCoverUnary : UnaryHistory finiteCover :=
    unary_cont_closed dyadicUnary streamUnary dyadicStream
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed finiteCoverUnary sealRowUnary finiteCoverSeal
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, finiteCoverUnary, coverReadUnary, endpointRoute,
      containmentRoute, sealRowRoute, dyadicStream, finiteCoverSeal, provenancePkg, coverPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
