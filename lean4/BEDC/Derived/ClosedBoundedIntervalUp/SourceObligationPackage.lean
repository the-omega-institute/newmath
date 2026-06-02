import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_source_obligation_package [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported sourceWindow sourceOut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      Cont dyadic stream sourceWindow ->
        Cont sourceWindow sealRow sourceOut ->
          PkgSig bundle sourceOut pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory sourceWindow ∧
                  UnaryHistory sourceOut ∧ Cont lower upper order ∧
                    Cont order rational dyadic ∧ Cont stream readback sealRow ∧
                      Cont dyadic stream sourceWindow ∧
                        Cont sourceWindow sealRow sourceOut ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sourceOut pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet dyadicStreamSource sourceSealOut sourceOutPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _exportedUnary, endpointRoute, containmentRoute, sealRowRoute,
    _replayRoute, _nameRoute, provenancePkg, _localNamePkg⟩ := packet
  have sourceWindowUnary : UnaryHistory sourceWindow :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSource
  have sourceOutUnary : UnaryHistory sourceOut :=
    unary_cont_closed sourceWindowUnary sealRowUnary sourceSealOut
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, sourceWindowUnary, sourceOutUnary, endpointRoute,
      containmentRoute, sealRowRoute, dyadicStreamSource, sourceSealOut, provenancePkg,
      sourceOutPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
