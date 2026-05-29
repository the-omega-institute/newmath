import BEDC.Derived.ClosedboundedintervalUp

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedBoundedIntervalPacket_located_cover_source_totality [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName exported coverWindow coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalPacket lower upper order rational dyadic stream readback sealRow
        transport replay provenance localName exported bundle pkg ->
      UnaryHistory coverWindow ->
        Cont exported coverWindow coverRead ->
          PkgSig bundle coverRead pkg ->
            UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧
              UnaryHistory rational ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
                UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory exported ∧
                  UnaryHistory coverWindow ∧ UnaryHistory coverRead ∧ Cont lower upper order ∧
                    Cont order rational dyadic ∧ Cont exported coverWindow coverRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle coverRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro packet coverWindowUnary exportedCoverWindow coverPkg
  obtain ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, exportedUnary, endpointRoute, containmentRoute, _sealRoute,
    _replayRoute, _nameRoute, provenancePkg, localNamePkg⟩ := packet
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed exportedUnary coverWindowUnary exportedCoverWindow
  exact
    ⟨lowerUnary, upperUnary, orderUnary, rationalUnary, dyadicUnary, streamUnary,
      readbackUnary, sealRowUnary, exportedUnary, coverWindowUnary, coverReadUnary,
      endpointRoute, containmentRoute, exportedCoverWindow, provenancePkg, localNamePkg,
      coverPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
