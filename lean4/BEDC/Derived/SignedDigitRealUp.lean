import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedDigitRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SignedDigitRealPacket [AskSetup] [PackageSetup]
    (stream window enclosure located sealRow transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory enclosure ∧
    UnaryHistory located ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont enclosure located sealRow ∧ Cont transport route provenance ∧
          PkgSig bundle cert pkg

theorem SignedDigitRealPacket_normalization_window_transport [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert normalized : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      Cont stream window normalized ->
        hsame normalized enclosure ->
          UnaryHistory normalized ∧ UnaryHistory enclosure ∧ UnaryHistory located ∧
            UnaryHistory sealRow ∧ hsame normalized enclosure ∧ Cont stream window normalized ∧
              Cont enclosure located sealRow ∧ PkgSig bundle cert pkg := by
  intro packet normalizationRow normalizedSame
  obtain ⟨streamUnary, windowUnary, _enclosureUnary, locatedUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, sealRow, _provenanceRow,
    certSig⟩ := packet
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed streamUnary windowUnary normalizationRow
  have enclosureUnary' : UnaryHistory enclosure :=
    unary_transport normalizedUnary normalizedSame
  exact
    ⟨normalizedUnary, enclosureUnary', locatedUnary, sealUnary, normalizedSame,
      normalizationRow, sealRow, certSig⟩

end BEDC.Derived.SignedDigitRealUp
