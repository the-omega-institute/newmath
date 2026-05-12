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

theorem SignedDigitRealPacket_dyadic_seal_compatibility [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert
      stream' window' enclosure' located' sealRow' transport' route' provenance' cert' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      SignedDigitRealPacket stream' window' enclosure' located' sealRow' transport' route'
          provenance' cert' bundle' pkg' ->
        hsame enclosure enclosure' ->
          hsame located located' ->
            hsame sealRow sealRow' ∧ UnaryHistory sealRow ∧ UnaryHistory sealRow' ∧
              Cont enclosure located sealRow ∧ Cont enclosure' located' sealRow' ∧
                PkgSig bundle cert pkg ∧ PkgSig bundle' cert' pkg' := by
  intro packet packet' sameEnclosure sameLocated
  obtain ⟨_streamUnary, _windowUnary, _enclosureUnary, _locatedUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, sealCont,
    _provenanceCont, certSig⟩ := packet
  obtain ⟨_streamUnary', _windowUnary', _enclosureUnary', _locatedUnary', sealUnary',
    _transportUnary', _routeUnary', _provenanceUnary', _certUnary', sealCont',
    _provenanceCont', certSig'⟩ := packet'
  have sameSeal : hsame sealRow sealRow' :=
    cont_respects_hsame sameEnclosure sameLocated sealCont sealCont'
  exact ⟨sameSeal, sealUnary, sealUnary', sealCont, sealCont', certSig, certSig'⟩

theorem SignedDigitRealPacket_window_classifier_stability [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert normalized
      stream' window' enclosure' located' sealRow' transport' route' provenance' cert'
      normalized' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      SignedDigitRealPacket stream' window' enclosure' located' sealRow' transport' route'
          provenance' cert' bundle' pkg' ->
        Cont stream window normalized ->
          Cont stream' window' normalized' ->
            hsame stream stream' ->
              hsame window window' ->
                hsame normalized enclosure ->
                  hsame normalized' enclosure' ->
                    hsame located located' ->
                      hsame normalized normalized' ∧ hsame enclosure enclosure' ∧
                        hsame sealRow sealRow' ∧ Cont enclosure located sealRow ∧
                          Cont enclosure' located' sealRow' ∧ PkgSig bundle cert pkg ∧
                            PkgSig bundle' cert' pkg' := by
  intro packet packet' normalizationRow normalizationRow' sameStream sameWindow
    sameNormalizedEnclosure sameNormalizedEnclosure' sameLocated
  have sameNormalized : hsame normalized normalized' :=
    cont_respects_hsame sameStream sameWindow normalizationRow normalizationRow'
  have sameEnclosure : hsame enclosure enclosure' :=
    hsame_trans (hsame_trans (hsame_symm sameNormalizedEnclosure) sameNormalized)
      sameNormalizedEnclosure'
  have sealRows :=
    SignedDigitRealPacket_dyadic_seal_compatibility packet packet' sameEnclosure sameLocated
  exact
    ⟨sameNormalized, sameEnclosure, sealRows.left, sealRows.right.right.right.left,
      sealRows.right.right.right.right.left, sealRows.right.right.right.right.right.left,
      sealRows.right.right.right.right.right.right⟩

theorem SignedDigitRealPacket_seal_ledger_exactness [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      Cont enclosure located sealRead ->
        hsame sealRead sealRow ->
          UnaryHistory enclosure ∧ UnaryHistory located ∧ UnaryHistory sealRow ∧
            UnaryHistory sealRead ∧ Cont enclosure located sealRow ∧
              Cont enclosure located sealRead ∧ hsame sealRead sealRow ∧
                PkgSig bundle cert pkg := by
  intro packet sealReadRoute sealReadSame
  obtain ⟨_streamUnary, _windowUnary, enclosureUnary, locatedUnary, sealRowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, sealRoute, _provenanceRoute,
    certSig⟩ := packet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary locatedUnary sealReadRoute
  exact
    ⟨enclosureUnary, locatedUnary, sealRowUnary, sealReadUnary, sealRoute, sealReadRoute,
      sealReadSame, certSig⟩

end BEDC.Derived.SignedDigitRealUp
