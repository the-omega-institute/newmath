import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SignedDigitRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem SignedDigitRealPacket_common_window_seal_determinacy [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert normalized stream'
      window' enclosure' located' sealRow' transport' route' provenance' cert' normalized'
      sealRead sealRead' : BHist}
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
                      Cont enclosure located sealRead ->
                        Cont enclosure' located' sealRead' ->
                          hsame sealRead sealRow ->
                            hsame sealRead' sealRow' ->
                              hsame normalized normalized' ∧ hsame enclosure enclosure' ∧
                                hsame sealRow sealRow' ∧ hsame sealRead sealRead' ∧
                                  PkgSig bundle cert pkg ∧ PkgSig bundle' cert' pkg' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro packet packet' normalizationRow normalizationRow' sameStream sameWindow
    sameNormalizedEnclosure sameNormalizedEnclosure' sameLocated sealReadRow sealReadRow'
    sameSealRead sameSealRead'
  have windowStable :=
    SignedDigitRealPacket_window_classifier_stability packet packet' normalizationRow
      normalizationRow' sameStream sameWindow sameNormalizedEnclosure sameNormalizedEnclosure'
      sameLocated
  have sameSealReadRows : hsame sealRead sealRead' :=
    cont_respects_hsame windowStable.right.left sameLocated sealReadRow sealReadRow'
  exact
    ⟨windowStable.left,
      windowStable.right.left,
      windowStable.right.right.left,
      sameSealReadRows,
      windowStable.right.right.right.right.right.left,
      windowStable.right.right.right.right.right.right⟩

theorem SignedDigitRealPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          SignedDigitRealPacket stream window enclosure located sealRow transport route provenance
            cert bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          SignedDigitRealPacket stream window enclosure located sealRow transport route provenance
            cert bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          SignedDigitRealPacket stream window enclosure located sealRow transport route provenance
            cert bundle pkg ∧ hsame row provenance)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited := Exists.intro provenance (And.intro packet (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem SignedDigitRealPacket_obligation_transport_package [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert streamT windowT
      enclosureT locatedT sealRowT : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      hsame stream streamT ->
        hsame window windowT ->
          hsame enclosure enclosureT ->
            hsame located locatedT ->
              hsame sealRow sealRowT ->
                Cont enclosureT locatedT sealRowT ->
                  UnaryHistory streamT ∧ UnaryHistory windowT ∧ UnaryHistory enclosureT ∧
                    UnaryHistory locatedT ∧ UnaryHistory sealRowT ∧
                      Cont enclosureT locatedT sealRowT ∧ hsame sealRow sealRowT ∧
                        PkgSig bundle cert pkg := by
  intro packet sameStream sameWindow sameEnclosure sameLocated sameSeal transportSeal
  obtain ⟨streamUnary, windowUnary, enclosureUnary, locatedUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, _sealRoute,
    _provenanceRoute, certSig⟩ := packet
  have streamTUnary : UnaryHistory streamT :=
    unary_transport streamUnary sameStream
  have windowTUnary : UnaryHistory windowT :=
    unary_transport windowUnary sameWindow
  have enclosureTUnary : UnaryHistory enclosureT :=
    unary_transport enclosureUnary sameEnclosure
  have locatedTUnary : UnaryHistory locatedT :=
    unary_transport locatedUnary sameLocated
  have sealRowTUnary : UnaryHistory sealRowT :=
    unary_transport sealUnary sameSeal
  exact
    ⟨streamTUnary, windowTUnary, enclosureTUnary, locatedTUnary, sealRowTUnary,
      transportSeal, sameSeal, certSig⟩

theorem SignedDigitRealPacket_exact_readback_boundary [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert normalized sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      Cont stream window normalized ->
        hsame normalized enclosure ->
          Cont enclosure located sealRead ->
            hsame sealRead sealRow ->
              UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory normalized ∧
                UnaryHistory enclosure ∧ UnaryHistory located ∧ UnaryHistory sealRow ∧
                  UnaryHistory sealRead ∧ Cont stream window normalized ∧
                    Cont enclosure located sealRead ∧ hsame normalized enclosure ∧
                      hsame sealRead sealRow ∧ PkgSig bundle cert pkg := by
  intro packet normalizationRoute normalizedSame sealReadRoute sealReadSame
  obtain ⟨streamUnary, windowUnary, enclosureUnary, locatedUnary, sealRowUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, _sealRoute,
    _provenanceRoute, certSig⟩ := packet
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed streamUnary windowUnary normalizationRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary locatedUnary sealReadRoute
  exact
    ⟨streamUnary, windowUnary, normalizedUnary, enclosureUnary, locatedUnary, sealRowUnary,
      sealReadUnary, normalizationRoute, sealReadRoute, normalizedSame, sealReadSame, certSig⟩

theorem SignedDigitRealPacket_tail_window_export [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert normalized sealRead
      realExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      Cont stream window normalized ->
        hsame normalized enclosure ->
          Cont enclosure located sealRead ->
            hsame sealRead sealRow ->
              Cont sealRead provenance realExport ->
                PkgSig bundle realExport pkg ->
                  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory normalized ∧
                    UnaryHistory enclosure ∧ UnaryHistory located ∧ UnaryHistory sealRow ∧
                      UnaryHistory sealRead ∧ UnaryHistory realExport ∧
                        Cont stream window normalized ∧ Cont enclosure located sealRead ∧
                          Cont sealRead provenance realExport ∧ hsame normalized enclosure ∧
                            hsame sealRead sealRow ∧ PkgSig bundle cert pkg ∧
                              PkgSig bundle realExport pkg := by
  intro packet normalizationRoute normalizedSame sealReadRoute sealReadSame exportRoute exportSig
  obtain ⟨streamUnary, windowUnary, enclosureUnary, locatedUnary, sealRowUnary,
    _transportUnary, _routeUnary, provenanceUnary, _certUnary, _sealRoute,
    _provenanceRoute, certSig⟩ := packet
  have normalizedUnary : UnaryHistory normalized :=
    unary_cont_closed streamUnary windowUnary normalizationRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed enclosureUnary locatedUnary sealReadRoute
  have realExportUnary : UnaryHistory realExport :=
    unary_cont_closed sealReadUnary provenanceUnary exportRoute
  exact
    ⟨streamUnary, windowUnary, normalizedUnary, enclosureUnary, locatedUnary, sealRowUnary,
      sealReadUnary, realExportUnary, normalizationRoute, sealReadRoute, exportRoute,
      normalizedSame, sealReadSame, certSig, exportSig⟩

theorem SignedDigitRealPacket_obligation_closure_package [AskSetup] [PackageSetup]
    {stream window enclosure located sealRow transport route provenance cert normalized sealRead
      realExport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SignedDigitRealPacket stream window enclosure located sealRow transport route provenance cert
        bundle pkg ->
      Cont stream window normalized ->
        hsame normalized enclosure ->
          Cont enclosure located sealRead ->
            hsame sealRead sealRow ->
              Cont sealRead provenance realExport ->
                PkgSig bundle realExport pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row realExport ∧ UnaryHistory row)
                    (fun row : BHist => hsame row sealRead ∨ hsame row realExport)
                    (fun row : BHist => hsame row realExport ∧ PkgSig bundle realExport pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro packet normalizationRoute normalizedSame sealReadRoute sealReadSame exportRoute exportSig
  obtain ⟨_streamUnary, _windowUnary, _normalizedUnary, _enclosureUnary, _locatedUnary,
    _sealRowUnary, _sealReadUnary, realExportUnary, _normalizationRoute, _sealReadRoute,
    _exportRoute, _normalizedSame, _sealReadSame, _certSig, realExportSig⟩ :=
    SignedDigitRealPacket_tail_window_export packet normalizationRoute normalizedSame sealReadRoute
      sealReadSame exportRoute exportSig
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realExport (And.intro (hsame_refl realExport) realExportUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left realExportSig
  }

end BEDC.Derived.SignedDigitRealUp
