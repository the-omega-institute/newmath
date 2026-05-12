import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ArchimedeanRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ArchimedeanRealPacket [AskSetup] [PackageSetup]
    (real bound dyadic stream regseq ledger transport continuation provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory real ∧ UnaryHistory bound ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
    UnaryHistory regseq ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
      UnaryHistory continuation ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
        Cont stream regseq ledger ∧ Cont ledger transport continuation ∧
          Cont continuation provenance real ∧ PkgSig bundle bound pkg ∧
            PkgSig bundle provenance pkg

theorem ArchimedeanRealPacket_rational_bound_witness [AskSetup] [PackageSetup]
    {real bound dyadic stream regseq ledger transport continuation provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealPacket real bound dyadic stream regseq ledger transport continuation
      provenance nameCert bundle pkg ->
      ∃ boundWitness dyadicWitness : BHist,
        hsame boundWitness bound ∧ hsame dyadicWitness dyadic ∧ UnaryHistory boundWitness ∧
          UnaryHistory dyadicWitness ∧ Cont stream regseq ledger ∧
            PkgSig bundle boundWitness pkg := by
  intro packet
  obtain ⟨_realUnary, boundUnary, dyadicUnary, _streamUnary, _regseqUnary, _ledgerUnary,
    _transportUnary, _continuationUnary, _provenanceUnary, _nameCertUnary, streamRegseqLedger,
    _ledgerTransportContinuation, _continuationProvenanceReal, boundPkg,
    _provenancePkg⟩ := packet
  exact
    ⟨bound, dyadic, hsame_refl bound, hsame_refl dyadic, boundUnary, dyadicUnary,
      streamRegseqLedger, boundPkg⟩

def ArchimedeanRealCarrier [AskSetup] [PackageSetup]
    (realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
    UnaryHistory streamWindow ∧ UnaryHistory regseqHandoff ∧ UnaryHistory boundLedger ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory localCert ∧ Cont realName streamWindow regseqHandoff ∧
          Cont ratBound dyadicBound boundLedger ∧ Cont regseqHandoff boundLedger transport ∧
            Cont transport routes provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localCert pkg

theorem ArchimedeanRealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {realName ratBound dyadicBound streamWindow regseqHandoff boundLedger transport routes
      provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
        boundLedger transport routes provenance localCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow
              regseqHandoff boundLedger transport routes provenance localCert bundle pkg)
        (fun _row : BHist =>
          UnaryHistory realName ∧ UnaryHistory ratBound ∧ UnaryHistory dyadicBound ∧
            Cont realName streamWindow regseqHandoff ∧ Cont ratBound dyadicBound boundLedger)
        (fun row : BHist => PkgSig bundle provenance pkg ∧ UnaryHistory row)
        hsame := by
  intro carrier
  have carrierWitness := carrier
  obtain ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, _streamWindowUnary,
    _regseqHandoffUnary, _boundLedgerUnary, _transportUnary, _routesUnary, _provenanceUnary,
    _localCertUnary, realNameStreamWindowRegseq, ratDyadicBoundLedger,
    _regseqLedgerTransport, _transportRoutesProvenance, provenancePkg, _localCertPkg⟩ :=
    carrier
  have sourceRealName :
      (fun row : BHist =>
        hsame row realName ∧
          ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
            boundLedger transport routes provenance localCert bundle pkg) realName := by
    exact And.intro (hsame_refl realName) carrierWitness
  have core :
      NameCert
        (fun row : BHist =>
          hsame row realName ∧
            ArchimedeanRealCarrier realName ratBound dyadicBound streamWindow regseqHandoff
              boundLedger transport routes provenance localCert bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro realName sourceRealName
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK sourceH
        have sameHRealName : hsame h realName := sourceH.left
        have sameKRealName : hsame k realName :=
          hsame_trans (hsame_symm sameHK) sameHRealName
        exact And.intro sameKRealName sourceH.right
    }
  exact {
    core := core
    pattern_sound := by
      intro _row _source
      exact
        ⟨realNameUnary, ratBoundUnary, dyadicBoundUnary, realNameStreamWindowRegseq,
          ratDyadicBoundLedger⟩
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport realNameUnary (hsame_symm source.left)
      exact And.intro provenancePkg rowUnary
  }

end BEDC.Derived.ArchimedeanRealUp
