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

end BEDC.Derived.ArchimedeanRealUp
