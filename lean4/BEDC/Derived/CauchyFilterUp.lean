import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream directed modulus endpoint regseq transport provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ Cont stream directed modulus ∧ Cont modulus endpoint regseq ∧
        Cont regseq transport provenance ∧ PkgSig bundle provenance pkg

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream directed modulus endpoint regseq transport consumer provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont stream directed modulus ∧ Cont modulus endpoint regseq ∧
          Cont regseq transport provenance ∧ Cont endpoint regseq transport ∧
            Cont transport consumer provenance ∧ Cont provenance cert consumer ∧
              PkgSig bundle provenance pkg

theorem CauchyFilterPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream directed modulus endpoint regseq transport consumer provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream directed modulus endpoint regseq transport consumer provenance cert
        bundle pkg ->
      CauchyFilterRegSeqRatWindow stream directed modulus endpoint regseq transport provenance
          bundle pkg ∧
        Cont endpoint regseq transport ∧ Cont transport consumer provenance ∧
          PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨streamUnary, directedUnary, modulusUnary, endpointUnary, regseqUnary,
    transportUnary, _consumerUnary, provenanceUnary, _certUnary, streamDirectedRow,
    modulusEndpointRow, regseqTransportRow, endpointRegseqRow, transportConsumerRow,
    _certConsumerRow, pkgRow⟩ := packet
  exact
    ⟨⟨streamUnary, directedUnary, modulusUnary, endpointUnary, regseqUnary, transportUnary,
        provenanceUnary, streamDirectedRow, modulusEndpointRow, regseqTransportRow, pkgRow⟩,
      endpointRegseqRow, transportConsumerRow, pkgRow⟩

end BEDC.Derived.CauchyFilterUp
