import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.QuantumStateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def QuantumStateBHistCarrier [AskSetup] [PackageSetup]
    (hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory hilbert ∧ UnaryHistory projective ∧ UnaryHistory vector ∧ UnaryHistory norm ∧
    UnaryHistory phase ∧ UnaryHistory projectiveEndpoint ∧ UnaryHistory provenance ∧
      Cont hilbert vector hilbertLedger ∧ Cont projective projectiveEndpoint projectiveLedger ∧
        Cont vector norm phase ∧ Cont provenance (append hilbertLedger projectiveLedger) endpoint ∧
          PkgSig bundle endpoint pkg

theorem QuantumStateBHistCarrier_hilbert_source_boundary [AskSetup] [PackageSetup]
    {hilbert projective vector norm phase projectiveEndpoint hilbertLedger projectiveLedger
      provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuantumStateBHistCarrier hilbert projective vector norm phase projectiveEndpoint
        hilbertLedger projectiveLedger provenance endpoint bundle pkg ->
      UnaryHistory vector ∧ UnaryHistory norm ∧ UnaryHistory hilbertLedger ∧
        Cont hilbert vector hilbertLedger ∧ Cont vector norm phase ∧
          hsame endpoint (append provenance (append hilbertLedger projectiveLedger)) ∧
            PkgSig bundle endpoint pkg := by
  intro carrier
  have vectorUnary : UnaryHistory vector :=
    carrier.right.right.left
  have normUnary : UnaryHistory norm :=
    carrier.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.right.right.left
  have hilbertLedgerRow : Cont hilbert vector hilbertLedger :=
    carrier.right.right.right.right.right.right.right.left
  have projectiveLedgerRow : Cont projective projectiveEndpoint projectiveLedger :=
    carrier.right.right.right.right.right.right.right.right.left
  have phaseRow : Cont vector norm phase :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have endpointRow : Cont provenance (append hilbertLedger projectiveLedger) endpoint :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have hilbertLedgerUnary : UnaryHistory hilbertLedger :=
    unary_cont_closed carrier.left vectorUnary hilbertLedgerRow
  have projectiveLedgerUnary : UnaryHistory projectiveLedger :=
    unary_cont_closed carrier.right.left carrier.right.right.right.right.right.left
      projectiveLedgerRow
  have combinedLedgerUnary : UnaryHistory (append hilbertLedger projectiveLedger) :=
    unary_append_closed hilbertLedgerUnary projectiveLedgerUnary
  have _endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary combinedLedgerUnary endpointRow
  exact And.intro vectorUnary
    (And.intro normUnary
      (And.intro hilbertLedgerUnary
        (And.intro hilbertLedgerRow
          (And.intro phaseRow
            (And.intro endpointRow pkgSig)))))

end BEDC.Derived.QuantumStateUp
