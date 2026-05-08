import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KnotUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KnotDiagramPacket [AskSetup] [PackageSetup]
    (sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sone ∧ UnaryHistory ambient ∧ UnaryHistory diagram ∧ UnaryHistory trace ∧
    UnaryHistory homotopy ∧ UnaryHistory endpoint0 ∧ UnaryHistory endpoint1 ∧
      Cont sone ambient provenance ∧ Cont endpoint0 endpoint1 ledger ∧
        Cont provenance ledger endpoint ∧ PkgSig bundle endpoint pkg

theorem KnotDiagramPacket_sone_source_boundary [AskSetup] [PackageSetup]
    {sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KnotDiagramPacket sone ambient diagram trace homotopy endpoint0 endpoint1 provenance ledger
        endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory ledger ∧ UnaryHistory endpoint ∧
        hsame provenance (append sone ambient) ∧ hsame ledger (append endpoint0 endpoint1) ∧
          hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have soneUnary : UnaryHistory sone :=
    packet.left
  have ambientUnary : UnaryHistory ambient :=
    packet.right.left
  have endpoint0Unary : UnaryHistory endpoint0 :=
    packet.right.right.right.right.right.left
  have endpoint1Unary : UnaryHistory endpoint1 :=
    packet.right.right.right.right.right.right.left
  have provenanceCont : Cont sone ambient provenance :=
    packet.right.right.right.right.right.right.right.left
  have ledgerCont : Cont endpoint0 endpoint1 ledger :=
    packet.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont provenance ledger endpoint :=
    packet.right.right.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed soneUnary ambientUnary provenanceCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed endpoint0Unary endpoint1Unary ledgerCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary endpointCont
  exact And.intro provenanceUnary
    (And.intro ledgerUnary
      (And.intro endpointUnary
        (And.intro provenanceCont
          (And.intro ledgerCont
            (And.intro endpointCont
              packet.right.right.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.KnotUp
