import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BousfieldLocalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BousfieldLocalizationPacket [AskSetup] [PackageSetup]
    (model selected localObjects route provenance ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObjects ∧
    UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
      UnaryHistory endpoint ∧ Cont model selected route ∧
        Cont route localObjects endpoint ∧ PkgSig bundle endpoint pkg

theorem BousfieldLocalizationPacket_local_object_handoff [AskSetup] [PackageSetup]
    {model selected localObjects route provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BousfieldLocalizationPacket model selected localObjects route provenance ledger endpoint
        bundle pkg ->
      UnaryHistory model ∧ UnaryHistory selected ∧ UnaryHistory localObjects ∧
        UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ Cont model selected route ∧
            Cont route localObjects endpoint ∧ hsame route (append model selected) ∧
              hsame endpoint (append route localObjects) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have modelUnary : UnaryHistory model :=
    packet.left
  have selectedUnary : UnaryHistory selected :=
    packet.right.left
  have localObjectsUnary : UnaryHistory localObjects :=
    packet.right.right.left
  have routeUnary : UnaryHistory route :=
    packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    packet.right.right.right.right.right.right.left
  have routeRow : Cont model selected route :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont route localObjects endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  exact
    ⟨modelUnary,
      selectedUnary,
      localObjectsUnary,
      routeUnary,
      provenanceUnary,
      ledgerUnary,
      endpointUnary,
      routeRow,
      endpointRow,
      routeRow,
      endpointRow,
      pkgSig⟩

end BEDC.Derived.BousfieldLocalizationUp
