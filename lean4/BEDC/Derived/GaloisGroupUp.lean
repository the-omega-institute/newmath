import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GaloisGroupAutomorphismActionPacket [AskSetup] [PackageSetup]
    (galoisExt group fixedBase action composition inverse classifier provenance ledger
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory galoisExt ∧ UnaryHistory group ∧ UnaryHistory fixedBase ∧
    UnaryHistory action ∧ UnaryHistory composition ∧ UnaryHistory inverse ∧
      Cont galoisExt group provenance ∧ Cont fixedBase action classifier ∧
        Cont composition inverse ledger ∧ Cont provenance ledger endpoint ∧
          PkgSig bundle endpoint pkg

theorem GaloisGroupAutomorphismActionPacket_fixed_base_carrier_obligation
    [AskSetup] [PackageSetup]
    {galoisExt group fixedBase action composition inverse classifier provenance ledger
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galoisExt group fixedBase action composition inverse
        classifier provenance ledger endpoint bundle pkg ->
      UnaryHistory provenance ∧ UnaryHistory classifier ∧ UnaryHistory ledger ∧
        UnaryHistory endpoint ∧ hsame provenance (append galoisExt group) ∧
          hsame classifier (append fixedBase action) ∧
            hsame ledger (append composition inverse) ∧
              hsame endpoint (append provenance ledger) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed packet.left packet.right.left
      packet.right.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed packet.right.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed packet.right.right.right.right.left
      packet.right.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed provenanceUnary ledgerUnary
      packet.right.right.right.right.right.right.right.right.right.left
  exact And.intro provenanceUnary
    (And.intro classifierUnary
      (And.intro ledgerUnary
        (And.intro endpointUnary
          (And.intro packet.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.left
              (And.intro packet.right.right.right.right.right.right.right.right.left
                (And.intro packet.right.right.right.right.right.right.right.right.right.left
                  packet.right.right.right.right.right.right.right.right.right.right)))))))

end BEDC.Derived.GaloisGroupUp
