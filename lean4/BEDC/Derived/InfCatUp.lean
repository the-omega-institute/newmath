import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.InfCatUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def InfCatBHistSourcePacket [AskSetup] [PackageSetup]
    (simplicial category horn lift provenance transport : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory simplicial ∧ UnaryHistory category ∧ UnaryHistory horn ∧
    UnaryHistory lift ∧ UnaryHistory provenance ∧ Cont simplicial horn lift ∧
      Cont provenance lift transport ∧ PkgSig bundle transport pkg

theorem InfCatBHistSourcePacket_inner_horn_ledger_boundary [AskSetup] [PackageSetup]
    {simplicial category horn lift provenance transport : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    InfCatBHistSourcePacket simplicial category horn lift provenance transport bundle pkg ->
      UnaryHistory simplicial ∧ UnaryHistory horn ∧ UnaryHistory lift ∧
        UnaryHistory provenance ∧ UnaryHistory transport ∧ Cont simplicial horn lift ∧
          Cont provenance lift transport ∧ hsame lift (append simplicial horn) ∧
            hsame transport (append provenance lift) ∧ PkgSig bundle transport pkg := by
  intro packet
  have simplicialUnary : UnaryHistory simplicial := packet.left
  have hornUnary : UnaryHistory horn := packet.right.right.left
  have liftUnary : UnaryHistory lift := packet.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.left
  have simplicialHornLift : Cont simplicial horn lift :=
    packet.right.right.right.right.right.left
  have provenanceLiftTransport : Cont provenance lift transport :=
    packet.right.right.right.right.right.right.left
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed provenanceUnary liftUnary provenanceLiftTransport
  exact And.intro simplicialUnary
    (And.intro hornUnary
      (And.intro liftUnary
        (And.intro provenanceUnary
          (And.intro transportUnary
            (And.intro simplicialHornLift
              (And.intro provenanceLiftTransport
                (And.intro simplicialHornLift
                  (And.intro provenanceLiftTransport
                    packet.right.right.right.right.right.right.right))))))))

end BEDC.Derived.InfCatUp
