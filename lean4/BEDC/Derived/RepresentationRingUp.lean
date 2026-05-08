import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RepresentationRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RepresentationRingBHistRepresentationPacket [AskSetup] [PackageSetup]
    (group ring reps directSum tensor provenance classifier ledger endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory group ∧ UnaryHistory ring ∧ UnaryHistory reps ∧ UnaryHistory directSum ∧
    UnaryHistory tensor ∧ UnaryHistory provenance ∧ UnaryHistory classifier ∧
      Cont reps directSum tensor ∧ Cont group ring provenance ∧
        Cont provenance classifier ledger ∧ Cont ledger tensor endpoint ∧
          PkgSig bundle endpoint pkg

theorem RepresentationRingBHistRepresentationPacket_carrier_boundary [AskSetup] [PackageSetup]
    {group ring reps directSum tensor provenance classifier ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RepresentationRingBHistRepresentationPacket group ring reps directSum tensor provenance
        classifier ledger endpoint bundle pkg ->
      UnaryHistory group ∧ UnaryHistory ring ∧ UnaryHistory reps ∧ UnaryHistory directSum ∧
        UnaryHistory tensor ∧ UnaryHistory provenance ∧ UnaryHistory classifier ∧
          UnaryHistory ledger ∧ UnaryHistory endpoint ∧
            hsame ledger (append provenance classifier) ∧
              hsame endpoint (append ledger tensor) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have groupUnary : UnaryHistory group := packet.left
  have ringUnary : UnaryHistory ring := packet.right.left
  have repsUnary : UnaryHistory reps := packet.right.right.left
  have directSumUnary : UnaryHistory directSum := packet.right.right.right.left
  have tensorUnary : UnaryHistory tensor := packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have classifierUnary : UnaryHistory classifier :=
    packet.right.right.right.right.right.right.left
  have ledgerCont : Cont provenance classifier ledger :=
    packet.right.right.right.right.right.right.right.right.right.left
  have endpointCont : Cont ledger tensor endpoint :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed provenanceUnary classifierUnary ledgerCont
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed ledgerUnary tensorUnary endpointCont
  exact And.intro groupUnary
    (And.intro ringUnary
      (And.intro repsUnary
        (And.intro directSumUnary
          (And.intro tensorUnary
            (And.intro provenanceUnary
              (And.intro classifierUnary
                (And.intro ledgerUnary
                  (And.intro endpointUnary
                    (And.intro ledgerCont
                      (And.intro endpointCont
                        packet.right.right.right.right.right.right.right.right.right.right.right))))))))))

end BEDC.Derived.RepresentationRingUp
