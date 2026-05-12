import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyNamePacket [AskSetup] [PackageSetup]
    (schedule observation radius ledger «seal» provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory observation ∧ UnaryHistory radius ∧
    UnaryHistory ledger ∧ UnaryHistory «seal» ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
      PkgSig bundle provenance pkg

theorem RegularCauchyNamePacket_streamname_handoff [AskSetup] [PackageSetup]
    {schedule observation radius ledger «seal» provenance name window point handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNamePacket schedule observation radius ledger «seal» provenance name bundle pkg ->
      Cont schedule observation window -> Cont window radius point -> Cont point «seal» handoff ->
        PkgSig bundle handoff pkg ->
          UnaryHistory schedule /\ UnaryHistory observation /\ UnaryHistory radius /\
            UnaryHistory window /\ UnaryHistory point /\ UnaryHistory handoff /\
              Cont schedule observation window /\ Cont window radius point /\
                Cont point «seal» handoff /\ PkgSig bundle provenance pkg /\
                  PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist
  intro packet windowCont pointCont handoffCont handoffPkg
  have scheduleUnary : UnaryHistory schedule := packet.left
  have observationUnary : UnaryHistory observation := packet.right.left
  have radiusUnary : UnaryHistory radius := packet.right.right.left
  have sealUnary : UnaryHistory «seal» := packet.right.right.right.right.left
  have provenancePkg : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right
  have windowUnary : UnaryHistory window :=
    unary_cont_closed scheduleUnary observationUnary windowCont
  have pointUnary : UnaryHistory point :=
    unary_cont_closed windowUnary radiusUnary pointCont
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed pointUnary sealUnary handoffCont
  constructor
  · exact scheduleUnary
  · constructor
    · exact observationUnary
    · constructor
      · exact radiusUnary
      · constructor
        · exact windowUnary
        · constructor
          · exact pointUnary
          · constructor
            · exact handoffUnary
            · constructor
              · exact windowCont
              · constructor
                · exact pointCont
                · constructor
                  · exact handoffCont
                  · constructor
                    · exact provenancePkg
                    · exact handoffPkg

end BEDC.Derived.RegularCauchyNameUp
