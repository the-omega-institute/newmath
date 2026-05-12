import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

def RegularCauchyNameCarrier [AskSetup] [PackageSetup]
    (schedule observation radius ledger sealRow provenance namecert endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory schedule ∧ UnaryHistory observation ∧ UnaryHistory radius ∧
    UnaryHistory ledger ∧ UnaryHistory sealRow ∧ UnaryHistory namecert ∧
      Cont schedule observation radius ∧ Cont radius ledger sealRow ∧
        Cont sealRow provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem RegularCauchyNameCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {schedule observation radius ledger sealRow provenance namecert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance namecert
        endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance
            namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance
            namecert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          RegularCauchyNameCarrier schedule observation radius ledger sealRow provenance
            namecert endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.RegularCauchyNameUp
