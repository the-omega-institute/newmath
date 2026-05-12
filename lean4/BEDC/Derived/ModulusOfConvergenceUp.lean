import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModulusOfConvergenceNameCertPacket [AskSetup] [PackageSetup]
    (precision threshold requestWindow modulus schedule witnessWindow witness exportWindow ledger
      provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      Cont precision threshold requestWindow ∧ Cont modulus schedule witnessWindow ∧
        Cont requestWindow witness exportWindow ∧ Cont exportWindow ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {precision threshold requestWindow modulus schedule witnessWindow witness exportWindow ledger
      provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceNameCertPacket precision threshold requestWindow modulus schedule witnessWindow
        witness exportWindow ledger provenance bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame ∧
        Cont precision threshold requestWindow ∧ Cont modulus schedule witnessWindow ∧
          Cont requestWindow witness exportWindow ∧ Cont exportWindow ledger provenance ∧
            PkgSig bundle provenance pkg := by
  intro packet
  have requestRow : Cont precision threshold requestWindow :=
    packet.right.right.right.right.right.right.left
  have witnessRow : Cont modulus schedule witnessWindow :=
    packet.right.right.right.right.right.right.right.left
  have exportRow : Cont requestWindow witness exportWindow :=
    packet.right.right.right.right.right.right.right.right.left
  have provenanceRow : Cont exportWindow ledger provenance :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  have cert :
      SemanticNameCert (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance)
          (fun row : BHist => hsame row provenance) hsame := {
    core := {
      carrier_inhabited := Exists.intro provenance (hsame_refl provenance)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro requestRow
      (And.intro witnessRow
        (And.intro exportRow
          (And.intro provenanceRow pkgSig))))

def ModulusOfConvergenceCarrier [AskSetup] [PackageSetup]
    (precision selector modulus schedule witness ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory selector ∧ UnaryHistory modulus ∧
    UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ Cont precision selector modulus ∧
        Cont modulus schedule witness ∧ Cont witness ledger provenance ∧
          PkgSig bundle provenance pkg

theorem ModulusOfConvergencePacket_tail_restriction_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance schedule' witness'
      provenance' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      hsame schedule schedule' ->
        hsame witness witness' ->
          hsame provenance provenance' ->
            Cont modulus schedule' witness' ->
              Cont witness' ledger provenance' ->
                PkgSig bundle provenance' pkg ->
                  ModulusOfConvergenceCarrier precision selector modulus schedule' witness'
                      ledger provenance' bundle pkg ∧
                    hsame witness witness' ∧ hsame provenance provenance' := by
  intro packet sameSchedule sameWitness sameProvenance restrictedWitness restrictedProvenance
    restrictedPkg
  have precisionUnary : UnaryHistory precision :=
    packet.left
  have selectorUnary : UnaryHistory selector :=
    packet.right.left
  have modulusUnary : UnaryHistory modulus :=
    packet.right.right.left
  have scheduleUnary : UnaryHistory schedule' :=
    unary_transport packet.right.right.right.left sameSchedule
  have witnessUnary : UnaryHistory witness' :=
    unary_transport packet.right.right.right.right.left sameWitness
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.right.left sameProvenance
  have modulusRoute : Cont precision selector modulus :=
    packet.right.right.right.right.right.right.right.left
  constructor
  · exact
      And.intro precisionUnary
        (And.intro selectorUnary
          (And.intro modulusUnary
            (And.intro scheduleUnary
              (And.intro witnessUnary
                (And.intro ledgerUnary
                  (And.intro provenanceUnary
                    (And.intro modulusRoute
                      (And.intro restrictedWitness
                        (And.intro restrictedProvenance restrictedPkg)))))))))
  · exact And.intro sameWitness sameProvenance

theorem ModulusOfConvergenceCarrier_composition_stability [AskSetup] [PackageSetup]
    {precision selector modulus schedule witness ledger provenance precision' selector' modulus'
      schedule' witness' ledger' provenance' : BHist}
    {bundle bundle' : ProbeBundle ProbeName} {pkg pkg' : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      ModulusOfConvergenceCarrier precision' selector' modulus' schedule' witness' ledger'
        provenance' bundle' pkg' ->
        exists joined : BHist, Cont provenance precision' joined ∧ UnaryHistory joined := by
  intro leftCarrier rightCarrier
  cases leftCarrier with
  | intro _precisionUnary leftRest =>
      cases leftRest with
      | intro _selectorUnary leftRest =>
          cases leftRest with
          | intro _modulusUnary leftRest =>
              cases leftRest with
              | intro _scheduleUnary leftRest =>
                  cases leftRest with
                  | intro _witnessUnary leftRest =>
                      cases leftRest with
                      | intro _ledgerUnary leftRest =>
                          cases leftRest with
                          | intro provenanceUnary _leftRows =>
                              cases rightCarrier with
                              | intro precisionUnary' _rightRest =>
                                  let joined := append provenance precision'
                                  have joinedRow : Cont provenance precision' joined := by
                                    rfl
                                  have joinedUnary : UnaryHistory joined :=
                                    unary_repetition_closed_under_continuation provenanceUnary
                                      precisionUnary' joinedRow
                                  exact ⟨joined, joinedRow, joinedUnary⟩

def ModulusOfConvergencePacket
    (precision threshold modulus schedule late ledger provenance : BHist) : Prop :=
  UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory schedule ∧
    UnaryHistory late ∧ Cont precision threshold modulus ∧ Cont schedule late ledger ∧
      Cont modulus ledger provenance

theorem ModulusOfConvergencePacket_ledger_exactness
    {precision threshold modulus schedule late ledger provenance : BHist} :
    ModulusOfConvergencePacket precision threshold modulus schedule late ledger provenance ->
      UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory schedule ∧
        UnaryHistory late ∧ UnaryHistory modulus ∧ UnaryHistory ledger ∧
          UnaryHistory provenance ∧ hsame modulus (append precision threshold) ∧
            hsame ledger (append schedule late) ∧
              hsame provenance (append modulus ledger) := by
  intro packet
  have precisionUnary : UnaryHistory precision := packet.left
  have thresholdUnary : UnaryHistory threshold := packet.right.left
  have scheduleUnary : UnaryHistory schedule := packet.right.right.left
  have lateUnary : UnaryHistory late := packet.right.right.right.left
  have modulusCont : Cont precision threshold modulus := packet.right.right.right.right.left
  have ledgerCont : Cont schedule late ledger := packet.right.right.right.right.right.left
  have provenanceCont : Cont modulus ledger provenance := packet.right.right.right.right.right.right
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed precisionUnary thresholdUnary modulusCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary lateUnary ledgerCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed modulusUnary ledgerUnary provenanceCont
  constructor
  · exact precisionUnary
  constructor
  · exact thresholdUnary
  constructor
  · exact scheduleUnary
  constructor
  · exact lateUnary
  constructor
  · exact modulusUnary
  constructor
  · exact ledgerUnary
  constructor
  · exact provenanceUnary
  constructor
  · exact modulusCont
  constructor
  · exact ledgerCont
  · exact provenanceCont

end BEDC.Derived.ModulusOfConvergenceUp
