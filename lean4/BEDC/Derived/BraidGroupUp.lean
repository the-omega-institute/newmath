import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.BraidGroupUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

def BraidGroupPacket [AskSetup] [PackageSetup]
    (strand word ledger classifier provenance action closureRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  PositiveUnaryDenominator strand ∧ UnaryHistory word ∧ UnaryHistory ledger ∧
    UnaryHistory provenance ∧ Cont word ledger classifier ∧
      Cont classifier provenance action ∧ Cont action strand closureRow ∧
        PkgSig bundle closureRow pkg

theorem BraidGroupPacket_artin_ledger_stability [AskSetup] [PackageSetup]
    {strand word ledger classifier provenance action closureRow word' ledger' classifier'
      provenance' action' closureRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupPacket strand word ledger classifier provenance action closureRow bundle pkg ->
      hsame word word' ->
        hsame ledger ledger' ->
          hsame provenance provenance' ->
            Cont word' ledger' classifier' ->
              Cont classifier' provenance' action' ->
                Cont action' strand closureRow' ->
                  PkgSig bundle closureRow' pkg ->
                    BraidGroupPacket strand word' ledger' classifier' provenance' action'
                        closureRow' bundle pkg ∧
                      hsame classifier classifier' ∧ hsame action action' ∧
                        hsame closureRow closureRow' := by
  intro packet wordSame ledgerSame provenanceSame classifierRow' actionRow' closureRowCont'
    closurePkg'
  have strandUnary : UnaryHistory strand :=
    (PositiveUnaryDenominator_unary_and_nonempty packet.left).left
  have wordUnary' : UnaryHistory word' :=
    unary_transport packet.right.left wordSame
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_transport packet.right.right.left ledgerSame
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.left provenanceSame
  have classifierUnary' : UnaryHistory classifier' :=
    unary_cont_closed wordUnary' ledgerUnary' classifierRow'
  have actionUnary' : UnaryHistory action' :=
    unary_cont_closed classifierUnary' provenanceUnary' actionRow'
  have closureUnary' : UnaryHistory closureRow' :=
    unary_cont_closed actionUnary' strandUnary closureRowCont'
  have classifierSame : hsame classifier classifier' :=
    cont_respects_hsame wordSame ledgerSame packet.right.right.right.right.left classifierRow'
  have actionSame : hsame action action' :=
    cont_respects_hsame classifierSame provenanceSame packet.right.right.right.right.right.left
      actionRow'
  have closureSame : hsame closureRow closureRow' :=
    cont_respects_hsame actionSame (hsame_refl strand)
      packet.right.right.right.right.right.right.left closureRowCont'
  have transportedStrand : PositiveUnaryDenominator strand :=
    PositiveUnaryDenominator_hsame_transport (hsame_refl strand) packet.left
  exact And.intro
    (And.intro transportedStrand
      (And.intro wordUnary'
        (And.intro ledgerUnary'
          (And.intro provenanceUnary'
            (And.intro classifierRow'
              (And.intro actionRow'
                (And.intro closureRowCont' closurePkg')))))))
    (And.intro classifierSame (And.intro actionSame closureSame))

theorem BraidGroupPacket_weyl_root_action_handoff [AskSetup] [PackageSetup]
    {strand word ledger classifier provenance action closureRow rootAction shadow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupPacket strand word ledger classifier provenance action closureRow bundle pkg ->
      Cont action provenance rootAction -> Cont rootAction word shadow -> PkgSig bundle shadow pkg ->
        UnaryHistory word ∧ UnaryHistory ledger ∧ UnaryHistory action ∧ UnaryHistory rootAction ∧
          UnaryHistory shadow ∧ Cont word ledger classifier ∧ Cont classifier provenance action ∧
            Cont action provenance rootAction ∧ Cont rootAction word shadow ∧
              PkgSig bundle closureRow pkg ∧ PkgSig bundle shadow pkg := by
  intro packet rootActionRow shadowRow shadowPkg
  have wordUnary : UnaryHistory word :=
    packet.right.left
  have ledgerUnary : UnaryHistory ledger :=
    packet.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    packet.right.right.right.left
  have classifierRow : Cont word ledger classifier :=
    packet.right.right.right.right.left
  have actionRow : Cont classifier provenance action :=
    packet.right.right.right.right.right.left
  have actionUnary : UnaryHistory action :=
    unary_cont_closed (unary_cont_closed wordUnary ledgerUnary classifierRow) provenanceUnary actionRow
  have rootActionUnary : UnaryHistory rootAction :=
    unary_cont_closed actionUnary provenanceUnary rootActionRow
  have shadowUnary : UnaryHistory shadow :=
    unary_cont_closed rootActionUnary wordUnary shadowRow
  exact
    And.intro wordUnary
      (And.intro ledgerUnary
        (And.intro actionUnary
          (And.intro rootActionUnary
            (And.intro shadowUnary
              (And.intro classifierRow
                (And.intro actionRow
                  (And.intro rootActionRow
                    (And.intro shadowRow
                      (And.intro packet.right.right.right.right.right.right.right shadowPkg)))))))))

def BraidGroupArtinPacket [AskSetup] [PackageSetup]
    (strand word moveLedger classifier dependency endpoint : BHist) (bundle : ProbeBundle ProbeName)
    (pkg : Pkg) : Prop :=
  PositiveUnaryDenominator strand ∧ UnaryHistory word ∧ UnaryHistory moveLedger ∧
    UnaryHistory dependency ∧ Cont strand word moveLedger ∧
      Cont moveLedger dependency classifier ∧ Cont classifier word endpoint ∧
        PkgSig bundle endpoint pkg

theorem BraidGroupArtinPacket_ledger_stability [AskSetup] [PackageSetup]
    {strand word moveLedger classifier dependency endpoint strand' word' moveLedger' classifier'
      dependency' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word moveLedger classifier dependency endpoint bundle pkg ->
      hsame strand strand' ->
        hsame word word' ->
          hsame dependency dependency' ->
            Cont strand' word' moveLedger' ->
              Cont moveLedger' dependency' classifier' ->
                Cont classifier' word' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    BraidGroupArtinPacket strand' word' moveLedger' classifier' dependency'
                        endpoint' bundle pkg ∧
                      hsame moveLedger moveLedger' ∧ hsame classifier classifier' ∧
                        hsame endpoint endpoint' := by
  intro packet sameStrand sameWord sameDependency moveLedgerCont' classifierCont' endpointCont'
    endpointPkg'
  have strandPositive' : PositiveUnaryDenominator strand' :=
    PositiveUnaryDenominator_hsame_transport sameStrand packet.left
  have wordUnary' : UnaryHistory word' :=
    unary_transport packet.right.left sameWord
  have sameMoveLedger : hsame moveLedger moveLedger' :=
    cont_respects_hsame sameStrand sameWord packet.right.right.right.right.left
      moveLedgerCont'
  have moveLedgerUnary' : UnaryHistory moveLedger' :=
    unary_transport packet.right.right.left sameMoveLedger
  have dependencyUnary' : UnaryHistory dependency' :=
    unary_transport packet.right.right.right.left sameDependency
  have sameClassifier : hsame classifier classifier' :=
    cont_respects_hsame sameMoveLedger sameDependency packet.right.right.right.right.right.left
      classifierCont'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameClassifier sameWord packet.right.right.right.right.right.right.left
      endpointCont'
  exact
    And.intro
      (And.intro strandPositive'
        (And.intro wordUnary'
          (And.intro moveLedgerUnary'
            (And.intro dependencyUnary'
              (And.intro moveLedgerCont'
                (And.intro classifierCont' (And.intro endpointCont' endpointPkg')))))))
      (And.intro sameMoveLedger (And.intro sameClassifier sameEndpoint))

theorem BraidGroupArtinPacket_artin_ledger_stability [AskSetup] [PackageSetup]
    {strand word moveLedger classifier dependency endpoint strand' word' moveLedger' classifier'
      dependency' endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word moveLedger classifier dependency endpoint bundle pkg ->
      hsame strand strand' ->
        hsame word word' ->
          hsame dependency dependency' ->
            Cont strand' word' moveLedger' ->
              Cont moveLedger' dependency' classifier' ->
                Cont classifier' word' endpoint' ->
                  PkgSig bundle endpoint' pkg ->
                    BraidGroupArtinPacket strand' word' moveLedger' classifier' dependency'
                        endpoint' bundle pkg ∧
                      hsame moveLedger moveLedger' ∧ hsame classifier classifier' ∧
                        hsame endpoint endpoint' :=
  BraidGroupArtinPacket_ledger_stability

theorem BraidGroupArtinPacket_namecert_obligation_surface [AskSetup] [PackageSetup]
    {strand word moveLedger classifier dependency endpoint consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word moveLedger classifier dependency endpoint bundle pkg ->
      Cont endpoint dependency consumer ->
        PkgSig bundle consumer pkg ->
          PositiveUnaryDenominator strand ∧ UnaryHistory word ∧ UnaryHistory moveLedger ∧
            UnaryHistory dependency ∧ UnaryHistory classifier ∧ UnaryHistory endpoint ∧
              UnaryHistory consumer ∧ Cont strand word moveLedger ∧
                Cont moveLedger dependency classifier ∧ Cont classifier word endpoint ∧
                  Cont endpoint dependency consumer ∧ hsame endpoint (append classifier word) ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle consumer pkg := by
  intro packet consumerRow consumerSig
  obtain ⟨strandPositive, wordUnary, moveLedgerUnary, dependencyUnary, strandWordRow,
    classifierRow, endpointRow, endpointSig⟩ := packet
  have classifierUnary : UnaryHistory classifier :=
    unary_cont_closed moveLedgerUnary dependencyUnary classifierRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed classifierUnary wordUnary endpointRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary dependencyUnary consumerRow
  exact
    ⟨strandPositive, wordUnary, moveLedgerUnary, dependencyUnary, classifierUnary, endpointUnary,
      consumerUnary, strandWordRow, classifierRow, endpointRow, consumerRow, endpointRow,
      endpointSig, consumerSig⟩

theorem BraidGroupArtinPacket_knot_closure_empty_boundary [AskSetup] [PackageSetup]
    {strand word moveLedger classifier dependency endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BraidGroupArtinPacket strand word moveLedger classifier dependency endpoint bundle pkg ->
      hsame endpoint BHist.Empty ->
        hsame classifier BHist.Empty ∧ hsame word BHist.Empty := by
  intro packet endpointEmpty
  have endpointRow : Cont classifier word endpoint :=
    packet.right.right.right.right.right.right.left
  have appendedEmpty : append classifier word = BHist.Empty := by
    cases endpointRow
    exact endpointEmpty
  have parts : classifier = BHist.Empty ∧ word = BHist.Empty :=
    append_eq_empty_iff.mp appendedEmpty
  exact And.intro parts.left parts.right

end BEDC.Derived.BraidGroupUp
