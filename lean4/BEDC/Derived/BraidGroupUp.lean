import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.BraidGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

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

end BEDC.Derived.BraidGroupUp
