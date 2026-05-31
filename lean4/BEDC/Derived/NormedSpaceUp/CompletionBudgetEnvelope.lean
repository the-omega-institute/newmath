import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NormedSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem NormedspaceCompletionBudgetEnvelope [AskSetup] [PackageSetup]
    {vector real norm metric completion transport replay provenance localName normRead metricRead
      budgetRead envelopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory vector ->
      UnaryHistory real ->
        UnaryHistory norm ->
          UnaryHistory metric ->
            UnaryHistory completion ->
              UnaryHistory transport ->
                UnaryHistory localName ->
                  Cont vector norm normRead ->
                    Cont norm real metricRead ->
                      Cont metric completion budgetRead ->
                        Cont budgetRead transport replay ->
                          Cont replay localName envelopeRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row envelopeRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row vector ∨ hsame row real ∨
                                        hsame row norm ∨ hsame row metric ∨
                                          hsame row completion ∨ hsame row envelopeRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                        PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                                    UnaryHistory budgetRead ∧ UnaryHistory replay ∧
                                      UnaryHistory envelopeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro vectorUnary realUnary normUnary metricUnary completionUnary transportUnary
    localNameUnary normRoute metricRoute budgetRoute replayRoute envelopeRoute
    provenancePkg localNamePkg
  have normReadUnary : UnaryHistory normRead :=
    unary_cont_closed vectorUnary normUnary normRoute
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary realUnary metricRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed metricUnary completionUnary budgetRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed budgetReadUnary transportUnary replayRoute
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed replayUnary localNameUnary envelopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row envelopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row vector ∨ hsame row real ∨ hsame row norm ∨ hsame row metric ∨
              hsame row completion ∨ hsame row envelopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro envelopeRead ⟨hsame_refl envelopeRead, envelopeUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact
    ⟨cert, normReadUnary, metricReadUnary, budgetReadUnary, replayUnary, envelopeUnary⟩

end BEDC.Derived.NormedSpaceUp
