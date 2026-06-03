import BEDC.Derived.NormedSpaceUp
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

theorem NormedSpaceCarrier_completion_request_budget [AskSetup] [PackageSetup]
    {V R N M Q H T P C metricRead completionRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NormedSpaceCarrier V R N M Q H T P C bundle pkg ->
      Cont V N metricRead ->
        Cont metricRead Q completionRead ->
          Cont completionRead H budgetRead ->
            PkgSig bundle budgetRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
                      hsame row H ∨ hsame row budgetRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont metricRead Q completionRead ∧
                      Cont completionRead H budgetRead ∧ PkgSig bundle budgetRead pkg)
                  hsame ∧
                UnaryHistory metricRead ∧ UnaryHistory completionRead ∧
                  UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier metricRoute completionRoute budgetRoute budgetPkg
  obtain ⟨vUnary, _rUnary, nUnary, _mUnary, qUnary, hUnary, _tUnary, _pUnary, _cUnary,
    _vectorNormRoute, _completionFacingRoute, _replayRoute, _provenancePkg, _localPkg⟩ :=
      carrier
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed vUnary nUnary metricRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary qUnary completionRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed completionUnary hUnary budgetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
              hsame row H ∨ hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metricRead Q completionRead ∧
              Cont completionRead H budgetRead ∧ PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
      exact ⟨source.right, completionRoute, budgetRoute, budgetPkg⟩
  }
  exact ⟨cert, metricUnary, completionUnary, budgetUnary⟩

end BEDC.Derived.NormedSpaceUp
