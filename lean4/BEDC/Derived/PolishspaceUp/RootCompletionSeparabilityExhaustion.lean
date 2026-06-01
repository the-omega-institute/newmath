import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRootCompletionSeparabilityExhaustion [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName completionRead separableRead handoffRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg →
      Cont metric complete completionRead →
        Cont metric separable separableRead →
          Cont completionRead separableRead handoffRead →
            Cont handoffRead localName terminalRead →
              PkgSig bundle handoffRead pkg →
                PkgSig bundle terminalRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
                          hsame row stream ∨ hsame row readback ∨ hsame row alignment ∨
                            hsame row handoffRead ∨ hsame row terminalRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle terminalRead pkg)
                      hsame ∧
                    UnaryHistory completionRead ∧ UnaryHistory separableRead ∧
                      UnaryHistory handoffRead ∧ UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier metricCompleteRead metricSeparableRead completeSeparableHandoff
    handoffLocalTerminal _handoffPkg terminalPkg
  obtain ⟨metricUnary, completeUnary, separableUnary, _streamUnary, _readbackUnary,
    _ledgerUnary, _alignmentUnary, _transportUnary, localNameUnary,
    _metricCompleteAlignment, _alignmentStreamReadback, _ledgerTransportRoute,
    provenancePkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteRead
  have separableReadUnary : UnaryHistory separableRead :=
    unary_cont_closed metricUnary separableUnary metricSeparableRead
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed completionUnary separableReadUnary completeSeparableHandoff
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed handoffUnary localNameUnary handoffLocalTerminal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row separable ∨
              hsame row stream ∨ hsame row readback ∨ hsame row alignment ∨
                hsame row handoffRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, terminalPkg⟩
  }
  exact ⟨cert, completionUnary, separableReadUnary, handoffUnary, terminalUnary⟩

end BEDC.Derived.PolishspaceUp
