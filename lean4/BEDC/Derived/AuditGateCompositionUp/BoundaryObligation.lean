import BEDC.Derived.AuditGateCompositionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditGateCompositionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditGateCompositionBoundary_obligation [AskSetup] [PackageSetup]
    {gateLeft gateRight boundaryLeft boundaryRight refusalLeft refusalRight composedTrace
      transport replay provenance localName boundaryRead traceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory gateLeft →
      UnaryHistory gateRight →
        UnaryHistory boundaryLeft →
          UnaryHistory boundaryRight →
            UnaryHistory refusalLeft →
              UnaryHistory refusalRight →
                UnaryHistory composedTrace →
                  UnaryHistory transport →
                    UnaryHistory replay →
                      UnaryHistory provenance →
                        UnaryHistory localName →
                          Cont boundaryLeft boundaryRight boundaryRead →
                            Cont boundaryRead composedTrace traceRead →
                              PkgSig bundle provenance pkg →
                                PkgSig bundle localName pkg →
                                  PkgSig bundle traceRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row traceRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row boundaryLeft ∨
                                            hsame row boundaryRight ∨
                                              hsame row transport ∨ hsame row replay ∨
                                                hsame row composedTrace ∨
                                                  hsame row traceRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧
                                            Cont boundaryLeft boundaryRight boundaryRead ∧
                                              Cont boundaryRead composedTrace traceRead ∧
                                                PkgSig bundle traceRead pkg)
                                        hsame ∧
                                      UnaryHistory boundaryRead ∧ UnaryHistory traceRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro _gateLeftUnary _gateRightUnary boundaryLeftUnary boundaryRightUnary _refusalLeftUnary
    _refusalRightUnary composedTraceUnary _transportUnary _replayUnary _provenanceUnary
    _localNameUnary boundaryRoute traceRoute _provenancePkg _localPkg tracePkg
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryLeftUnary boundaryRightUnary boundaryRoute
  have traceUnary : UnaryHistory traceRead :=
    unary_cont_closed boundaryUnary composedTraceUnary traceRoute
  have sourceTrace : hsame traceRead traceRead ∧ UnaryHistory traceRead :=
    ⟨hsame_refl traceRead, traceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row traceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryLeft ∨ hsame row boundaryRight ∨ hsame row transport ∨
              hsame row replay ∨ hsame row composedTrace ∨ hsame row traceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryLeft boundaryRight boundaryRead ∧
              Cont boundaryRead composedTrace traceRead ∧ PkgSig bundle traceRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro traceRead sourceTrace
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
      exact ⟨source.right, boundaryRoute, traceRoute, tracePkg⟩
  }
  exact ⟨cert, boundaryUnary, traceUnary⟩

end BEDC.Derived.AuditGateCompositionUp
