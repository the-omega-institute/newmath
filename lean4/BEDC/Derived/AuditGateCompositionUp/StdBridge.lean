import BEDC.Derived.AuditGateCompositionUp.BoundaryObligation
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

theorem AuditGateCompositionUp_StdBridge [AskSetup] [PackageSetup]
    {_gateLeft _gateRight boundaryLeft boundaryRight _refusalLeft _refusalRight composedTrace
      _transport replay _provenance _localName boundaryRead traceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory boundaryLeft →
      UnaryHistory boundaryRight →
        UnaryHistory composedTrace →
          UnaryHistory replay →
            Cont boundaryLeft boundaryRight boundaryRead →
              Cont boundaryRead composedTrace traceRead →
                Cont traceRead replay publicRead →
                  PkgSig bundle publicRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row boundaryLeft ∨ hsame row boundaryRight ∨
                            hsame row composedTrace ∨ hsame row traceRead ∨
                              hsame row publicRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont boundaryLeft boundaryRight boundaryRead ∧
                            Cont boundaryRead composedTrace traceRead ∧
                              Cont traceRead replay publicRead ∧
                                PkgSig bundle publicRead pkg)
                        hsame ∧
                      UnaryHistory boundaryRead ∧ UnaryHistory traceRead ∧
                        UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro boundaryLeftUnary boundaryRightUnary composedTraceUnary replayUnary boundaryRoute
    traceRoute publicRoute publicPkg
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed boundaryLeftUnary boundaryRightUnary boundaryRoute
  have traceReadUnary : UnaryHistory traceRead :=
    unary_cont_closed boundaryReadUnary composedTraceUnary traceRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed traceReadUnary replayUnary publicRoute
  have sourcePublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row boundaryLeft ∨ hsame row boundaryRight ∨ hsame row composedTrace ∨
              hsame row traceRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont boundaryLeft boundaryRight boundaryRead ∧
              Cont boundaryRead composedTrace traceRead ∧ Cont traceRead replay publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, boundaryRoute, traceRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, boundaryReadUnary, traceReadUnary, publicReadUnary⟩

end BEDC.Derived.AuditGateCompositionUp
