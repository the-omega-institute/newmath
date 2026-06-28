import BEDC.Derived.AxisUnarySpineNormalizerUp.NameCertObligations
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisUnarySpineNormalizerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem AxisUnarySpineNormalizerScopeBinding
    {sourceSpine axisZeroSpine lengthLedger standardBoundary componentTransport
      continuationRoutes provenance name boundaryRead replayRead : BHist} :
    UnaryHistory sourceSpine ->
      UnaryHistory axisZeroSpine ->
        UnaryHistory lengthLedger ->
          UnaryHistory standardBoundary ->
            Cont sourceSpine lengthLedger boundaryRead ->
              Cont boundaryRead standardBoundary replayRead ->
                hsame replayRead standardBoundary ->
                  SemanticNameCert
                      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row sourceSpine ∨ hsame row axisZeroSpine ∨
                          hsame row lengthLedger ∨ hsame row standardBoundary ∨
                            hsame row componentTransport ∨ hsame row continuationRoutes ∨
                              hsame row provenance ∨ hsame row name ∨
                                hsame row replayRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont sourceSpine lengthLedger boundaryRead ∧
                          Cont boundaryRead standardBoundary replayRead)
                      hsame ∧
                    hsame replayRead standardBoundary := by
  -- BEDC touchpoint anchor: AxisUnarySpineNormalizerUp BHist Cont hsame SemanticNameCert UnaryHistory
  intro sourceUnary _axisUnary lengthUnary boundaryUnary sourceRoute replayRoute sameBoundary
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sourceUnary lengthUnary sourceRoute
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryReadUnary boundaryUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceSpine ∨ hsame row axisZeroSpine ∨ hsame row lengthLedger ∨
              hsame row standardBoundary ∨ hsame row componentTransport ∨
                hsame row continuationRoutes ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceSpine lengthLedger boundaryRead ∧
              Cont boundaryRead standardBoundary replayRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, replayRoute⟩
  }
  exact ⟨cert, sameBoundary⟩

end BEDC.Derived.AxisUnarySpineNormalizerUp
