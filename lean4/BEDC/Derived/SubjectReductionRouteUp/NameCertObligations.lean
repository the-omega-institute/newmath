import BEDC.Derived.SubjectReductionRouteUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.SubjectReductionRouteUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem SubjectReductionRouteNameCertObligations
    {beta application lambda pi bundle setup invocation consumer transport route provenance name
      handoff : BHist} :
    Cont bundle invocation handoff →
      UnaryHistory beta →
        UnaryHistory application →
          UnaryHistory lambda →
            UnaryHistory pi →
              UnaryHistory bundle →
                UnaryHistory setup →
                  UnaryHistory invocation →
                    UnaryHistory consumer →
                      UnaryHistory transport →
                        UnaryHistory route →
                          UnaryHistory provenance →
                            UnaryHistory name →
                              SemanticNameCert
                                  (fun row : BHist => hsame row handoff ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row beta ∨ hsame row application ∨
                                      hsame row lambda ∨ hsame row pi ∨ hsame row bundle ∨
                                        hsame row setup ∨ hsame row invocation ∨
                                          hsame row consumer ∨ hsame row transport ∨
                                            hsame row route ∨ hsame row provenance ∨
                                              hsame row name ∨ hsame row handoff)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont bundle invocation handoff)
                                  hsame ∧
                                UnaryHistory handoff := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro bundleRoute unaryBeta unaryApplication unaryLambda unaryPi unaryBundle unarySetup
    unaryInvocation unaryConsumer unaryTransport unaryRoute unaryProvenance unaryName
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed unaryBundle unaryInvocation bundleRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro handoff ⟨hsame_refl handoff, handoffUnary⟩
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
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left)))))))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, bundleRoute⟩
    }
  · exact handoffUnary

end BEDC.Derived.SubjectReductionRouteUp
