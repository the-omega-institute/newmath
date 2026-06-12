import BEDC.Derived.IntervalDomainUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainDirectedCompletionScope
    {L R N W Q E H C P A refinementRead directedRead endpointRead sealRead
      namedRead : BHist} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory N ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory E ->
                UnaryHistory A ->
                  Cont L R refinementRead ->
                    Cont refinementRead N directedRead ->
                      Cont W Q endpointRead ->
                        Cont directedRead endpointRead sealRead ->
                          Cont sealRead A namedRead ->
                            hsame H C ->
                              IntervalDomainTasteGate_single_carrier_alignment_fields
                                    (IntervalDomainUp.mk L R N W Q E H C P A) =
                                  [L, R, N, W, Q, E, H, C, P, A] ∧
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row L ∨ hsame row R ∨ hsame row N ∨
                                        hsame row W ∨ hsame row Q ∨ hsame row E ∨
                                          hsame row sealRead ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont L R refinementRead ∧
                                        Cont refinementRead N directedRead ∧
                                          Cont W Q endpointRead ∧
                                            Cont directedRead endpointRead sealRead ∧
                                              Cont sealRead A namedRead ∧ hsame H C)
                                    hsame ∧
                                  UnaryHistory refinementRead ∧ UnaryHistory directedRead ∧
                                    UnaryHistory endpointRead ∧ UnaryHistory sealRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro lUnary rUnary nUnary wUnary qUnary _eUnary aUnary refinementRoute directedRoute
    endpointRoute sealRoute namedRoute structuralSame
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed lUnary rUnary refinementRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed refinementUnary nUnary directedRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed wUnary qUnary endpointRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed directedUnary endpointUnary sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary aUnary namedRoute
  constructor
  · rfl
  · constructor
    · exact {
        core := {
          carrier_inhabited :=
            Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
          exact
            ⟨source.right, refinementRoute, directedRoute, endpointRoute, sealRoute,
              namedRoute, structuralSame⟩
      }
    · exact ⟨refinementUnary, directedUnary, endpointUnary, sealUnary, namedUnary⟩

end BEDC.Derived.IntervalDomainUp
