import BEDC.Derived.IntervalDomainUp.NameCertObligations
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainFiniteEndpointOrder
    {L R N W Q E H C P A endpointRead refinementRead sealRead : BHist} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory N ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory E ->
                Cont R L endpointRead ->
                  Cont endpointRead N refinementRead ->
                    Cont refinementRead E sealRead ->
                      IntervalDomainTasteGate_single_carrier_alignment_fields
                          (IntervalDomainUp.mk L R N W Q E H C P A) =
                        [L, R, N, W, Q, E, H, C, P, A] ∧
                        SemanticNameCert
                            (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row L ∨ hsame row R ∨ hsame row N ∨
                                hsame row endpointRead ∨ hsame row refinementRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont R L endpointRead ∧
                                Cont endpointRead N refinementRead)
                            hsame ∧
                          UnaryHistory endpointRead ∧
                            UnaryHistory refinementRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro leftUnary rationalUnary nestedUnary _windowUnary _regseqUnary realSealUnary
    endpointRoute refinementRoute sealRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed rationalUnary leftUnary endpointRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed endpointUnary nestedUnary refinementRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed refinementUnary realSealUnary sealRoute
  constructor
  · rfl
  · constructor
    · exact {
        core := {
          carrier_inhabited := Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
          exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
        ledger_sound := by
          intro _row source
          exact ⟨source.right, endpointRoute, refinementRoute⟩
      }
    · exact ⟨endpointUnary, refinementUnary, sealUnary⟩

end BEDC.Derived.IntervalDomainUp
