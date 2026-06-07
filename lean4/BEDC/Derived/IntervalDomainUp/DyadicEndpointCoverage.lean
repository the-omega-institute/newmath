import BEDC.Derived.IntervalDomainUp.NameCertObligations
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainDyadicEndpointCoverage
    {L R N W Q E H C P A dyadic toleranceRead endpointRead refinementRead sealRead : BHist} :
    UnaryHistory L ->
      UnaryHistory R ->
        UnaryHistory dyadic ->
          UnaryHistory W ->
            UnaryHistory Q ->
              UnaryHistory E ->
                Cont R dyadic toleranceRead ->
                  Cont L toleranceRead endpointRead ->
                    Cont W Q refinementRead ->
                      Cont endpointRead E sealRead ->
                        IntervalDomainTasteGate_single_carrier_alignment_fields
                            (IntervalDomainUp.mk L R N W Q E H C P A) =
                          [L, R, N, W, Q, E, H, C, P, A] ∧
                          SemanticNameCert
                              (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row dyadic ∨ hsame row R ∨ hsame row toleranceRead ∨
                                  hsame row endpointRead ∨ hsame row sealRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont R dyadic toleranceRead ∧
                                  Cont L toleranceRead endpointRead ∧ Cont endpointRead E sealRead)
                              hsame ∧
                            UnaryHistory toleranceRead ∧
                              UnaryHistory endpointRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro leftUnary rationalUnary dyadicUnary windowUnary regseqUnary realSealUnary
    toleranceRoute endpointRoute _refinementRoute sealRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed rationalUnary dyadicUnary toleranceRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary toleranceUnary endpointRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary realSealUnary sealRoute
  have _refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed windowUnary regseqUnary _refinementRoute
  constructor
  · rfl
  · constructor
    · exact {
        core := {
          carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
          exact ⟨source.right, toleranceRoute, endpointRoute, sealRoute⟩
      }
    · exact ⟨toleranceUnary, endpointUnary, sealUnary⟩

end BEDC.Derived.IntervalDomainUp
