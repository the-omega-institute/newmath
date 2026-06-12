import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.IntervalDomainUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem IntervalDomainRegularCauchyWindow
    {located rational nested stream regseq realSeal transport replay provenance localName
      endpointRead refinementRead sealRead structuralRead : BHist} :
    UnaryHistory located ->
      UnaryHistory rational ->
        UnaryHistory nested ->
          UnaryHistory stream ->
            UnaryHistory regseq ->
              UnaryHistory realSeal ->
                UnaryHistory transport ->
                  UnaryHistory replay ->
                    Cont stream regseq endpointRead ->
                      Cont rational endpointRead refinementRead ->
                        Cont refinementRead realSeal sealRead ->
                          Cont transport replay structuralRead ->
                            hsame provenance localName ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row stream ∨ hsame row regseq ∨
                                      hsame row rational ∨ hsame row refinementRead ∨
                                        hsame row realSeal ∨ hsame row sealRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont stream regseq endpointRead ∧
                                      Cont rational endpointRead refinementRead ∧
                                        Cont refinementRead realSeal sealRead ∧
                                          hsame provenance localName)
                                  hsame ∧
                                UnaryHistory endpointRead ∧
                                  UnaryHistory refinementRead ∧
                                    UnaryHistory sealRead ∧ UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert UnaryHistory
  intro _locatedUnary rationalUnary _nestedUnary streamUnary regseqUnary realSealUnary
    transportUnary replayUnary endpointRoute refinementRoute sealRoute structuralRoute
    provenanceSameName
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed streamUnary regseqUnary endpointRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed rationalUnary endpointUnary refinementRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed refinementUnary realSealUnary sealRoute
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary structuralRoute
  constructor
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, endpointRoute, refinementRoute, sealRoute,
            provenanceSameName⟩
    }
  · exact ⟨endpointUnary, refinementUnary, sealUnary, structuralUnary⟩

end BEDC.Derived.IntervalDomainUp
