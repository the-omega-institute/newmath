import BEDC.Derived.ConnectedIntervalUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConnectedIntervalUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ConnectedIntervalCarrier_real_route
    {left right window branch nested signRoute realSeal transport replay provenance localName
      endpointRead windowRead sealRead : BHist} :
    Cont left right endpointRead ->
      Cont endpointRead window windowRead ->
        Cont windowRead realSeal sealRead ->
          UnaryHistory left ->
            UnaryHistory right ->
              UnaryHistory window ->
                UnaryHistory realSeal ->
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row left ∨ hsame row right ∨ hsame row window ∨
                          hsame row realSeal ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont left right endpointRead ∧
                          Cont endpointRead window windowRead ∧ Cont windowRead realSeal sealRead)
                      hsame ∧
                    UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro endpointRoute windowRoute sealRoute leftUnary rightUnary windowUnary sealUnary
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed leftUnary rightUnary endpointRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed endpointUnary windowUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary sealRoute
  have sourceSeal : hsame sealRead sealRead ∧ UnaryHistory sealRead :=
    ⟨hsame_refl sealRead, sealReadUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row left ∨ hsame row right ∨ hsame row window ∨ hsame row realSeal ∨
            hsame row sealRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont left right endpointRead ∧ Cont endpointRead window windowRead ∧
            Cont windowRead realSeal sealRead)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row col sameRowCol
        exact hsame_symm sameRowCol
      equiv_trans := by
        intro row col out sameRowCol sameColOut
        exact hsame_trans sameRowCol sameColOut
      carrier_respects_equiv := by
        intro row col sameRowCol sourceRow
        cases sameRowCol
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro row sourceRow
      cases sourceRow.left
      exact ⟨sealReadUnary, endpointRoute, windowRoute, sealRoute⟩
  }
  exact ⟨cert, endpointUnary, windowReadUnary, sealReadUnary⟩

end BEDC.Derived.ConnectedIntervalUp
