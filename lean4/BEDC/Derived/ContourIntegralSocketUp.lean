import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ContourIntegralSocketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def ContourIntegralSocketCarrier
    (contour holomorphic modulus output ledger transport route provenance name : BHist) : Prop :=
  hsame output (BHist.e0 modulus) ∧ Cont contour holomorphic route ∧
    Cont route ledger provenance ∧ hsame name name

theorem ContourIntegralSocketSemanticNameCert :
    SemanticNameCert
      (fun row : BHist =>
        ContourIntegralSocketCarrier BHist.Empty BHist.Empty BHist.Empty row
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty row)
      (fun row : BHist =>
        ContourIntegralSocketCarrier BHist.Empty BHist.Empty BHist.Empty row
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty row)
      (fun row : BHist =>
        ContourIntegralSocketCarrier BHist.Empty BHist.Empty BHist.Empty row
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty row)
      hsame := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert ContourIntegralSocketCarrier
  let Carrier : BHist -> Prop := fun row : BHist =>
    ContourIntegralSocketCarrier BHist.Empty BHist.Empty BHist.Empty row
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty row
  have routeRead : Cont BHist.Empty BHist.Empty BHist.Empty := by
    rfl
  have provenanceRead : Cont BHist.Empty BHist.Empty BHist.Empty := by
    rfl
  have witness : Carrier (BHist.e0 BHist.Empty) := by
    exact And.intro rfl (And.intro routeRead (And.intro provenanceRead rfl))
  exact {
    core := {
      carrier_inhabited := Exists.intro (BHist.e0 BHist.Empty) witness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }

theorem ContourIntegralSocketCarrier_transport
    {contour holomorphic modulus output ledger transport route provenance name output' route'
      provenance' : BHist} :
    ContourIntegralSocketCarrier contour holomorphic modulus output ledger transport route
      provenance name →
      hsame output output' →
      Cont contour holomorphic route' →
      Cont route' ledger provenance' →
      ContourIntegralSocketCarrier contour holomorphic modulus output' ledger transport route'
        provenance' name := by
  -- BEDC touchpoint anchor: BHist hsame Cont ContourIntegralSocketCarrier
  intro carrier sameOutput routeRead provenanceRead
  cases carrier with
  | intro outputRead carrierTail =>
      cases carrierTail with
      | intro _oldRoute carrierTail =>
          cases carrierTail with
          | intro _oldProvenance nameRead =>
              constructor
              · exact hsame_trans (hsame_symm sameOutput) outputRead
              · constructor
                · exact routeRead
                · constructor
                  · exact provenanceRead
                  · exact nameRead

theorem ContourIntegralSocketCarrier_component_transport_closure
    {contour holomorphic modulus output output' ledger transport route provenance name : BHist}
    (carrier :
      ContourIntegralSocketCarrier contour holomorphic modulus output ledger transport route
        provenance name)
    (sameOutput : hsame output' output) :
    ContourIntegralSocketCarrier contour holomorphic modulus output' ledger transport route
        provenance name ∧
      Cont contour holomorphic route ∧ Cont route ledger provenance := by
  -- BEDC touchpoint anchor: BHist hsame Cont ContourIntegralSocketCarrier
  cases sameOutput
  exact And.intro carrier (And.intro carrier.right.left carrier.right.right.left)

theorem ContourIntegralSocketCarrier_ledger_exactness
    {contour holomorphic modulus output ledger transport route provenance name lawRead : BHist} :
    ContourIntegralSocketCarrier contour holomorphic modulus output ledger transport route
        provenance name →
      Cont ledger route lawRead →
        SemanticNameCert
            (fun row : BHist => hsame row lawRead ∧ Cont ledger route lawRead)
            (fun row : BHist => hsame row lawRead ∧ Cont route ledger provenance)
            (fun row : BHist => hsame row lawRead ∧ Cont ledger route lawRead)
            hsame ∧
          Cont contour holomorphic route ∧
            Cont route ledger provenance ∧ Cont ledger route lawRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert ContourIntegralSocketCarrier
  intro carrier lawRoute
  have contourRoute : Cont contour holomorphic route := carrier.right.left
  have provenanceRoute : Cont route ledger provenance := carrier.right.right.left
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lawRead ∧ Cont ledger route lawRead)
          (fun row : BHist => hsame row lawRead ∧ Cont route ledger provenance)
          (fun row : BHist => hsame row lawRead ∧ Cont ledger route lawRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lawRead ⟨hsame_refl lawRead, lawRoute⟩
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
        intro row row' sameRows source
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, provenanceRoute⟩
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨cert, contourRoute, provenanceRoute, lawRoute⟩

theorem ContourIntegralSocketBoundaryRouteTotality
    {contour holomorphic modulus output ledger transport route provenance name : BHist} :
    ContourIntegralSocketCarrier contour holomorphic modulus output ledger transport route
        provenance name →
      SemanticNameCert
          (fun row : BHist =>
            hsame row (append route provenance) ∧
              Cont route provenance (append route provenance))
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row ledger ∨
              hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                hsame row (append route provenance))
          (fun row : BHist =>
            hsame row (append route provenance) ∧ Cont contour holomorphic route ∧
              Cont route ledger provenance ∧ Cont route provenance (append route provenance))
          hsame ∧
        Cont contour holomorphic route ∧ Cont route ledger provenance ∧
          Cont route provenance (append route provenance) := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert ContourIntegralSocketCarrier
  intro carrier
  have contourRoute : Cont contour holomorphic route := carrier.right.left
  have provenanceRoute : Cont route ledger provenance := carrier.right.right.left
  have boundaryRoute : Cont route provenance (append route provenance) := rfl
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row (append route provenance) ∧
              Cont route provenance (append route provenance))
          (fun row : BHist =>
            hsame row contour ∨ hsame row holomorphic ∨ hsame row ledger ∨
              hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                hsame row (append route provenance))
          (fun row : BHist =>
            hsame row (append route provenance) ∧ Cont contour holomorphic route ∧
              Cont route ledger provenance ∧ Cont route provenance (append route provenance))
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro (append route provenance)
          ⟨hsame_refl (append route provenance), boundaryRoute⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, contourRoute, provenanceRoute, source.right⟩
  }
  exact ⟨cert, contourRoute, provenanceRoute, boundaryRoute⟩

end BEDC.Derived.ContourIntegralSocketUp
