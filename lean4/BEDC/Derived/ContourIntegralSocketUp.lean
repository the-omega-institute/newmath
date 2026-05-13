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

end BEDC.Derived.ContourIntegralSocketUp
