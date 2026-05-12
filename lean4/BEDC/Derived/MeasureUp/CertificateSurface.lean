import BEDC.Derived.MeasureUp

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def MeasureCertificateSurface
    (event union countable complement disjoint value sigma classifier ledger endpoint : BHist) :
    Prop :=
  MeasureZeroBHistCarrier event ∧
    MeasureZeroBHistCarrier union ∧
      MeasureZeroBHistCarrier countable ∧
        MeasureZeroBHistCarrier complement ∧
          MeasureZeroBHistCarrier disjoint ∧
            MeasureZeroBHistCarrier value ∧
              MeasureZeroBHistClassifier value endpoint ∧
                Cont event union countable ∧
                  Cont complement disjoint ledger ∧
                    hsame classifier (append value endpoint) ∧ hsame sigma sigma

theorem MeasureCertificateSurface_endpoint_namecert
    {event union countable complement disjoint value sigma classifier ledger endpoint : BHist} :
    MeasureCertificateSurface event union countable complement disjoint value sigma classifier
        ledger endpoint ->
      SemanticNameCert
        (fun row : BHist =>
          MeasureCertificateSurface event union countable complement disjoint value sigma
            classifier ledger endpoint ∧ hsame row endpoint)
        (fun row : BHist =>
          MeasureZeroBHistCarrier endpoint ∧
            MeasureZeroBHistClassifier value endpoint ∧ hsame row endpoint)
        (fun row : BHist =>
          Cont event union countable ∧ Cont complement disjoint ledger ∧ hsame row endpoint)
        hsame := by
  intro surface
  have endpointCarrier : MeasureZeroBHistCarrier endpoint :=
    surface.right.right.right.right.right.right.left.right.left
  have valueEndpointClassified : MeasureZeroBHistClassifier value endpoint :=
    surface.right.right.right.right.right.right.left
  have eventUnionCountable : Cont event union countable :=
    surface.right.right.right.right.right.right.right.left
  have complementDisjointLedger : Cont complement disjoint ledger :=
    surface.right.right.right.right.right.right.right.right.left
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro surface (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact And.intro endpointCarrier (And.intro valueEndpointClassified source.right)
    ledger_sound := by
      intro _row source
      exact And.intro eventUnionCountable
        (And.intro complementDisjointLedger source.right)
  }

end BEDC.Derived.MeasureUp
