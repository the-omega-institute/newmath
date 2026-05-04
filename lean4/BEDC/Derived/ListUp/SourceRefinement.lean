import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem FramedListBridgeClassifier_empty_left_source_refinement {A B : BHist → Prop}
    {RelA RelB : BHist → BHist → Prop}
    (carrierIncl : ∀ x : BHist, A x → B x)
    (relIncl : ∀ x y : BHist, RelA x y → RelB x y) {k : BHist} :
    FramedListBridgeClassifier A RelA (BHist.e0 BHist.Empty) k →
      FramedListBridgeClassifier B RelB (BHist.e0 BHist.Empty) k := by
  intro bridge
  have refineRep :
      ∀ {h : BHist} {xs : ListCarrier BHist},
        FramedListSpineRep A h xs → FramedListSpineRep B h xs := by
    intro h xs rep
    cases rep with
    | intro entries endpoint =>
        constructor
        · intro x memX
          exact carrierIncl x (entries x memX)
        · exact endpoint
  have refineClassifier :
      ∀ {xs ys : ListCarrier BHist},
        ListClassifierSpec RelA xs ys → ListClassifierSpec RelB xs ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys classified
        cases ys with
        | nil =>
            constructor
        | cons _ _ =>
            cases classified
    | cons x xs ih =>
        intro ys classified
        cases ys with
        | nil =>
            cases classified
        | cons y ys =>
            cases classified with
            | intro headRel tailRel =>
                constructor
                · exact relIncl x y headRel
                · exact ih tailRel
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro leftRep bridgeRest =>
              cases bridgeRest with
              | intro rightRep classified =>
                  exact Exists.intro xs
                    (Exists.intro ys
                      (And.intro (refineRep leftRep)
                        (And.intro (refineRep rightRep) (refineClassifier classified))))

end BEDC.Derived.ListUp
