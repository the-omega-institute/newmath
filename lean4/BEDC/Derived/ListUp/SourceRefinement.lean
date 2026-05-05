import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist

theorem FramedListSemanticFields_source_refinement {A B : BHist -> Prop}
    (carrierIncl : forall x : BHist, A x -> B x) :
    (forall {h : BHist}, FramedListHistoryCarrier A h -> FramedListHistoryCarrier B h) ∧
      (forall {h : BHist} {xs : ListCarrier BHist},
        FramedListSpineRep A h xs -> FramedListSpineRep B h xs) ∧
        (FramedListSpineRep A (BHist.e0 BHist.Empty) [] ->
          FramedListSpineRep B (BHist.e0 BHist.Empty) []) ∧
          (forall {RelA RelB : BHist -> BHist -> Prop},
            (forall x y : BHist, RelA x y -> RelB x y) ->
              forall {h k : BHist},
                FramedListBridgeClassifier A RelA h k ->
                  FramedListBridgeClassifier B RelB h k) := by
  have refineRep :
      forall {h : BHist} {xs : ListCarrier BHist},
        FramedListSpineRep A h xs -> FramedListSpineRep B h xs := by
    intro h xs rep
    cases rep with
    | intro entries endpoint =>
        constructor
        · intro x memX
          exact carrierIncl x (entries x memX)
        · exact endpoint
  have refineCarrier :
      forall {h : BHist}, FramedListHistoryCarrier A h -> FramedListHistoryCarrier B h := by
    intro h carrier
    cases carrier with
    | intro xs rep =>
        exact Exists.intro xs (refineRep rep)
  have refineClassifier :
      forall {RelA RelB : BHist -> BHist -> Prop},
        (forall x y : BHist, RelA x y -> RelB x y) ->
          forall {xs ys : ListCarrier BHist},
            ListClassifierSpec RelA xs ys -> ListClassifierSpec RelB xs ys := by
    intro RelA RelB relIncl xs
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
  constructor
  · exact refineCarrier
  · constructor
    · intro h xs rep
      exact refineRep rep
    · constructor
      · intro nilRep
        exact refineRep nilRep
      · intro RelA RelB relIncl h k bridge
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
                              (And.intro (refineRep rightRep)
                                (refineClassifier relIncl classified))))

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

theorem FramedListBridgeClassifier_e1_left_source_refinement {A B : BHist → Prop}
    {RelA RelB : BHist → BHist → Prop}
    (carrierIncl : ∀ x : BHist, A x → B x)
    (relIncl : ∀ x y : BHist, RelA x y → RelB x y) {t k : BHist} :
    FramedListBridgeClassifier A RelA (BHist.e1 t) k →
      FramedListBridgeClassifier B RelB (BHist.e1 t) k := by
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
