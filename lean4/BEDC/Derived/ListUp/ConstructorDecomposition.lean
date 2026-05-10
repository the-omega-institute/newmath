import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem FramedListBridgeClassifier_constructor_decomposition {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel) {h k : BHist} :
    FramedListBridgeClassifier A Rel h k ->
      (hsame h (BHist.e0 BHist.Empty) ∧ hsame k (BHist.e0 BHist.Empty)) ∨
        (exists a : BHist, exists b : BHist, exists xs : ListCarrier BHist,
          exists ys : ListCarrier BHist,
            FramedListSpineRep A h (a :: xs) ∧
              FramedListSpineRep A k (b :: ys) ∧
                Rel a b ∧ ListClassifierSpec Rel xs ys) := by
  intro bridge
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repH bridgeRest =>
              cases bridgeRest with
              | intro repK classified =>
                  cases xs with
                  | nil =>
                      cases ys with
                      | nil =>
                          exact Or.inl (And.intro repH.right repK.right)
                      | cons b ys =>
                          cases classified
                  | cons a xs =>
                      cases ys with
                      | nil =>
                          cases classified
                      | cons b ys =>
                          have consConsExactness :
                              ∀ {h k a b : BHist} {xs ys : ListCarrier BHist},
                                FramedListSpineRep A h (a :: xs) →
                                  FramedListSpineRep A k (b :: ys) →
                                    (FramedListBridgeClassifier A Rel h k ↔
                                      Rel a b ∧ ListClassifierSpec Rel xs ys) := by
                            cases FramedListBridgeClassifier_constructor_exactness cert compat with
                            | intro _nilNil rest =>
                                cases rest with
                                | intro _nilCons rest =>
                                    cases rest with
                                    | intro _consNil consCons =>
                                        exact consCons
                          have exactness :
                              FramedListBridgeClassifier A Rel h k ↔
                                Rel a b ∧ ListClassifierSpec Rel xs ys :=
                            consConsExactness (h := h) (k := k)
                              (a := a) (b := b) (xs := xs) (ys := ys) repH repK
                          have headTail : Rel a b ∧ ListClassifierSpec Rel xs ys :=
                            exactness.mp
                              (Exists.intro (a :: xs)
                                (Exists.intro (b :: ys)
                                  (And.intro repH (And.intro repK classified))))
                          exact Or.inr
                            (Exists.intro a
                              (Exists.intro b
                                (Exists.intro xs
                                  (Exists.intro ys
                                    (And.intro repH
                                      (And.intro repK headTail))))))

end BEDC.Derived.ListUp
