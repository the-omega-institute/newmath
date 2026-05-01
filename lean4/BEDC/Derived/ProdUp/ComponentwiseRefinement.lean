import BEDC.Derived.ProdUp.PairRepresentation

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ProdComponentHistoryClassifier_source_refinement
    {Left Right Left' Right' : BHist → Prop}
    {LeftEq RightEq LeftEq' RightEq' : BHist → BHist → Prop}
    (left_carrier : ∀ {u : BHist}, Left u → Left' u)
    (right_carrier : ∀ {u : BHist}, Right u → Right' u)
    (left_rel : ∀ {a b : BHist}, LeftEq a b → LeftEq' a b)
    (right_rel : ∀ {a b : BHist}, RightEq a b → RightEq' a b) {h k : BHist} :
    ProdComponentHistoryClassifier Left Right LeftEq RightEq h k →
      ProdComponentHistoryClassifier Left' Right' LeftEq' RightEq' h k := by
  intro classifier
  cases classifier with
  | intro lh restLH =>
      cases restLH with
      | intro rh restRH =>
          cases restRH with
          | intro lk restLK =>
              cases restLK with
              | intro rk data =>
                  cases data with
                  | intro leftH rest =>
                      cases rest with
                      | intro rightH rest =>
                          cases rest with
                          | intro contH rest =>
                              cases rest with
                              | intro leftK rest =>
                                  cases rest with
                                  | intro rightK rest =>
                                      cases rest with
                                      | intro contK componentRel =>
                                          cases componentRel with
                                          | intro sameLeft sameRight =>
                                              exact Exists.intro lh
                                                (Exists.intro rh
                                                  (Exists.intro lk
                                                    (Exists.intro rk
                                                      (And.intro (left_carrier leftH)
                                                        (And.intro (right_carrier rightH)
                                                          (And.intro contH
                                                            (And.intro (left_carrier leftK)
                                                              (And.intro
                                                                (right_carrier rightK)
                                                                (And.intro contK
                                                                  (And.intro
                                                                    (left_rel sameLeft)
                                                                    (right_rel
                                                                      sameRight)))))))))))

theorem ProdComponentHistoryClassifier_inversion
    {Left Right : BHist → Prop} {LeftEq RightEq : BHist → BHist → Prop}
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq)
    (left_trans : ∀ {a b c : BHist}, LeftEq a b → LeftEq b c → LeftEq a c)
    (right_trans : ∀ {a b c : BHist}, RightEq a b → RightEq b c → RightEq a c)
    {h k l r l' r' : BHist} :
    ProdPairRep Left Right h l r →
      ProdPairRep Left Right k l' r' →
        ProdComponentHistoryClassifier Left Right LeftEq RightEq h k →
          LeftEq l l' ∧ RightEq r r' := by
  intro repH repK classifier
  cases classifier with
  | intro lh restLH =>
      cases restLH with
      | intro rh restRH =>
          cases restRH with
          | intro lk restLK =>
              cases restLK with
              | intro rk data =>
                  cases data with
                  | intro leftH rest =>
                      cases rest with
                      | intro rightH rest =>
                          cases rest with
                          | intro contH rest =>
                              cases rest with
                              | intro leftK rest =>
                                  cases rest with
                                  | intro rightK rest =>
                                      cases rest with
                                      | intro contK componentRel =>
                                          cases componentRel with
                                          | intro sameLeft sameRight =>
                                              have witnessH :
                                                  ProdPairRep Left Right h lh rh :=
                                                And.intro leftH (And.intro rightH contH)
                                              have witnessK :
                                                  ProdPairRep Left Right k lk rk :=
                                                And.intro leftK (And.intro rightK contK)
                                              have leftAtH : LeftEq l lh :=
                                                (coherent repH witnessH).left
                                              have rightAtH : RightEq r rh :=
                                                (coherent repH witnessH).right
                                              have leftAtK : LeftEq lk l' :=
                                                (coherent witnessK repK).left
                                              have rightAtK : RightEq rk r' :=
                                                (coherent witnessK repK).right
                                              constructor
                                              · exact left_trans leftAtH
                                                  (left_trans sameLeft leftAtK)
                                              · exact right_trans rightAtH
                                                  (right_trans sameRight rightAtK)

theorem ProdComponentHistoryClassifier_descends_to_envelope
    {Left Right : BHist → Prop} {LeftEq RightEq : BHist → BHist → Prop}
    (left_sound : ∀ {x y : BHist}, LeftEq x y → hsame x y)
    (right_sound : ∀ {x y : BHist}, RightEq x y → hsame x y) {h k : BHist} :
    ProdComponentHistoryClassifier Left Right LeftEq RightEq h k →
      ProdHistoryClassifier Left Right h k := by
  intro classifier
  cases classifier with
  | intro lh restLH =>
      cases restLH with
      | intro rh restRH =>
          cases restRH with
          | intro lk restLK =>
              cases restLK with
              | intro rk data =>
                  cases data with
                  | intro leftH rest =>
                      cases rest with
                      | intro rightH rest =>
                          cases rest with
                          | intro contH rest =>
                              cases rest with
                              | intro leftK rest =>
                                  cases rest with
                                  | intro rightK rest =>
                                      cases rest with
                                      | intro contK componentRel =>
                                          cases componentRel with
                                          | intro sameLeft sameRight =>
                                              have sameHK : hsame h k :=
                                                BEDC.FKernel.Cont.cont_respects_hsame
                                                  (left_sound sameLeft)
                                                  (right_sound sameRight)
                                                  contH contK
                                              exact And.intro
                                                (ProdHistoryCarrier_cont_intro
                                                  leftH rightH contH)
                                                (And.intro
                                                  (ProdHistoryCarrier_cont_intro
                                                    leftK rightK contK)
                                                  sameHK)

theorem ProdComponentHistoryClassifier_carrier_reflexivity_from_source_certificates
    {Left Right : BHist → Prop} {LeftEq RightEq : BHist → BHist → Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    {h : BHist} :
    ProdHistoryCarrier Left Right h →
      ProdComponentHistoryClassifier Left Right LeftEq RightEq h h := by
  intro carrier
  cases carrier with
  | intro leftHist restLeft =>
      cases restLeft with
      | intro rightHist data =>
          cases data with
          | intro leftCarrier rest =>
              cases rest with
              | intro rightCarrier contH =>
                  exact Exists.intro leftHist
                    (Exists.intro rightHist
                      (Exists.intro leftHist
                        (Exists.intro rightHist
                          (And.intro leftCarrier
                            (And.intro rightCarrier
                              (And.intro contH
                                (And.intro leftCarrier
                                  (And.intro rightCarrier
                                    (And.intro contH
                                      (And.intro
                                        (leftCert.equiv_refl leftCarrier)
                                        (rightCert.equiv_refl rightCarrier)))))))))))

theorem ProdHistoryClassifier_pair_coherent_componentwise_hsame
    {Left Right : BHist → Prop}
    (coherent : ProdPairRepCoherent Left Right hsame hsame) {h k : BHist} :
    ProdHistoryClassifier Left Right h k →
      ProdComponentHistoryClassifier Left Right hsame hsame h k := by
  intro classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          cases carrierH with
          | intro lh restLH =>
              cases restLH with
              | intro rh dataH =>
                  cases dataH with
                  | intro leftH restH =>
                      cases restH with
                      | intro rightH contH =>
                          cases carrierK with
                          | intro lk restLK =>
                              cases restLK with
                              | intro rk dataK =>
                                  cases dataK with
                                  | intro leftK restK =>
                                      cases restK with
                                      | intro rightK contK =>
                                          have repH : ProdPairRep Left Right h lh rh :=
                                            And.intro leftH (And.intro rightH contH)
                                          have repK : ProdPairRep Left Right k lk rk :=
                                            And.intro leftK (And.intro rightK contK)
                                          have components :
                                              hsame lh lk ∧ hsame rh rk :=
                                            ProdPairRep_hsame_coherence coherent repH repK
                                              sameHK
                                          exact Exists.intro lh
                                            (Exists.intro rh
                                              (Exists.intro lk
                                                (Exists.intro rk
                                                  (And.intro leftH
                                                    (And.intro rightH
                                                      (And.intro contH
                                                        (And.intro leftK
                                                          (And.intro rightK
                                                            (And.intro contK
                                                              components)))))))))

end BEDC.Derived.ProdUp
