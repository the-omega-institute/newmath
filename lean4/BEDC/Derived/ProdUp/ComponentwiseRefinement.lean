import BEDC.Derived.ProdUp.PairRepresentation

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
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

theorem ProdComponentHistoryClassifier_displayed_exactness
    {Left Right : BHist -> Prop} {LeftEq RightEq : BHist -> BHist -> Prop}
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq)
    (left_trans : forall {a b c : BHist}, LeftEq a b -> LeftEq b c -> LeftEq a c)
    (right_trans : forall {a b c : BHist}, RightEq a b -> RightEq b c -> RightEq a c)
    {h k l r l' r' : BHist} :
    ProdPairRep Left Right h l r ->
      ProdPairRep Left Right k l' r' ->
        (ProdComponentHistoryClassifier Left Right LeftEq RightEq h k <->
          LeftEq l l' /\ RightEq r r') := by
  intro repH repK
  constructor
  · intro classifier
    exact ProdComponentHistoryClassifier_inversion coherent left_trans right_trans
      repH repK classifier
  · intro componentRel
    cases repH with
    | intro leftH restH =>
        cases restH with
        | intro rightH contH =>
            cases repK with
            | intro leftK restK =>
                cases restK with
                | intro rightK contK =>
                    cases componentRel with
                    | intro sameLeft sameRight =>
                        exact Exists.intro l
                          (Exists.intro r
                            (Exists.intro l'
                              (Exists.intro r'
                                (And.intro leftH
                                  (And.intro rightH
                                    (And.intro contH
                                      (And.intro leftK
                                        (And.intro rightK
                                          (And.intro contK
                                            (And.intro sameLeft sameRight))))))))))

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

theorem ProdComponentHistoryClassifier_symm_from_source_certificates
    {Left Right : BHist → Prop} {LeftEq RightEq : BHist → BHist → Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    {h k : BHist} :
    ProdComponentHistoryClassifier Left Right LeftEq RightEq h k →
      ProdComponentHistoryClassifier Left Right LeftEq RightEq k h := by
  intro classifier
  exact
    match classifier with
    | ⟨lh, rh, lk, rk, leftH, rightH, contH, leftK, rightK, contK,
        sameLeft, sameRight⟩ =>
        ⟨lk, rk, lh, rh, leftK, rightK, contK, leftH, rightH, contH,
          leftCert.equiv_symm sameLeft, rightCert.equiv_symm sameRight⟩

theorem ProdComponentHistoryClassifier_trans_from_pair_coherence
    {Left Right : BHist → Prop} {LeftEq RightEq : BHist → BHist → Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq) {h k u : BHist} :
    ProdComponentHistoryClassifier Left Right LeftEq RightEq h k →
      ProdComponentHistoryClassifier Left Right LeftEq RightEq k u →
        ProdComponentHistoryClassifier Left Right LeftEq RightEq h u := by
  intro classifierHK classifierKU
  exact
    match classifierHK, classifierKU with
    | ⟨lh, rh, lk, rk, leftH, rightH, contH, leftK, rightK, contK,
        sameLeftHK, sameRightHK⟩,
      ⟨lk', rk', lu, ru, leftK', rightK', contK', leftU, rightU, contU,
        sameLeftKU, sameRightKU⟩ =>
        let repK : ProdPairRep Left Right k lk rk := ⟨leftK, rightK, contK⟩
        let repK' : ProdPairRep Left Right k lk' rk' := ⟨leftK', rightK', contK'⟩
        let middle : LeftEq lk lk' ∧ RightEq rk rk' := coherent repK repK'
        let sameLeftHU : LeftEq lh lu :=
          leftCert.equiv_trans sameLeftHK
            (leftCert.equiv_trans middle.left sameLeftKU)
        let sameRightHU : RightEq rh ru :=
          rightCert.equiv_trans sameRightHK
            (rightCert.equiv_trans middle.right sameRightKU)
        ⟨lh, rh, lu, ru, leftH, rightH, contH, leftU, rightU, contU,
          sameLeftHU, sameRightHU⟩

theorem ProdComponentHistoryClassifier_name_certificate
    {Left Right : BHist -> Prop} {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    (coherent : ProdPairRepCoherent Left Right LeftEq RightEq) :
    NameCert (ProdHistoryCarrier Left Right)
      (ProdComponentHistoryClassifier Left Right LeftEq RightEq) := by
  cases leftCert.carrier_inhabited with
  | intro leftHist leftCarrier =>
      cases rightCert.carrier_inhabited with
      | intro rightHist rightCarrier =>
          exact {
            carrier_inhabited := Exists.intro (append leftHist rightHist)
              (ProdHistoryCarrier_append_intro leftCarrier rightCarrier)
            equiv_refl := by
              intro h carrier
              exact
                ProdComponentHistoryClassifier_carrier_reflexivity_from_source_certificates
                  leftCert rightCert carrier
            equiv_symm := by
              intro h k classifier
              exact
                ProdComponentHistoryClassifier_symm_from_source_certificates
                  leftCert rightCert classifier
            equiv_trans := by
              intro h k u classifierHK classifierKU
              exact
                ProdComponentHistoryClassifier_trans_from_pair_coherence
                  leftCert rightCert coherent classifierHK classifierKU
            carrier_respects_equiv := by
              intro h k classifier _carrier
              exact (ProdComponentHistoryClassifier_endpoint_carriers classifier).right
          }

end BEDC.Derived.ProdUp
