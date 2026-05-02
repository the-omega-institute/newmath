import BEDC.Derived.ContinuousUp

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousFunctionCarrier_prefixed_graph_chain_factorizes
    {p source map target delta1 delta2 delta cert : BHist} :
    UnaryHistory delta1 → UnaryHistory delta2 → Cont delta1 delta2 delta →
      ContinuousFunctionCarrier (append p source) map (append p target) delta
        (append p cert) →
        ∃ middle : BHist,
          ContinuousFunctionCarrier source map target delta cert ∧
            ContinuousModulusWitness target delta1 middle ∧
              ContinuousModulusWitness middle delta2 cert := by
  intro delta1Carrier delta2Carrier compositeRel prefixedCarrier
  have carrier := (ContinuousFunctionCarrier_prefix_iff.mp prefixedCarrier).right
  cases carrier with
  | intro sourceCarrier carrierRest =>
      cases carrierRest with
      | intro targetCarrier carrierRest =>
          cases carrierRest with
          | intro mapCarrier carrierRest =>
              cases carrierRest with
              | intro deltaCarrier carrierRest =>
                  cases carrierRest with
                  | intro sourceMap targetDelta =>
                      let middle := append target delta1
                      have middleCarrier : UnaryHistory middle :=
                        unary_append_closed targetCarrier delta1Carrier
                      have firstWitness : ContinuousModulusWitness target delta1 middle :=
                        And.intro targetCarrier
                          (And.intro delta1Carrier
                            (And.intro middleCarrier (cont_intro rfl)))
                      have secondRel : Cont middle delta2 cert := by
                        cases targetDelta
                        cases compositeRel
                        exact cont_intro (append_assoc target delta1 delta2).symm
                      have secondWitness : ContinuousModulusWitness middle delta2 cert :=
                        And.intro middleCarrier
                          (And.intro delta2Carrier
                            (And.intro
                              (unary_cont_closed targetCarrier deltaCarrier targetDelta)
                              secondRel))
                      exact Exists.intro middle
                        (And.intro
                          (And.intro sourceCarrier
                            (And.intro targetCarrier
                              (And.intro mapCarrier
                                (And.intro deltaCarrier
                                  (And.intro sourceMap targetDelta)))))
                          (And.intro firstWitness secondWitness))

theorem ContinuousFunctionCarrier_prefixed_graph_chain_factorization
    {p source map target delta1 delta2 delta cert : BHist} :
    UnaryHistory delta1 -> UnaryHistory delta2 -> Cont delta1 delta2 delta ->
      ContinuousFunctionCarrier (append p source) map (append p target) delta
          (append p cert) ->
        exists middle : BHist,
          ContinuousFunctionCarrier source map target delta1 middle ∧
            ContinuousModulusWitness middle delta2 cert := by
  intro delta1Carrier delta2Carrier compositeRel prefixedCarrier
  have carrier := (ContinuousFunctionCarrier_prefix_iff.mp prefixedCarrier).right
  cases carrier with
  | intro sourceCarrier carrierRest =>
      cases carrierRest with
      | intro targetCarrier carrierRest =>
          cases carrierRest with
          | intro mapCarrier carrierRest =>
              cases carrierRest with
              | intro _deltaCarrier carrierRest =>
                  cases carrierRest with
                  | intro sourceMap targetDelta =>
                      let middle := append target delta1
                      have middleCarrier : UnaryHistory middle :=
                        unary_append_closed targetCarrier delta1Carrier
                      have certCarrier : UnaryHistory cert :=
                        unary_cont_closed targetCarrier
                          (unary_cont_closed delta1Carrier delta2Carrier compositeRel) targetDelta
                      have firstCarrier :
                          ContinuousFunctionCarrier source map target delta1 middle :=
                        And.intro sourceCarrier
                          (And.intro targetCarrier
                            (And.intro mapCarrier
                              (And.intro delta1Carrier
                                (And.intro sourceMap (cont_intro rfl)))))
                      have secondRel : Cont middle delta2 cert := by
                        cases targetDelta
                        cases compositeRel
                        exact cont_intro (append_assoc target delta1 delta2).symm
                      have secondWitness : ContinuousModulusWitness middle delta2 cert :=
                        And.intro middleCarrier
                          (And.intro delta2Carrier (And.intro certCarrier secondRel))
                      exact Exists.intro middle (And.intro firstCarrier secondWitness)

end BEDC.Derived.ContinuousUp
