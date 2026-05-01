import BEDC.FKernel.Unary
import BEDC.FKernel.Cont

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def ContinuousModulusWitness (source modulus target : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory target ∧ Cont source modulus target

def ContinuousModulusChain (source first second target : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory first ∧ UnaryHistory second ∧ UnaryHistory target ∧
    ∃ middle : BHist, Cont source first middle ∧ Cont middle second target

theorem ContinuousModulusChain_factorizes {source first second target : BHist} :
    ContinuousModulusChain source first second target ->
      ∃ middle : BHist,
        ContinuousModulusWitness source first middle ∧
          ContinuousModulusWitness middle second target := by
  intro chain
  cases chain with
  | intro sourceCarrier rest =>
      cases rest with
      | intro firstCarrier rest =>
          cases rest with
          | intro secondCarrier rest =>
              cases rest with
              | intro targetCarrier chainWitness =>
                  cases chainWitness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          have middleCarrier : UnaryHistory middle :=
                            unary_cont_closed sourceCarrier firstCarrier firstRel
                          exact
                            Exists.intro middle
                              (And.intro
                                (And.intro sourceCarrier
                                  (And.intro firstCarrier
                                    (And.intro middleCarrier firstRel)))
                                (And.intro middleCarrier
                                  (And.intro secondCarrier
                                    (And.intro targetCarrier secondRel))))

theorem ContinuousModulusChain_composite_closed {source first second target composite : BHist} :
    ContinuousModulusChain source first second target -> Cont first second composite ->
      ContinuousModulusWitness source composite target := by
  intro chain compositeRel
  cases chain with
  | intro sourceCarrier rest =>
      cases rest with
      | intro firstCarrier rest =>
          cases rest with
          | intro secondCarrier rest =>
              cases rest with
              | intro targetCarrier chainWitness =>
                  cases chainWitness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          cases firstRel
                          cases secondRel
                          cases compositeRel
                          exact
                            And.intro sourceCarrier
                              (And.intro
                                (unary_cont_closed firstCarrier secondCarrier (cont_intro rfl))
                                (And.intro targetCarrier
                                  (cont_intro (append_assoc source first second))))

def ContinuousFunctionCarrier (source map target modulus cert : BHist) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory map ∧ UnaryHistory modulus ∧
    Cont source map target ∧ Cont target modulus cert

theorem ContinuousFunctionCarrier_comp_closed
    {source middle target f g fg modF modG modFG certF certG cert : BHist} :
    ContinuousFunctionCarrier source f middle modF certF ->
      ContinuousFunctionCarrier middle g target modG certG ->
        Cont f g fg -> Cont modF modG modFG -> Cont target modFG cert ->
          ContinuousFunctionCarrier source fg target modFG cert := by
  intro first second fgRel modRel certRel
  cases first with
  | intro sourceCarrier firstRest =>
      cases firstRest with
      | intro _middleCarrier firstRest =>
          cases firstRest with
          | intro fCarrier firstRest =>
              cases firstRest with
              | intro modFCarrier firstRest =>
                  cases firstRest with
                  | intro sourceMap _certFRel =>
                      cases second with
                      | intro _middleCarrier' secondRest =>
                          cases secondRest with
                          | intro targetCarrier secondRest =>
                              cases secondRest with
                              | intro gCarrier secondRest =>
                                  cases secondRest with
                                  | intro modGCarrier secondRest =>
                                      cases secondRest with
                                      | intro middleMap _certGRel =>
                                          have fgCarrier : UnaryHistory fg :=
                                            unary_cont_closed fCarrier gCarrier fgRel
                                          have modFGCarrier : UnaryHistory modFG :=
                                            unary_cont_closed modFCarrier modGCarrier modRel
                                          have sourceTarget : Cont source fg target := by
                                            cases sourceMap
                                            cases middleMap
                                            cases fgRel
                                            exact cont_intro (append_assoc source f g)
                                          exact
                                            And.intro sourceCarrier
                                              (And.intro targetCarrier
                                                (And.intro fgCarrier
                                                  (And.intro modFGCarrier
                                                    (And.intro sourceTarget certRel))))

theorem ContinuousFunctionCarrier_modulus_chain_replacement
    {source map target oldMod oldCert delta1 delta2 delta cert : BHist} :
    ContinuousFunctionCarrier source map target oldMod oldCert ->
      ContinuousModulusChain target delta1 delta2 cert -> Cont delta1 delta2 delta ->
        ContinuousFunctionCarrier source map target delta cert := by
  intro carrier chain compositeRel
  have replacementWitness : ContinuousModulusWitness target delta cert :=
    ContinuousModulusChain_composite_closed chain compositeRel
  cases carrier with
  | intro sourceCarrier carrierRest =>
      cases carrierRest with
      | intro targetCarrier carrierRest =>
          cases carrierRest with
          | intro mapCarrier carrierRest =>
              cases carrierRest with
              | intro _oldModCarrier carrierRest =>
                  cases carrierRest with
                  | intro sourceMap _oldCertRel =>
                      cases replacementWitness with
                      | intro _targetCarrier witnessRest =>
                          cases witnessRest with
                          | intro deltaCarrier witnessRest =>
                              cases witnessRest with
                              | intro _certCarrier targetDelta =>
                                  exact
                                    And.intro sourceCarrier
                                      (And.intro targetCarrier
                                        (And.intro mapCarrier
                                          (And.intro deltaCarrier
                                            (And.intro sourceMap targetDelta))))

theorem ContinuousFunctionCarrier_prefix_closed
    {p source map targetHist modulus certHist : BHist} :
    UnaryHistory p -> ContinuousFunctionCarrier source map targetHist modulus certHist ->
      ContinuousFunctionCarrier (append p source) map (append p targetHist) modulus
        (append p certHist) := by
  intro prefixCarrier carrier
  cases carrier with
  | intro sourceCarrier rest =>
      cases rest with
      | intro targetCarrier rest =>
          cases rest with
          | intro mapCarrier rest =>
              cases rest with
              | intro modulusCarrier rest =>
                  cases rest with
                  | intro sourceMap targetCert =>
                      exact
                        And.intro (unary_append_closed prefixCarrier sourceCarrier)
                          (And.intro (unary_append_closed prefixCarrier targetCarrier)
                            (And.intro mapCarrier
                              (And.intro modulusCarrier
                                (And.intro
                                  (cont_intro
                                    ((congrArg (append p) sourceMap).trans
                                      (append_assoc p source map).symm))
                                  (cont_intro
                                    ((congrArg (append p) targetCert).trans
                                      (append_assoc p targetHist modulus).symm))))))

theorem ContinuousFunctionCarrier_prefix_iff {p source map target modulus cert : BHist} :
    ContinuousFunctionCarrier (append p source) map (append p target) modulus
        (append p cert) ↔
      UnaryHistory p ∧ ContinuousFunctionCarrier source map target modulus cert := by
  constructor
  · intro prefixed
    cases prefixed with
    | intro prefixedSource rest =>
        cases rest with
        | intro prefixedTarget rest =>
            cases rest with
            | intro mapCarrier rest =>
                cases rest with
                | intro modulusCarrier rest =>
                    cases rest with
                    | intro sourceMap targetCert =>
                        exact
                          And.intro (unary_append_left_factor prefixedSource)
                            (And.intro (unary_append_right_factor prefixedSource)
                              (And.intro (unary_append_right_factor prefixedTarget)
                                (And.intro mapCarrier
                                  (And.intro modulusCarrier
                                    (And.intro (cont_prefix_cancel sourceMap)
                                      (cont_prefix_cancel targetCert))))))
  · intro base
    cases base with
    | intro prefixCarrier carrier =>
        exact ContinuousFunctionCarrier_prefix_closed prefixCarrier carrier

theorem ContinuousModulusChain_prefix_closed {p source first second target : BHist} :
    UnaryHistory p -> ContinuousModulusChain source first second target ->
      ContinuousModulusChain (append p source) first second (append p target) := by
  intro prefixCarrier chain
  cases chain with
  | intro sourceCarrier rest =>
      cases rest with
      | intro firstCarrier rest =>
          cases rest with
          | intro secondCarrier rest =>
              cases rest with
              | intro targetCarrier chainWitness =>
                  cases chainWitness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          exact
                            And.intro (unary_append_closed prefixCarrier sourceCarrier)
                              (And.intro firstCarrier
                                (And.intro secondCarrier
                                  (And.intro (unary_append_closed prefixCarrier targetCarrier)
                                    (Exists.intro (append p middle)
                                      (And.intro
                                        (cont_intro
                                          ((congrArg (append p) firstRel).trans
                                            (append_assoc p source first).symm))
                                        (cont_intro
                                          ((congrArg (append p) secondRel).trans
                                            (append_assoc p middle second).symm)))))))

theorem ContinuousModulusChain_prefix_iff {p source first second target : BHist} :
    ContinuousModulusChain (append p source) first second (append p target) ↔
      UnaryHistory p ∧ ContinuousModulusChain source first second target := by
  constructor
  · intro prefixed
    cases prefixed with
    | intro prefixedSource rest =>
        cases rest with
        | intro firstCarrier rest =>
            cases rest with
            | intro secondCarrier rest =>
                cases rest with
                | intro prefixedTarget chainWitness =>
                    cases chainWitness with
                    | intro middle middleData =>
                        cases middleData with
                        | intro firstRel secondRel =>
                            let baseMiddle := append source first
                            have middlePrefixed :
                                hsame middle (append p baseMiddle) := by
                              exact firstRel.trans (append_assoc p source first)
                            have prefixedSecond :
                                hsame (append p target) (append p (append baseMiddle second)) := by
                              exact
                                secondRel.trans
                                  ((congrArg (fun result => append result second)
                                      middlePrefixed).trans
                                    (append_assoc p baseMiddle second))
                            have baseSecond : Cont baseMiddle second target := by
                              apply cont_intro
                              exact append_left_cancel (h := p) prefixedSecond
                            exact
                              And.intro (unary_append_left_factor prefixedSource)
                                (And.intro (unary_append_right_factor prefixedSource)
                                  (And.intro firstCarrier
                                    (And.intro secondCarrier
                                      (And.intro (unary_append_right_factor prefixedTarget)
                                        (Exists.intro baseMiddle
                                          (And.intro (cont_intro rfl) baseSecond))))))
  · intro base
    cases base with
    | intro prefixCarrier chain =>
        exact ContinuousModulusChain_prefix_closed prefixCarrier chain

theorem ContinuousModulusWitness_prefixed_composite_closed
    {p source first second target composite : BHist} :
    UnaryHistory p -> ContinuousModulusChain source first second target ->
      Cont first second composite ->
        ContinuousModulusWitness (append p source) composite (append p target) := by
  intro prefixCarrier chain compositeRel
  exact
    ContinuousModulusChain_composite_closed
      (ContinuousModulusChain_prefix_closed prefixCarrier chain) compositeRel

theorem ContinuousFunctionCarrier_prefixed_graph_chain_closed
    {p source map target delta1 delta2 delta cert : BHist} :
    UnaryHistory p -> UnaryHistory source -> UnaryHistory target -> UnaryHistory map ->
      Cont source map target -> ContinuousModulusChain target delta1 delta2 cert ->
        Cont delta1 delta2 delta ->
          ContinuousFunctionCarrier (append p source) map (append p target) delta
            (append p cert) := by
  intro prefixCarrier sourceCarrier _targetCarrier mapCarrier graphRel chain compositeRel
  have replacementWitness :
      ContinuousModulusWitness (append p target) delta (append p cert) :=
    ContinuousModulusWitness_prefixed_composite_closed prefixCarrier chain compositeRel
  cases replacementWitness with
  | intro prefixedTargetCarrier witnessRest =>
      cases witnessRest with
      | intro deltaCarrier witnessRest =>
          cases witnessRest with
          | intro _prefixedCertCarrier targetDelta =>
              exact
                And.intro (unary_append_closed prefixCarrier sourceCarrier)
                  (And.intro prefixedTargetCarrier
                    (And.intro mapCarrier
                      (And.intro deltaCarrier
                        (And.intro
                          (cont_intro
                            ((congrArg (append p) graphRel).trans
                              (append_assoc p source map).symm))
                          targetDelta))))

end BEDC.Derived.ContinuousUp
