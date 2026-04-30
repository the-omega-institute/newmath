import BEDC.FKernel.Cont

namespace BEDC.FKernel.Cont

open BEDC.FKernel.Hist

theorem cont_determinacy_up_to_hsame_spine {h k r r' : BHist} :
    Cont h k r -> Cont h k r' -> hsame r r' := by
  intro left right
  exact cont_deterministic left right

theorem cont_e0_result_witness {h k r : BHist} :
    Cont h (BHist.e0 k) r -> exists r0 : BHist, r = BHist.e0 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.left hcont

theorem cont_e1_result_witness {h k r : BHist} :
    Cont h (BHist.e1 k) r -> exists r0 : BHist, r = BHist.e1 r0 /\ Cont h k r0 := by
  intro hcont
  exact cont_step_result_inversions.right hcont

theorem cont_step_zero_iff {h k r : BHist} :
    Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r := by
  constructor
  · intro hcont
    exact cont_step_rules_inversion_pair.left hcont
  · intro hcont
    exact cont_step_zero hcont

theorem cont_step_one_iff {h k r : BHist} :
    Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r := by
  constructor
  · intro hcont
    exact cont_step_rules_inversion_pair.right hcont
  · intro hcont
    exact cont_step_one hcont

theorem cont_step_rules_iff_pair :
    (∀ {h k r : BHist}, Cont h (BHist.e0 k) (BHist.e0 r) ↔ Cont h k r) ∧
      (∀ {h k r : BHist}, Cont h (BHist.e1 k) (BHist.e1 r) ↔ Cont h k r) := by
  constructor
  · exact cont_step_zero_iff
  · exact cont_step_one_iff

theorem continuation_step_rules_iff_pair :
    (forall {h k r : BHist}, Cont h (BHist.e0 k) (BHist.e0 r) <-> Cont h k r) /\
      (forall {h k r : BHist}, Cont h (BHist.e1 k) (BHist.e1 r) <-> Cont h k r) := by
  exact cont_step_rules_iff_pair

theorem continuation_step_result_witness_iff_pair :
    (∀ {h k r : BHist},
        Cont h (BHist.e0 k) r ↔ ∃ r0 : BHist, r = BHist.e0 r0 ∧ Cont h k r0) ∧
      (∀ {h k r : BHist},
        Cont h (BHist.e1 k) r ↔ ∃ r0 : BHist, r = BHist.e1 r0 ∧ Cont h k r0) := by
  constructor
  · intro h k r
    constructor
    · intro hcont
      exact cont_step_result_inversions.left hcont
    · intro witness
      cases witness with
      | intro r0 packed =>
          cases packed with
          | intro result hcont =>
              cases result
              exact cont_step_zero hcont
  · intro h k r
    constructor
    · intro hcont
      exact cont_step_result_inversions.right hcont
    · intro witness
      cases witness with
      | intro r0 packed =>
          cases packed with
          | intro result hcont =>
              cases result
              exact cont_step_one hcont

theorem cont_step_result_witnesses_by_constructor :
    (∀ {h k r : BHist},
      Cont h (BHist.e0 k) r → ∃ r0 : BHist, r = BHist.e0 r0 ∧ Cont h k r0) ∧
      (∀ {h k r : BHist},
        Cont h (BHist.e1 k) r → ∃ r0 : BHist, r = BHist.e1 r0 ∧ Cont h k r0) := by
  constructor
  · intro h k r hcont
    exact cont_step_result_inversions.left hcont
  · intro h k r hcont
    exact cont_step_result_inversions.right hcont

theorem continuation_step_result_witnesses_pair {h k rz ro : BHist} :
    Cont h (BHist.e0 k) rz → Cont h (BHist.e1 k) ro →
      ∃ a : BHist, ∃ b : BHist,
        rz = BHist.e0 a ∧ Cont h k a ∧ ro = BHist.e1 b ∧ Cont h k b := by
  intro zeroStep oneStep
  cases cont_e0_result_witness zeroStep with
  | intro a zeroWitness =>
      cases zeroWitness with
      | intro zeroResult zeroCont =>
          cases cont_e1_result_witness oneStep with
          | intro b oneWitness =>
              cases oneWitness with
              | intro oneResult oneCont =>
                  exact Exists.intro a
                    (Exists.intro b
                      (And.intro zeroResult
                        (And.intro zeroCont (And.intro oneResult oneCont))))

theorem cont_step_result_no_confusion_pair :
    (forall {h k0 k1 r : BHist},
      Cont h (BHist.e0 k0) r -> Cont h (BHist.e1 k1) r -> False) /\
      (forall {h k0 k1 r : BHist},
        Cont h (BHist.e1 k0) r -> Cont h (BHist.e0 k1) r -> False) := by
  constructor
  · intro h k0 k1 r zeroStep oneStep
    cases cont_e0_result_witness zeroStep with
    | intro rz zeroWitness =>
        cases zeroWitness with
        | intro zeroResult _ =>
            cases zeroResult
            cases cont_e1_result_witness oneStep with
            | intro ro oneWitness =>
                cases oneWitness with
                | intro oneResult _ =>
                    cases oneResult
  · intro h k0 k1 r oneStep zeroStep
    cases cont_e1_result_witness oneStep with
    | intro ro oneWitness =>
        cases oneWitness with
        | intro oneResult _ =>
            cases oneResult
            cases cont_e0_result_witness zeroStep with
            | intro rz zeroWitness =>
                cases zeroWitness with
                | intro zeroResult _ =>
                    cases zeroResult

end BEDC.FKernel.Cont
