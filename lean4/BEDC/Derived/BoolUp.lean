import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BoolUp

abbrev BoolCarrier : Type := BEDC.FKernel.Mark.BMark

def BoolClassifierSpec : BoolCarrier → BoolCarrier → Prop :=
  BEDC.FKernel.Mark.msame

def BoolSourceSpec (value : BEDC.FKernel.Mark.BMark) : Prop :=
  BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b0 ∨
    BEDC.FKernel.Mark.msame value BEDC.FKernel.Mark.BMark.b1

def BoolPatternSpec : Prop :=
  BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b0 ∧
    BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b1 ∧
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 →
        False) ∧
        (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b0 →
          False)

theorem BoolSourceSpec_msame_transport {v w : BEDC.FKernel.Mark.BMark} :
    BEDC.FKernel.Mark.msame v w → BoolSourceSpec v → BoolSourceSpec w := by
  intro same src
  cases same
  exact src

def BoolLedgerPolicy
    (source visible : BEDC.FKernel.Mark.BMark) : Prop :=
  BEDC.Derived.BoolUp.BoolSourceSpec source ∧
    BEDC.FKernel.Mark.msame source visible

theorem BoolClassifierSpec_constructor_separation :
    BoolClassifierSpec BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 → False := by
  exact BEDC.FKernel.Mark.not_msame_b0_b1

theorem bool_stability_certificate_fields :
    (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b0 ∧
        BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b1) ∧
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 →
        False) ∧
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b0 →
        False) ∧
      (∀ v : BEDC.FKernel.Mark.BMark, BoolSourceSpec v) := by
  constructor
  · constructor
    · rfl
    · rfl
  · constructor
    · intro h
      cases h
    · constructor
      · intro h
        cases h
      · intro v
        cases v with
        | b0 =>
            exact Or.inl rfl
        | b1 =>
            exact Or.inr rfl

theorem boolClassifierSpec_stability :
    BoolClassifierSpec BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b0 /\
      BoolClassifierSpec BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b1 /\
        (BoolClassifierSpec BEDC.FKernel.Mark.BMark.b0 BEDC.FKernel.Mark.BMark.b1 ->
          False) /\
          (BoolClassifierSpec BEDC.FKernel.Mark.BMark.b1 BEDC.FKernel.Mark.BMark.b0 ->
            False) := by
  constructor
  · exact BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0
  · constructor
    · exact BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1
    · constructor
      · exact BEDC.FKernel.Mark.not_msame_b0_b1
      · exact BEDC.FKernel.Mark.not_msame_b1_b0

theorem bool_stability_certificate :
    BoolSourceSpec BEDC.FKernel.Mark.BMark.b0 /\
      BoolSourceSpec BEDC.FKernel.Mark.BMark.b1 /\
      (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b0
          BEDC.FKernel.Mark.BMark.b1 -> False) /\
        (BEDC.FKernel.Mark.msame BEDC.FKernel.Mark.BMark.b1
          BEDC.FKernel.Mark.BMark.b0 -> False) := by
  constructor
  · exact Or.inl rfl
  · constructor
    · exact Or.inr rfl
    · exact BEDC.FKernel.Mark.mark_no_confusion

theorem BoolSourceSpec_respects_msame {v w : BEDC.FKernel.Mark.BMark} :
    BoolSourceSpec v -> BEDC.FKernel.Mark.msame v w -> BoolSourceSpec w := by
  intro hv hvw
  cases hv with
  | inl hv0 =>
      exact Or.inl
        (BEDC.FKernel.Mark.msame_trans (BEDC.FKernel.Mark.msame_symm hvw) hv0)
  | inr hv1 =>
      exact Or.inr
        (BEDC.FKernel.Mark.msame_trans (BEDC.FKernel.Mark.msame_symm hvw) hv1)

def BoolHistoryCarrier (h : BEDC.FKernel.Hist.BHist) : Prop :=
  BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty \/
    BEDC.FKernel.Hist.hsame h
      (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty)

theorem BoolHistoryCarrier_e0_absurd {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e0 h) -> False := by
  intro carrier
  cases carrier with
  | inl emptyCase =>
      exact BEDC.FKernel.Hist.not_hsame_e0_empty emptyCase
  | inr oneCase =>
      exact BEDC.FKernel.Hist.not_hsame_e0_e1 oneCase

def BoolHistoryClassifier
    (h k : BEDC.FKernel.Hist.BHist) : Prop :=
  BoolHistoryCarrier h /\
    BoolHistoryCarrier k /\
      BEDC.FKernel.Hist.hsame h k

theorem BoolHistoryClassifier_constructor_separation :
    BoolHistoryClassifier BEDC.FKernel.Hist.BHist.Empty
      (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) -> False := by
  intro classifier
  cases classifier with
  | intro _ rest =>
      cases rest with
      | intro _ same =>
          exact BEDC.FKernel.Hist.not_hsame_emp_e1 same

theorem BoolHistoryClassifier_trans {h k r : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k -> BoolHistoryClassifier k r -> BoolHistoryClassifier h r := by
  intro sameHK sameKR
  cases sameHK with
  | intro carrierH restHK =>
      cases restHK with
      | intro _ histHK =>
          cases sameKR with
          | intro _ restKR =>
              cases restKR with
              | intro carrierR histKR =>
                  constructor
                  · exact carrierH
                  · constructor
                    · exact carrierR
                    · exact BEDC.FKernel.Hist.hsame_trans histHK histKR

theorem BoolHistoryCarrier_hsame_transport {h k : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h k -> BoolHistoryCarrier h -> BoolHistoryCarrier k := by
  intro same carrier
  cases carrier with
  | inl emptyCase =>
      exact Or.inl
        (BEDC.FKernel.Hist.hsame_trans (BEDC.FKernel.Hist.hsame_symm same) emptyCase)
  | inr oneCase =>
      exact Or.inr
        (BEDC.FKernel.Hist.hsame_trans (BEDC.FKernel.Hist.hsame_symm same) oneCase)

theorem BoolHistoryClassifier_cases {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k ->
      (BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty ∧
          BEDC.FKernel.Hist.hsame k BEDC.FKernel.Hist.BHist.Empty) ∨
        (BEDC.FKernel.Hist.hsame h
            (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) ∧
          BEDC.FKernel.Hist.hsame k
            (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty)) := by
  intro classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro _ sameHK =>
          cases carrierH with
          | inl emptyH =>
              exact Or.inl
                ⟨emptyH,
                  BEDC.FKernel.Hist.hsame_trans
                    (BEDC.FKernel.Hist.hsame_symm sameHK) emptyH⟩
          | inr oneH =>
              exact Or.inr
                ⟨oneH,
                  BEDC.FKernel.Hist.hsame_trans
                    (BEDC.FKernel.Hist.hsame_symm sameHK) oneH⟩

theorem bool_history_name_certificate :
    BEDC.FKernel.NameCert.NameCert BoolHistoryCarrier BoolHistoryClassifier := by
  exact {
    carrier_inhabited :=
      Exists.intro BEDC.FKernel.Hist.BHist.Empty
        (Or.inl (BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty))
    equiv_refl := by
      intro h carrier
      constructor
      · exact carrier
      · constructor
        · exact carrier
        · exact BEDC.FKernel.Hist.hsame_refl h
    equiv_symm := by
      intro h k same
      cases same with
      | intro carrierH rest =>
          cases rest with
          | intro carrierK histSame =>
              constructor
              · exact carrierK
              · constructor
                · exact carrierH
                · exact BEDC.FKernel.Hist.hsame_symm histSame
    equiv_trans := by
      intro h k r sameHK sameKR
      cases sameHK with
      | intro carrierH restHK =>
          cases restHK with
          | intro _ histHK =>
              cases sameKR with
              | intro _ restKR =>
                  cases restKR with
                  | intro carrierR histKR =>
                      constructor
                      · exact carrierH
                      · constructor
                        · exact carrierR
                        · exact BEDC.FKernel.Hist.hsame_trans histHK histKR
    carrier_respects_equiv := by
      intro h k same _
      cases same with
      | intro _ rest =>
          cases rest with
          | intro carrierK _ =>
              exact carrierK
  }

end BEDC.Derived.BoolUp
