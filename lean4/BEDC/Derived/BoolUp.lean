import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

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

def BoolEndpoint : BEDC.FKernel.Mark.BMark → BEDC.FKernel.Hist.BHist
  | BEDC.FKernel.Mark.BMark.b0 => BEDC.FKernel.Hist.BHist.Empty
  | BEDC.FKernel.Mark.BMark.b1 =>
      BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty

theorem BoolEndpoint_bridge_exactness {v w : BEDC.FKernel.Mark.BMark} :
    BEDC.FKernel.Mark.msame v w ↔
      BEDC.FKernel.Hist.hsame (BoolEndpoint v) (BoolEndpoint w) := by
  cases v with
  | b0 =>
      cases w with
      | b0 =>
          constructor
          · intro _
            exact BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty
          · intro _
            exact BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0
      | b1 =>
          constructor
          · intro same
            exact False.elim (BEDC.FKernel.Mark.not_msame_b0_b1 same)
          · intro same
            exact False.elim (BEDC.FKernel.Hist.not_hsame_emp_e1 same)
  | b1 =>
      cases w with
      | b0 =>
          constructor
          · intro same
            exact False.elim (BEDC.FKernel.Mark.not_msame_b1_b0 same)
          · intro same
            exact False.elim (BEDC.FKernel.Hist.not_hsame_e1_empty same)
      | b1 =>
          constructor
          · intro _
            exact BEDC.FKernel.Hist.hsame_refl
              (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty)
          · intro _
            exact BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1

theorem BoolEndpoint_readback_deterministic {v w : BEDC.FKernel.Mark.BMark}
    {h : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h (BoolEndpoint v) →
      BEDC.FKernel.Hist.hsame h (BoolEndpoint w) →
        BEDC.FKernel.Mark.msame v w := by
  intro sameV sameW
  exact BoolEndpoint_bridge_exactness.mpr
    (BEDC.FKernel.Hist.hsame_trans (BEDC.FKernel.Hist.hsame_symm sameV) sameW)

theorem BoolHistoryCarrier_endpoint_coverage {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier h ↔
      ∃ v : BEDC.FKernel.Mark.BMark,
        BEDC.FKernel.Hist.hsame h (BoolEndpoint v) := by
  constructor
  · intro carrier
    cases carrier with
    | inl emptyCase =>
        exact Exists.intro BEDC.FKernel.Mark.BMark.b0 emptyCase
    | inr oneCase =>
        exact Exists.intro BEDC.FKernel.Mark.BMark.b1 oneCase
  · intro witness
    cases witness with
    | intro v same =>
        cases v with
        | b0 =>
            exact Or.inl same
        | b1 =>
            exact Or.inr same

theorem BoolEndpoint_readback_determinism {v w : BEDC.FKernel.Mark.BMark}
    {h : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h (BoolEndpoint v) ->
      BEDC.FKernel.Hist.hsame h (BoolEndpoint w) ->
        BEDC.FKernel.Mark.msame v w := by
  intro readV readW
  exact (BoolEndpoint_bridge_exactness (v := v) (w := w)).mpr
    (BEDC.FKernel.Hist.hsame_trans
      (BEDC.FKernel.Hist.hsame_symm readV)
      readW)

theorem BoolEndpoint_readback_total_unique {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier h →
      ∃ v : BEDC.FKernel.Mark.BMark,
        BEDC.FKernel.Hist.hsame h (BoolEndpoint v) ∧
          BoolSourceSpec v ∧
            ∀ w : BEDC.FKernel.Mark.BMark,
              BEDC.FKernel.Hist.hsame h (BoolEndpoint w) →
                BEDC.FKernel.Mark.msame v w := by
  intro carrier
  cases (BoolHistoryCarrier_endpoint_coverage (h := h)).mp carrier with
  | intro v sameEndpoint =>
      exact Exists.intro v
        (And.intro sameEndpoint
          (And.intro
            (by
              cases v with
              | b0 =>
                  exact Or.inl
                    (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0)
              | b1 =>
                  exact Or.inr
                    (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1))
            (by
              intro w sameOther
              exact BoolEndpoint_readback_determinism (v := v) (w := w)
                (h := h) sameEndpoint sameOther)))

theorem BoolHistoryCarrier_e0_absurd {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e0 h) -> False := by
  intro carrier
  cases carrier with
  | inl emptyCase =>
      exact BEDC.FKernel.Hist.not_hsame_e0_empty emptyCase
  | inr oneCase =>
      exact BEDC.FKernel.Hist.not_hsame_e0_e1 oneCase

theorem BoolHistoryCarrier_e1_tail_empty {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e1 h) ->
      BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty := by
  intro carrier
  cases carrier with
  | inl emptyCase =>
      exact False.elim (BEDC.FKernel.Hist.not_hsame_e1_empty emptyCase)
  | inr oneCase =>
      exact BEDC.FKernel.Hist.hsame_e1_iff.mp oneCase

theorem BoolHistoryCarrier_e1_e1_absurd {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e1 (BEDC.FKernel.Hist.BHist.e1 h)) ->
      False := by
  intro carrier
  exact BEDC.FKernel.Hist.not_hsame_e1_empty
    (BoolHistoryCarrier_e1_tail_empty carrier)

theorem BoolHistoryCarrier_e1_iff_tail_empty {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier (BEDC.FKernel.Hist.BHist.e1 h) ↔
      BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty := by
  constructor
  · exact BoolHistoryCarrier_e1_tail_empty
  · intro tailEmpty
    exact Or.inr (BEDC.FKernel.Hist.hsame_e1_congr tailEmpty)

def BoolHistoryClassifier
    (h k : BEDC.FKernel.Hist.BHist) : Prop :=
  BoolHistoryCarrier h /\
    BoolHistoryCarrier k /\
      BEDC.FKernel.Hist.hsame h k

theorem BoolHistoryClassifier_e0_endpoint_absurd_pair :
    (∀ {h k : BEDC.FKernel.Hist.BHist},
        BoolHistoryClassifier (BEDC.FKernel.Hist.BHist.e0 h) k → False) ∧
      (∀ {h k : BEDC.FKernel.Hist.BHist},
        BoolHistoryClassifier h (BEDC.FKernel.Hist.BHist.e0 k) → False) := by
  constructor
  · intro h k classifier
    cases classifier with
    | intro carrierLeft _ =>
        exact BoolHistoryCarrier_e0_absurd carrierLeft
  · intro h k classifier
    cases classifier with
    | intro _ rest =>
        cases rest with
        | intro carrierRight _ =>
            exact BoolHistoryCarrier_e0_absurd carrierRight

theorem BoolHistoryClassifier_e1_tail_hsame {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier (BEDC.FKernel.Hist.BHist.e1 h)
      (BEDC.FKernel.Hist.BHist.e1 k) ->
      BEDC.FKernel.Hist.hsame h k := by
  intro classifier
  cases classifier with
  | intro _ rest =>
      cases rest with
      | intro _ same =>
          exact BEDC.FKernel.Hist.hsame_e1_iff.mp same

theorem BoolHistoryClassifier_e1_iff_tails_empty {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier (BEDC.FKernel.Hist.BHist.e1 h)
      (BEDC.FKernel.Hist.BHist.e1 k) <->
      BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty /\
        BEDC.FKernel.Hist.hsame k BEDC.FKernel.Hist.BHist.Empty := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK _same =>
            exact And.intro (BoolHistoryCarrier_e1_tail_empty carrierH)
              (BoolHistoryCarrier_e1_tail_empty carrierK)
  · intro tails
    cases tails with
    | intro tailH tailK =>
        constructor
        · exact (BoolHistoryCarrier_e1_iff_tail_empty (h := h)).mpr tailH
        · constructor
          · exact (BoolHistoryCarrier_e1_iff_tail_empty (h := k)).mpr tailK
          · exact BEDC.FKernel.Hist.hsame_e1_congr
              (BEDC.FKernel.Hist.hsame_trans tailH
                (BEDC.FKernel.Hist.hsame_symm tailK))

theorem BoolHistoryClassifier_e1_left_iff {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier (BEDC.FKernel.Hist.BHist.e1 h) k ↔
      BEDC.FKernel.Hist.hsame h BEDC.FKernel.Hist.BHist.Empty ∧
        BEDC.FKernel.Hist.hsame k
          (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty) := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierLeft rest =>
        cases rest with
        | intro _carrierRight sameLeftRight =>
            have tailEmpty := BoolHistoryCarrier_e1_tail_empty carrierLeft
            constructor
            · exact tailEmpty
            · exact BEDC.FKernel.Hist.hsame_trans
                (BEDC.FKernel.Hist.hsame_symm sameLeftRight)
                (BEDC.FKernel.Hist.hsame_e1_congr tailEmpty)
  · intro endpoints
    cases endpoints with
    | intro tailEmpty sameRight =>
        constructor
        · exact BoolHistoryCarrier_e1_iff_tail_empty.mpr tailEmpty
        · constructor
          · exact Or.inr sameRight
          · exact BEDC.FKernel.Hist.hsame_trans
              (BEDC.FKernel.Hist.hsame_e1_congr tailEmpty)
              (BEDC.FKernel.Hist.hsame_symm sameRight)

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

theorem BoolHistoryClassifier_symm {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k -> BoolHistoryClassifier k h := by
  intro classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          constructor
          · exact carrierK
          · constructor
            · exact carrierH
            · exact BEDC.FKernel.Hist.hsame_symm sameHK

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

theorem BoolHistoryClassifier_hsame_transport {h h' k k' : BEDC.FKernel.Hist.BHist} :
    BEDC.FKernel.Hist.hsame h h' -> BEDC.FKernel.Hist.hsame k k' ->
      BoolHistoryClassifier h k -> BoolHistoryClassifier h' k' := by
  intro sameH sameK classifier
  cases classifier with
  | intro carrierH rest =>
      cases rest with
      | intro carrierK sameHK =>
          constructor
          · exact BoolHistoryCarrier_hsame_transport sameH carrierH
          · constructor
            · exact BoolHistoryCarrier_hsame_transport sameK carrierK
            · exact BEDC.FKernel.Hist.hsame_trans
                (BEDC.FKernel.Hist.hsame_symm sameH)
                (BEDC.FKernel.Hist.hsame_trans sameHK sameK)

theorem BoolHistoryClassifier_empty_left_iff {k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier BEDC.FKernel.Hist.BHist.Empty k <->
      BEDC.FKernel.Hist.hsame k BEDC.FKernel.Hist.BHist.Empty := by
  constructor
  · intro classifier
    cases classifier with
    | intro _ rest =>
        cases rest with
        | intro _ same =>
            exact BEDC.FKernel.Hist.hsame_symm same
  · intro same
    constructor
    · exact Or.inl
        (BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty)
    · constructor
      · exact Or.inl same
      · exact BEDC.FKernel.Hist.hsame_symm same

theorem BoolHistoryCarrier_unary {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier h -> BEDC.FKernel.Unary.UnaryHistory h := by
  intro carrier
  cases carrier with
  | inl emptyCase =>
      exact BEDC.FKernel.Unary.unary_transport BEDC.FKernel.Unary.unary_empty
        (BEDC.FKernel.Hist.hsame_symm emptyCase)
  | inr oneCase =>
      exact BEDC.FKernel.Unary.unary_transport
        (BEDC.FKernel.Unary.unary_e1_closed BEDC.FKernel.Unary.unary_empty)
        (BEDC.FKernel.Hist.hsame_symm oneCase)

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

theorem BoolHistoryClassifier_mark_readback_exactness {h k : BEDC.FKernel.Hist.BHist} :
    BoolHistoryClassifier h k <->
      exists v : BEDC.FKernel.Mark.BMark, exists w : BEDC.FKernel.Mark.BMark,
        BEDC.FKernel.Hist.hsame h (BoolEndpoint v) /\
          BEDC.FKernel.Hist.hsame k (BoolEndpoint w) /\
            BEDC.FKernel.Mark.msame v w := by
  constructor
  · intro classifier
    cases classifier with
    | intro carrierH rest =>
        cases rest with
        | intro carrierK sameHK =>
            cases (BoolHistoryCarrier_endpoint_coverage (h := h)).mp carrierH with
            | intro v readH =>
                cases (BoolHistoryCarrier_endpoint_coverage (h := k)).mp carrierK with
                | intro w readK =>
                    have endpointSame :
                        BEDC.FKernel.Hist.hsame (BoolEndpoint v) (BoolEndpoint w) :=
                      BEDC.FKernel.Hist.hsame_trans
                        (BEDC.FKernel.Hist.hsame_symm readH)
                        (BEDC.FKernel.Hist.hsame_trans sameHK readK)
                    exact Exists.intro v
                      (Exists.intro w
                        ⟨readH, readK,
                          (BoolEndpoint_bridge_exactness (v := v) (w := w)).mpr
                            endpointSame⟩)
  · intro witness
    cases witness with
    | intro v rest =>
        cases rest with
        | intro w payload =>
            cases payload with
            | intro readH restPayload =>
                cases restPayload with
                | intro readK sameVW =>
                    constructor
                    · exact (BoolHistoryCarrier_endpoint_coverage (h := h)).mpr
                        (Exists.intro v readH)
                    · constructor
                      · exact (BoolHistoryCarrier_endpoint_coverage (h := k)).mpr
                          (Exists.intro w readK)
                      · exact BEDC.FKernel.Hist.hsame_trans readH
                          (BEDC.FKernel.Hist.hsame_trans
                            ((BoolEndpoint_bridge_exactness (v := v) (w := w)).mp sameVW)
                            (BEDC.FKernel.Hist.hsame_symm readK))

theorem BoolHistoryCarrier_classifier_endpoint_exactness
    {h : BEDC.FKernel.Hist.BHist} :
    BoolHistoryCarrier h <->
      exists v : BEDC.FKernel.Mark.BMark,
        BoolSourceSpec v /\ BoolHistoryClassifier h (BoolEndpoint v) := by
  constructor
  · intro carrier
    cases (BoolHistoryCarrier_endpoint_coverage (h := h)).mp carrier with
    | intro v sameEndpoint =>
        have source : BoolSourceSpec v := by
          cases v with
          | b0 =>
              exact Or.inl (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b0)
          | b1 =>
              exact Or.inr (BEDC.FKernel.Mark.msame_refl BEDC.FKernel.Mark.BMark.b1)
        have endpointCarrier : BoolHistoryCarrier (BoolEndpoint v) := by
          cases v with
          | b0 =>
              exact Or.inl (BEDC.FKernel.Hist.hsame_refl BEDC.FKernel.Hist.BHist.Empty)
          | b1 =>
              exact Or.inr
                (BEDC.FKernel.Hist.hsame_refl
                  (BEDC.FKernel.Hist.BHist.e1 BEDC.FKernel.Hist.BHist.Empty))
        exact Exists.intro v
          (And.intro source
            (And.intro carrier (And.intro endpointCarrier sameEndpoint)))
  · intro witness
    cases witness with
    | intro _ payload =>
        cases payload with
        | intro _ classifier =>
            exact classifier.left

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
