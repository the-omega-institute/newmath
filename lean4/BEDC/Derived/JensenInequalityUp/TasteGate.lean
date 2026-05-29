import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.JensenInequalityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive JensenInequalityUp : Type where
  | mk (F W A X Y R Q H C P N : BHist) : JensenInequalityUp
  deriving DecidableEq

def jensenInequalityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: jensenInequalityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: jensenInequalityEncodeBHist h

def jensenInequalityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (jensenInequalityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (jensenInequalityDecodeBHist tail)

private theorem JensenInequalityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, jensenInequalityDecodeBHist (jensenInequalityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def jensenInequalityFields : JensenInequalityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | JensenInequalityUp.mk F W A X Y R Q H C P N => [F, W, A, X, Y, R, Q, H, C, P, N]

def jensenInequalityToEventFlow : JensenInequalityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (jensenInequalityFields x).map jensenInequalityEncodeBHist

private def jensenInequalityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => jensenInequalityEventAtDefault index rest

def jensenInequalityFromEventFlow : EventFlow → Option JensenInequalityUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (JensenInequalityUp.mk
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 0 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 1 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 2 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 3 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 4 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 5 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 6 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 7 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 8 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 9 ef))
      (jensenInequalityDecodeBHist (jensenInequalityEventAtDefault 10 ef)))

private theorem JensenInequalityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : JensenInequalityUp,
      jensenInequalityFromEventFlow (jensenInequalityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F W A X Y R Q H C P N =>
      have hmk :
          JensenInequalityUp.mk
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist F))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist W))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist A))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist X))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist Y))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist R))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist Q))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist H))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist C))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist P))
              (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist N)) =
            JensenInequalityUp.mk F W A X Y R Q H C P N := by
        rw [JensenInequalityTasteGate_single_carrier_alignment_decode_encode F,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode W,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode A,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode X,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode Y,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode R,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode Q,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode H,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode C,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode P,
          JensenInequalityTasteGate_single_carrier_alignment_decode_encode N]
      exact congrArg some hmk

private theorem JensenInequalityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : JensenInequalityUp} :
    jensenInequalityToEventFlow x = jensenInequalityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      jensenInequalityFromEventFlow (jensenInequalityToEventFlow x) =
        jensenInequalityFromEventFlow (jensenInequalityToEventFlow y) :=
    congrArg jensenInequalityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (JensenInequalityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (JensenInequalityTasteGate_single_carrier_alignment_round_trip y)))

private theorem JensenInequalityTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : JensenInequalityUp, jensenInequalityFields x = jensenInequalityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ W₁ A₁ X₁ Y₁ R₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk F₂ W₂ A₂ X₂ Y₂ R₂ Q₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hF tail0
          injection tail0 with hW tail1
          injection tail1 with hA tail2
          injection tail2 with hX tail3
          injection tail3 with hY tail4
          injection tail4 with hR tail5
          injection tail5 with hQ tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hF
          subst hW
          subst hA
          subst hX
          subst hY
          subst hR
          subst hQ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance jensenInequalityBHistCarrier : BHistCarrier JensenInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := jensenInequalityToEventFlow
  fromEventFlow := jensenInequalityFromEventFlow

instance jensenInequalityChapterTasteGate : ChapterTasteGate JensenInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change jensenInequalityFromEventFlow (jensenInequalityToEventFlow x) = some x
    exact JensenInequalityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (JensenInequalityTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance jensenInequalityFieldFaithful : FieldFaithful JensenInequalityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := jensenInequalityFields
  field_faithful := JensenInequalityTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate JensenInequalityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  jensenInequalityChapterTasteGate

theorem JensenInequalityTasteGate_single_carrier_alignment :
    (∀ h : BHist, jensenInequalityDecodeBHist (jensenInequalityEncodeBHist h) = h) ∧
      (∀ x : JensenInequalityUp,
        jensenInequalityFromEventFlow (jensenInequalityToEventFlow x) = some x) ∧
        (∀ x y : JensenInequalityUp,
          jensenInequalityToEventFlow x = jensenInequalityToEventFlow y → x = y) ∧
          jensenInequalityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  have hdecode :
      ∀ h : BHist, jensenInequalityDecodeBHist (jensenInequalityEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  constructor
  · exact hdecode
  constructor
  · intro x
    cases x with
    | mk F W A X Y R Q H C P N =>
        have hmk :
            JensenInequalityUp.mk
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist F))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist W))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist A))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist X))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist Y))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist R))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist Q))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist H))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist C))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist P))
                (jensenInequalityDecodeBHist (jensenInequalityEncodeBHist N)) =
              JensenInequalityUp.mk F W A X Y R Q H C P N := by
          rw [hdecode F, hdecode W, hdecode A, hdecode X, hdecode Y, hdecode R,
            hdecode Q, hdecode H, hdecode C, hdecode P, hdecode N]
        exact congrArg some hmk
  constructor
  · intro x y heq
    cases x with
    | mk F₁ W₁ A₁ X₁ Y₁ R₁ Q₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk F₂ W₂ A₂ X₂ Y₂ R₂ Q₂ H₂ C₂ P₂ N₂ =>
            change
              [jensenInequalityEncodeBHist F₁, jensenInequalityEncodeBHist W₁,
                jensenInequalityEncodeBHist A₁, jensenInequalityEncodeBHist X₁,
                jensenInequalityEncodeBHist Y₁, jensenInequalityEncodeBHist R₁,
                jensenInequalityEncodeBHist Q₁, jensenInequalityEncodeBHist H₁,
                jensenInequalityEncodeBHist C₁, jensenInequalityEncodeBHist P₁,
                jensenInequalityEncodeBHist N₁] =
              [jensenInequalityEncodeBHist F₂, jensenInequalityEncodeBHist W₂,
                jensenInequalityEncodeBHist A₂, jensenInequalityEncodeBHist X₂,
                jensenInequalityEncodeBHist Y₂, jensenInequalityEncodeBHist R₂,
                jensenInequalityEncodeBHist Q₂, jensenInequalityEncodeBHist H₂,
                jensenInequalityEncodeBHist C₂, jensenInequalityEncodeBHist P₂,
                jensenInequalityEncodeBHist N₂] at heq
            injection heq with hF tail0
            injection tail0 with hW tail1
            injection tail1 with hA tail2
            injection tail2 with hX tail3
            injection tail3 with hY tail4
            injection tail4 with hR tail5
            injection tail5 with hQ tail6
            injection tail6 with hH tail7
            injection tail7 with hC tail8
            injection tail8 with hP tail9
            injection tail9 with hN _
            have hF' : F₁ = F₂ :=
              Eq.trans (hdecode F₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hF) (hdecode F₂))
            have hW' : W₁ = W₂ :=
              Eq.trans (hdecode W₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hW) (hdecode W₂))
            have hA' : A₁ = A₂ :=
              Eq.trans (hdecode A₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hA) (hdecode A₂))
            have hX' : X₁ = X₂ :=
              Eq.trans (hdecode X₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hX) (hdecode X₂))
            have hY' : Y₁ = Y₂ :=
              Eq.trans (hdecode Y₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hY) (hdecode Y₂))
            have hR' : R₁ = R₂ :=
              Eq.trans (hdecode R₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hR) (hdecode R₂))
            have hQ' : Q₁ = Q₂ :=
              Eq.trans (hdecode Q₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hQ) (hdecode Q₂))
            have hH' : H₁ = H₂ :=
              Eq.trans (hdecode H₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hH) (hdecode H₂))
            have hC' : C₁ = C₂ :=
              Eq.trans (hdecode C₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hC) (hdecode C₂))
            have hP' : P₁ = P₂ :=
              Eq.trans (hdecode P₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hP) (hdecode P₂))
            have hN' : N₁ = N₂ :=
              Eq.trans (hdecode N₁).symm (Eq.trans (congrArg jensenInequalityDecodeBHist hN) (hdecode N₂))
            cases hF'
            cases hW'
            cases hA'
            cases hX'
            cases hY'
            cases hR'
            cases hQ'
            cases hH'
            cases hC'
            cases hP'
            cases hN'
            rfl
  · rfl

end BEDC.Derived.JensenInequalityUp
