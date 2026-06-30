import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperbolicTranslationLengthUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperbolicTranslationLengthUp : Type where
  | mk (M F B X R D E H C P N : BHist) : HyperbolicTranslationLengthUp
  deriving DecidableEq

def hyperbolicTranslationLengthEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperbolicTranslationLengthEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperbolicTranslationLengthEncodeBHist h

def hyperbolicTranslationLengthDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperbolicTranslationLengthDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperbolicTranslationLengthDecodeBHist tail)

private theorem HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperbolicTranslationLengthFields :
    HyperbolicTranslationLengthUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperbolicTranslationLengthUp.mk M F B X R D E H C P N =>
      [M, F, B, X, R, D, E, H, C, P, N]

def hyperbolicTranslationLengthToEventFlow :
    HyperbolicTranslationLengthUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperbolicTranslationLengthFields x).map
      hyperbolicTranslationLengthEncodeBHist

private def hyperbolicTranslationLengthEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hyperbolicTranslationLengthEventAtDefault index rest

def hyperbolicTranslationLengthFromEventFlow
    (ef : EventFlow) : Option HyperbolicTranslationLengthUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HyperbolicTranslationLengthUp.mk
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 0 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 1 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 2 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 3 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 4 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 5 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 6 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 7 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 8 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 9 ef))
      (hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEventAtDefault 10 ef)))

private theorem HyperbolicTranslationLengthTasteGate_single_carrier_alignment_round_trip
    (x : HyperbolicTranslationLengthUp) :
    hyperbolicTranslationLengthFromEventFlow
      (hyperbolicTranslationLengthToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M F B X R D E H C P N =>
      change
        some
          (HyperbolicTranslationLengthUp.mk
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist M))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist F))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist B))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist X))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist R))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist D))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist E))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist H))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist C))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist P))
            (hyperbolicTranslationLengthDecodeBHist
              (hyperbolicTranslationLengthEncodeBHist N))) =
          some (HyperbolicTranslationLengthUp.mk M F B X R D E H C P N)
      rw [HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode M,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode F,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode B,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode X,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode R,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode D,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode E,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode H,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode C,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode P,
        HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode N]

private theorem HyperbolicTranslationLengthTasteGate_single_carrier_alignment_injective
    {x y : HyperbolicTranslationLengthUp} :
    hyperbolicTranslationLengthToEventFlow x =
      hyperbolicTranslationLengthToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperbolicTranslationLengthFromEventFlow
          (hyperbolicTranslationLengthToEventFlow x) =
        hyperbolicTranslationLengthFromEventFlow
          (hyperbolicTranslationLengthToEventFlow y) :=
    congrArg hyperbolicTranslationLengthFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (HyperbolicTranslationLengthTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (HyperbolicTranslationLengthTasteGate_single_carrier_alignment_round_trip y)))

private theorem HyperbolicTranslationLengthTasteGate_single_carrier_alignment_fields :
    ∀ x y : HyperbolicTranslationLengthUp,
      hyperbolicTranslationLengthFields x = hyperbolicTranslationLengthFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ F₁ B₁ X₁ R₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ F₂ B₂ X₂ R₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance hyperbolicTranslationLengthBHistCarrier :
    BHistCarrier HyperbolicTranslationLengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperbolicTranslationLengthToEventFlow
  fromEventFlow := hyperbolicTranslationLengthFromEventFlow

instance hyperbolicTranslationLengthChapterTasteGate :
    ChapterTasteGate HyperbolicTranslationLengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      hyperbolicTranslationLengthFromEventFlow
        (hyperbolicTranslationLengthToEventFlow x) = some x
    exact HyperbolicTranslationLengthTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HyperbolicTranslationLengthTasteGate_single_carrier_alignment_injective heq)

instance hyperbolicTranslationLengthFieldFaithful :
    FieldFaithful HyperbolicTranslationLengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperbolicTranslationLengthFields
  field_faithful := HyperbolicTranslationLengthTasteGate_single_carrier_alignment_fields

instance hyperbolicTranslationLengthNontrivial :
    Nontrivial HyperbolicTranslationLengthUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperbolicTranslationLengthUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      HyperbolicTranslationLengthUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperbolicTranslationLengthTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      hyperbolicTranslationLengthDecodeBHist
        (hyperbolicTranslationLengthEncodeBHist h) = h) ∧
      (∀ x : HyperbolicTranslationLengthUp,
        hyperbolicTranslationLengthFromEventFlow
          (hyperbolicTranslationLengthToEventFlow x) = some x) ∧
        (∀ x y : HyperbolicTranslationLengthUp,
          hyperbolicTranslationLengthToEventFlow x =
            hyperbolicTranslationLengthToEventFlow y → x = y) ∧
          hyperbolicTranslationLengthEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨HyperbolicTranslationLengthTasteGate_single_carrier_alignment_decode_encode,
      HyperbolicTranslationLengthTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => HyperbolicTranslationLengthTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.HyperbolicTranslationLengthUp
