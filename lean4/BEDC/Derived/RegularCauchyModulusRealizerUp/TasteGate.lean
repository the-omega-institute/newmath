import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusRealizerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusRealizerUp : Type where
  | mk (A M W D Q E H C P N : BHist) : RegularCauchyModulusRealizerUp
  deriving DecidableEq

def regularCauchyModulusRealizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusRealizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusRealizerEncodeBHist h

def regularCauchyModulusRealizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusRealizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusRealizerDecodeBHist tail)

private theorem RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyModulusRealizerDecodeBHist
        (regularCauchyModulusRealizerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyModulusRealizerFields :
    RegularCauchyModulusRealizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyModulusRealizerUp.mk A M W D Q E H C P N =>
      [A, M, W, D, Q, E, H, C, P, N]

def regularCauchyModulusRealizerToEventFlow :
    RegularCauchyModulusRealizerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyModulusRealizerFields x).map
        regularCauchyModulusRealizerEncodeBHist

private def RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt index rest

def regularCauchyModulusRealizerFromEventFlow
    (ef : EventFlow) : Option RegularCauchyModulusRealizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyModulusRealizerUp.mk
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 0 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 1 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 2 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 3 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 4 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 5 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 6 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 7 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 8 ef))
      (regularCauchyModulusRealizerDecodeBHist
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyModulusRealizerUp) :
    regularCauchyModulusRealizerFromEventFlow
        (regularCauchyModulusRealizerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A M W D Q E H C P N =>
      change
        some
          (RegularCauchyModulusRealizerUp.mk
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist A))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist M))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist W))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist D))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist Q))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist E))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist H))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist C))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist P))
            (regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist N))) =
          some (RegularCauchyModulusRealizerUp.mk A M W D Q E H C P N)
      rw [RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyModulusRealizerUp} :
    regularCauchyModulusRealizerToEventFlow x =
      regularCauchyModulusRealizerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow x) =
        regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow y) :=
    congrArg regularCauchyModulusRealizerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyModulusRealizerUp,
      regularCauchyModulusRealizerFields x =
        regularCauchyModulusRealizerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ M₁ W₁ D₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ M₂ W₂ D₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance regularCauchyModulusRealizerBHistCarrier :
    BHistCarrier RegularCauchyModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyModulusRealizerToEventFlow
  fromEventFlow := regularCauchyModulusRealizerFromEventFlow

instance regularCauchyModulusRealizerChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyModulusRealizerFromEventFlow
          (regularCauchyModulusRealizerToEventFlow x) = some x
    exact RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyModulusRealizerFieldFaithful :
    FieldFaithful RegularCauchyModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyModulusRealizerFields
  field_faithful :=
    RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyModulusRealizerNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RegularCauchyModulusRealizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyModulusRealizerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyModulusRealizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RegularCauchyModulusRealizerTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RegularCauchyModulusRealizerUp) ∧
      Nonempty (FieldFaithful RegularCauchyModulusRealizerUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial RegularCauchyModulusRealizerUp) ∧
          (∀ h : BHist,
            regularCauchyModulusRealizerDecodeBHist
              (regularCauchyModulusRealizerEncodeBHist h) = h) ∧
            (∀ x : RegularCauchyModulusRealizerUp,
              regularCauchyModulusRealizerFromEventFlow
                (regularCauchyModulusRealizerToEventFlow x) = some x) ∧
              regularCauchyModulusRealizerEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨regularCauchyModulusRealizerChapterTasteGate⟩,
      ⟨regularCauchyModulusRealizerFieldFaithful⟩,
      ⟨regularCauchyModulusRealizerNontrivial⟩,
      RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyModulusRealizerTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.RegularCauchyModulusRealizerUp.TasteGate
