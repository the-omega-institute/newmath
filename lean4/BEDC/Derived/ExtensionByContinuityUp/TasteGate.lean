import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ExtensionByContinuityUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ExtensionByContinuityUp : Type where
  | mk (D F U L W R T A H C P N : BHist) : ExtensionByContinuityUp
  deriving DecidableEq

def extensionByContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: extensionByContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: extensionByContinuityEncodeBHist h

def extensionByContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (extensionByContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (extensionByContinuityDecodeBHist tail)

private theorem extensionByContinuity_decode_encode :
    ∀ h : BHist, extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def extensionByContinuityToEventFlow : ExtensionByContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ExtensionByContinuityUp.mk D F U L W R T A H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0],
        extensionByContinuityEncodeBHist D,
        extensionByContinuityEncodeBHist F,
        extensionByContinuityEncodeBHist U,
        extensionByContinuityEncodeBHist L,
        extensionByContinuityEncodeBHist W,
        extensionByContinuityEncodeBHist R,
        extensionByContinuityEncodeBHist T,
        extensionByContinuityEncodeBHist A,
        extensionByContinuityEncodeBHist H,
        extensionByContinuityEncodeBHist C,
        extensionByContinuityEncodeBHist P,
        extensionByContinuityEncodeBHist N]

private def extensionByContinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => extensionByContinuityEventAtDefault index rest

def extensionByContinuityFromEventFlow (ef : EventFlow) : Option ExtensionByContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ExtensionByContinuityUp.mk
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 1 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 2 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 3 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 4 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 5 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 6 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 7 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 8 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 9 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 10 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 11 ef))
      (extensionByContinuityDecodeBHist (extensionByContinuityEventAtDefault 12 ef)))

private theorem extensionByContinuity_round_trip :
    ∀ x : ExtensionByContinuityUp,
      extensionByContinuityFromEventFlow (extensionByContinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D F U L W R T A H C P N =>
      change
        some
          (ExtensionByContinuityUp.mk
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist D))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist F))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist U))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist L))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist W))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist R))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist T))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist A))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist H))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist C))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist P))
            (extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist N))) =
          some (ExtensionByContinuityUp.mk D F U L W R T A H C P N)
      rw [extensionByContinuity_decode_encode D, extensionByContinuity_decode_encode F,
        extensionByContinuity_decode_encode U, extensionByContinuity_decode_encode L,
        extensionByContinuity_decode_encode W, extensionByContinuity_decode_encode R,
        extensionByContinuity_decode_encode T, extensionByContinuity_decode_encode A,
        extensionByContinuity_decode_encode H, extensionByContinuity_decode_encode C,
        extensionByContinuity_decode_encode P, extensionByContinuity_decode_encode N]

private theorem extensionByContinuityToEventFlow_injective
    {x y : ExtensionByContinuityUp} :
    extensionByContinuityToEventFlow x = extensionByContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = extensionByContinuityFromEventFlow (extensionByContinuityToEventFlow x) :=
        (extensionByContinuity_round_trip x).symm
      _ = extensionByContinuityFromEventFlow (extensionByContinuityToEventFlow y) :=
        congrArg extensionByContinuityFromEventFlow hxy
      _ = some y := extensionByContinuity_round_trip y
  exact Option.some.inj optionEq

instance extensionByContinuityBHistCarrier : BHistCarrier ExtensionByContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := extensionByContinuityToEventFlow
  fromEventFlow := extensionByContinuityFromEventFlow

instance extensionByContinuityChapterTasteGate :
    ChapterTasteGate ExtensionByContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change extensionByContinuityFromEventFlow (extensionByContinuityToEventFlow x) = some x
    exact extensionByContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (extensionByContinuityToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ExtensionByContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  extensionByContinuityChapterTasteGate

theorem ExtensionByContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      extensionByContinuityDecodeBHist (extensionByContinuityEncodeBHist h) = h) ∧
      (∀ x : ExtensionByContinuityUp,
        extensionByContinuityFromEventFlow (extensionByContinuityToEventFlow x) = some x) ∧
        (∀ x y : ExtensionByContinuityUp,
          extensionByContinuityToEventFlow x = extensionByContinuityToEventFlow y → x = y) ∧
          extensionByContinuityEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : ExtensionByContinuityUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨extensionByContinuity_decode_encode, extensionByContinuity_round_trip,
      (fun _ _ heq => extensionByContinuityToEventFlow_injective heq), rfl,
      ⟨ExtensionByContinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty,
        ExtensionByContinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          injection h with hd _hf _hu _hl _hw _hr _ht _ha _hh _hc _hp _hn
          cases hd⟩⟩

end BEDC.Derived.ExtensionByContinuityUp.TasteGate
