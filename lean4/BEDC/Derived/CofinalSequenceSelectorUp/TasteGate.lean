import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalSequenceSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalSequenceSelectorUp : Type where
  | mk (I W M Q F U R H C P N : BHist) : CofinalSequenceSelectorUp

def cofinalSequenceSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalSequenceSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalSequenceSelectorEncodeBHist h

def cofinalSequenceSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalSequenceSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalSequenceSelectorDecodeBHist tail)

private theorem cofinalSequenceSelector_decode_encode_bhist :
    ∀ h : BHist,
      cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cofinalSequenceSelectorFields : CofinalSequenceSelectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalSequenceSelectorUp.mk I W M Q F U R H C P N => [I, W, M, Q, F, U, R, H, C, P, N]

def cofinalSequenceSelectorToEventFlow : CofinalSequenceSelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cofinalSequenceSelectorFields x).map cofinalSequenceSelectorEncodeBHist

private def cofinalSequenceSelectorEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cofinalSequenceSelectorEventAtDefault index rest

def cofinalSequenceSelectorFromEventFlow : EventFlow → Option CofinalSequenceSelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CofinalSequenceSelectorUp.mk
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 0 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 1 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 2 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 3 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 4 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 5 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 6 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 7 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 8 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 9 ef))
          (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEventAtDefault 10 ef)))

private theorem cofinalSequenceSelector_round_trip :
    ∀ x : CofinalSequenceSelectorUp,
      cofinalSequenceSelectorFromEventFlow (cofinalSequenceSelectorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I W M Q F U R H C P N =>
      change
        some
          (CofinalSequenceSelectorUp.mk
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist I))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist W))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist M))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist Q))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist F))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist U))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist R))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist H))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist C))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist P))
            (cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist N))) =
          some (CofinalSequenceSelectorUp.mk I W M Q F U R H C P N)
      rw [cofinalSequenceSelector_decode_encode_bhist I,
        cofinalSequenceSelector_decode_encode_bhist W,
        cofinalSequenceSelector_decode_encode_bhist M,
        cofinalSequenceSelector_decode_encode_bhist Q,
        cofinalSequenceSelector_decode_encode_bhist F,
        cofinalSequenceSelector_decode_encode_bhist U,
        cofinalSequenceSelector_decode_encode_bhist R,
        cofinalSequenceSelector_decode_encode_bhist H,
        cofinalSequenceSelector_decode_encode_bhist C,
        cofinalSequenceSelector_decode_encode_bhist P,
        cofinalSequenceSelector_decode_encode_bhist N]

private theorem cofinalSequenceSelectorToEventFlow_injective
    {x y : CofinalSequenceSelectorUp} :
    cofinalSequenceSelectorToEventFlow x = cofinalSequenceSelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalSequenceSelectorFromEventFlow (cofinalSequenceSelectorToEventFlow x) =
        cofinalSequenceSelectorFromEventFlow (cofinalSequenceSelectorToEventFlow y) :=
    congrArg cofinalSequenceSelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalSequenceSelector_round_trip x).symm
      (Eq.trans hread (cofinalSequenceSelector_round_trip y)))

instance cofinalSequenceSelectorBHistCarrier :
    BHistCarrier CofinalSequenceSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalSequenceSelectorToEventFlow
  fromEventFlow := cofinalSequenceSelectorFromEventFlow

instance cofinalSequenceSelectorChapterTasteGate :
    ChapterTasteGate CofinalSequenceSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalSequenceSelectorFromEventFlow (cofinalSequenceSelectorToEventFlow x) = some x
    exact cofinalSequenceSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalSequenceSelectorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CofinalSequenceSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalSequenceSelectorChapterTasteGate

theorem CofinalSequenceSelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cofinalSequenceSelectorDecodeBHist (cofinalSequenceSelectorEncodeBHist h) = h) ∧
      (∀ x : CofinalSequenceSelectorUp,
        cofinalSequenceSelectorFromEventFlow
          (cofinalSequenceSelectorToEventFlow x) = some x) ∧
        cofinalSequenceSelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨cofinalSequenceSelector_decode_encode_bhist,
      cofinalSequenceSelector_round_trip,
      rfl⟩

end BEDC.Derived.CofinalSequenceSelectorUp
