import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DarbouxTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DarbouxTheoremUp : Type where
  | mk (F I A B Y S D R Q E H C P N : BHist) : DarbouxTheoremUp
  deriving DecidableEq

def darbouxTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: darbouxTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: darbouxTheoremEncodeBHist h

def darbouxTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (darbouxTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (darbouxTheoremDecodeBHist tail)

private theorem DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def darbouxTheoremFields : DarbouxTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DarbouxTheoremUp.mk F I A B Y S D R Q E H C P N =>
      [F, I, A, B, Y, S, D, R, Q, E, H, C, P, N]

def darbouxTheoremToEventFlow : DarbouxTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (darbouxTheoremFields x).map darbouxTheoremEncodeBHist

private def darbouxTheoremEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => darbouxTheoremEventAtDefault index rest

def darbouxTheoremFromEventFlow (ef : EventFlow) : Option DarbouxTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DarbouxTheoremUp.mk
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 0 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 1 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 2 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 3 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 4 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 5 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 6 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 7 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 8 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 9 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 10 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 11 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 12 ef))
      (darbouxTheoremDecodeBHist (darbouxTheoremEventAtDefault 13 ef)))

private theorem DarbouxTheoremTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DarbouxTheoremUp,
      darbouxTheoremFromEventFlow (darbouxTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I A B Y S D R Q E H C P N =>
      change
        some
          (DarbouxTheoremUp.mk
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist F))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist I))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist A))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist B))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist Y))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist S))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist D))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist R))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist Q))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist E))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist H))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist C))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist P))
            (darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist N))) =
          some (DarbouxTheoremUp.mk F I A B Y S D R Q E H C P N)
      rw [DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode F,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode I,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode A,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode B,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode Y,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode S,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode D,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode R,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode Q,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode E,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode H,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode C,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode P,
        DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode N]

private theorem DarbouxTheoremTasteGate_single_carrier_alignment_injective
    {x y : DarbouxTheoremUp} :
    darbouxTheoremToEventFlow x = darbouxTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      darbouxTheoremFromEventFlow (darbouxTheoremToEventFlow x) =
        darbouxTheoremFromEventFlow (darbouxTheoremToEventFlow y) :=
    congrArg darbouxTheoremFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (DarbouxTheoremTasteGate_single_carrier_alignment_round_trip x).symm
        (Eq.trans hread (DarbouxTheoremTasteGate_single_carrier_alignment_round_trip y)))

instance darbouxTheoremBHistCarrier : BHistCarrier DarbouxTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := darbouxTheoremToEventFlow
  fromEventFlow := darbouxTheoremFromEventFlow

instance darbouxTheoremChapterTasteGate : ChapterTasteGate DarbouxTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change darbouxTheoremFromEventFlow (darbouxTheoremToEventFlow x) = some x
    exact DarbouxTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DarbouxTheoremTasteGate_single_carrier_alignment_injective heq)

theorem DarbouxTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, darbouxTheoremDecodeBHist (darbouxTheoremEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DarbouxTheoremUp) ∧
      Nonempty (ChapterTasteGate DarbouxTheoremUp) ∧
      darbouxTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DarbouxTheoremTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨darbouxTheoremBHistCarrier⟩, ⟨⟨darbouxTheoremChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.DarbouxTheoremUp
