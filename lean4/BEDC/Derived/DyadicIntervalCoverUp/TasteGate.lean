import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalCoverUp : Type where
  | mk (L U M R V W Q A H C P N : BHist) : DyadicIntervalCoverUp
  deriving DecidableEq

def dyadicIntervalCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalCoverEncodeBHist h

def dyadicIntervalCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalCoverDecodeBHist tail)

private theorem DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def dyadicIntervalCoverFields : DyadicIntervalCoverUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalCoverUp.mk L U M R V W Q A H C P N => [L, U, M, R, V, W, Q, A, H, C, P, N]

def dyadicIntervalCoverToEventFlow : DyadicIntervalCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicIntervalCoverFields x).map dyadicIntervalCoverEncodeBHist

private def dyadicIntervalCoverEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalCoverEventAt index rest

def dyadicIntervalCoverFromEventFlow (ef : EventFlow) : Option DyadicIntervalCoverUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalCoverUp.mk
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 0 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 1 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 2 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 3 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 4 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 5 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 6 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 7 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 8 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 9 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 10 ef))
      (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEventAt 11 ef)))

private theorem DyadicIntervalCoverTasteGate_single_carrier_alignment_round_trip
    (x : DyadicIntervalCoverUp) :
    dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      change
        some
          (DyadicIntervalCoverUp.mk
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist L))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist U))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist M))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist R))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist V))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist W))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist Q))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist A))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist H))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist C))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist P))
            (dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist N))) =
          some (DyadicIntervalCoverUp.mk L U M R V W Q A H C P N)
      rw [DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode L,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode U,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode M,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode R,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode V,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode W,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode A,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode H,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode C,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode P,
        DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicIntervalCoverUp} :
    dyadicIntervalCoverToEventFlow x = dyadicIntervalCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) =
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow y) :=
    congrArg dyadicIntervalCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalCoverTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicIntervalCoverTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicIntervalCoverBHistCarrier : BHistCarrier DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalCoverToEventFlow
  fromEventFlow := dyadicIntervalCoverFromEventFlow

instance dyadicIntervalCoverChapterTasteGate :
    ChapterTasteGate DyadicIntervalCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x
    exact DyadicIntervalCoverTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicIntervalCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicIntervalCoverDecodeBHist (dyadicIntervalCoverEncodeBHist h) = h) ∧
      (∀ x : DyadicIntervalCoverUp,
        dyadicIntervalCoverFromEventFlow (dyadicIntervalCoverToEventFlow x) = some x) ∧
        (∀ x y : DyadicIntervalCoverUp,
          dyadicIntervalCoverToEventFlow x = dyadicIntervalCoverToEventFlow y → x = y) ∧
          dyadicIntervalCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DyadicIntervalCoverTasteGate_single_carrier_alignment_decode_encode,
      DyadicIntervalCoverTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => DyadicIntervalCoverTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicIntervalCoverUp
