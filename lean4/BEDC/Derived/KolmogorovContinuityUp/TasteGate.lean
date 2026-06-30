import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KolmogorovContinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KolmogorovContinuityUp : Type where
  | mk (I M S Q R E H C P N : BHist) : KolmogorovContinuityUp
  deriving DecidableEq

def kolmogorovContinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kolmogorovContinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kolmogorovContinuityEncodeBHist h

def kolmogorovContinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kolmogorovContinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kolmogorovContinuityDecodeBHist tail)

private theorem kolmogorovContinuity_decode_encode :
    ∀ h : BHist, kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kolmogorovContinuityFields : KolmogorovContinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KolmogorovContinuityUp.mk I M S Q R E H C P N =>
      [I, M, S, Q, R, E, H, C, P, N]

def kolmogorovContinuityToEventFlow : KolmogorovContinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kolmogorovContinuityFields x).map kolmogorovContinuityEncodeBHist

private def kolmogorovContinuityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kolmogorovContinuityEventAt index rest

def kolmogorovContinuityFromEventFlow
    (ef : EventFlow) : Option KolmogorovContinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KolmogorovContinuityUp.mk
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 0 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 1 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 2 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 3 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 4 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 5 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 6 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 7 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 8 ef))
      (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEventAt 9 ef)))

private theorem kolmogorovContinuity_round_trip
    (x : KolmogorovContinuityUp) :
    kolmogorovContinuityFromEventFlow (kolmogorovContinuityToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I M S Q R E H C P N =>
      change
        some
          (KolmogorovContinuityUp.mk
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist I))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist M))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist S))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist Q))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist R))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist E))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist H))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist C))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist P))
            (kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist N))) =
          some (KolmogorovContinuityUp.mk I M S Q R E H C P N)
      rw [kolmogorovContinuity_decode_encode I,
        kolmogorovContinuity_decode_encode M,
        kolmogorovContinuity_decode_encode S,
        kolmogorovContinuity_decode_encode Q,
        kolmogorovContinuity_decode_encode R,
        kolmogorovContinuity_decode_encode E,
        kolmogorovContinuity_decode_encode H,
        kolmogorovContinuity_decode_encode C,
        kolmogorovContinuity_decode_encode P,
        kolmogorovContinuity_decode_encode N]

private theorem kolmogorovContinuityToEventFlow_injective {x y : KolmogorovContinuityUp} :
    kolmogorovContinuityToEventFlow x = kolmogorovContinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kolmogorovContinuityFromEventFlow (kolmogorovContinuityToEventFlow x) =
        kolmogorovContinuityFromEventFlow (kolmogorovContinuityToEventFlow y) :=
    congrArg kolmogorovContinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kolmogorovContinuity_round_trip x).symm
      (Eq.trans hread (kolmogorovContinuity_round_trip y)))

instance kolmogorovContinuityBHistCarrier : BHistCarrier KolmogorovContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kolmogorovContinuityToEventFlow
  fromEventFlow := kolmogorovContinuityFromEventFlow

instance kolmogorovContinuityChapterTasteGate :
    ChapterTasteGate KolmogorovContinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kolmogorovContinuityFromEventFlow (kolmogorovContinuityToEventFlow x) = some x
    exact kolmogorovContinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kolmogorovContinuityToEventFlow_injective heq)

theorem KolmogorovContinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist, kolmogorovContinuityDecodeBHist (kolmogorovContinuityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier KolmogorovContinuityUp) ∧
        Nonempty (ChapterTasteGate KolmogorovContinuityUp) ∧
          kolmogorovContinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨kolmogorovContinuity_decode_encode,
      ⟨kolmogorovContinuityBHistCarrier⟩,
      ⟨kolmogorovContinuityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.KolmogorovContinuityUp
