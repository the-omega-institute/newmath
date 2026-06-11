import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SupportNerveCensusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SupportNerveCensusUp : Type where
  | mk (S A N B T L H R P M : BHist) : SupportNerveCensusUp
  deriving DecidableEq

def supportNerveCensusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: supportNerveCensusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: supportNerveCensusEncodeBHist h

def supportNerveCensusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (supportNerveCensusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (supportNerveCensusDecodeBHist tail)

private theorem supportNerveCensus_decode_encode_bhist :
    ∀ h : BHist,
      supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def supportNerveCensusToEventFlow : SupportNerveCensusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SupportNerveCensusUp.mk S A N B T L H R P M =>
      [supportNerveCensusEncodeBHist S,
        supportNerveCensusEncodeBHist A,
        supportNerveCensusEncodeBHist N,
        supportNerveCensusEncodeBHist B,
        supportNerveCensusEncodeBHist T,
        supportNerveCensusEncodeBHist L,
        supportNerveCensusEncodeBHist H,
        supportNerveCensusEncodeBHist R,
        supportNerveCensusEncodeBHist P,
        supportNerveCensusEncodeBHist M]

private def supportNerveCensusEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => supportNerveCensusEventAt index rest

def supportNerveCensusFromEventFlow : EventFlow → Option SupportNerveCensusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (SupportNerveCensusUp.mk
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 0 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 1 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 2 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 3 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 4 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 5 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 6 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 7 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 8 ef))
        (supportNerveCensusDecodeBHist (supportNerveCensusEventAt 9 ef)))

private theorem supportNerveCensus_round_trip :
    ∀ x : SupportNerveCensusUp,
      supportNerveCensusFromEventFlow (supportNerveCensusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A N B T L H R P M =>
      change
        some
            (SupportNerveCensusUp.mk
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist S))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist A))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist N))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist B))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist T))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist L))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist H))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist R))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist P))
              (supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist M))) =
          some (SupportNerveCensusUp.mk S A N B T L H R P M)
      rw [supportNerveCensus_decode_encode_bhist S,
        supportNerveCensus_decode_encode_bhist A,
        supportNerveCensus_decode_encode_bhist N,
        supportNerveCensus_decode_encode_bhist B,
        supportNerveCensus_decode_encode_bhist T,
        supportNerveCensus_decode_encode_bhist L,
        supportNerveCensus_decode_encode_bhist H,
        supportNerveCensus_decode_encode_bhist R,
        supportNerveCensus_decode_encode_bhist P,
        supportNerveCensus_decode_encode_bhist M]

private theorem supportNerveCensusToEventFlow_injective {x y : SupportNerveCensusUp} :
    supportNerveCensusToEventFlow x = supportNerveCensusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      supportNerveCensusFromEventFlow (supportNerveCensusToEventFlow x) =
        supportNerveCensusFromEventFlow (supportNerveCensusToEventFlow y) :=
    congrArg supportNerveCensusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (supportNerveCensus_round_trip x).symm
      (Eq.trans hread (supportNerveCensus_round_trip y)))

instance supportNerveCensusBHistCarrier : BHistCarrier SupportNerveCensusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := supportNerveCensusToEventFlow
  fromEventFlow := supportNerveCensusFromEventFlow

instance supportNerveCensusChapterTasteGate : ChapterTasteGate SupportNerveCensusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change supportNerveCensusFromEventFlow (supportNerveCensusToEventFlow x) = some x
    exact supportNerveCensus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (supportNerveCensusToEventFlow_injective heq)

theorem SupportNerveCensusTasteGate_single_carrier_alignment :
    (∀ h : BHist, supportNerveCensusDecodeBHist (supportNerveCensusEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SupportNerveCensusUp) ∧
        Nonempty (ChapterTasteGate SupportNerveCensusUp) ∧
          supportNerveCensusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨supportNerveCensus_decode_encode_bhist,
      ⟨supportNerveCensusBHistCarrier⟩,
      ⟨supportNerveCensusChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SupportNerveCensusUp
