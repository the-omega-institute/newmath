import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevPoincareFiniteEnergyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevPoincareFiniteEnergyUp : Type where
  | mk (S Q D W Y A R Z H C P N : BHist) : SobolevPoincareFiniteEnergyUp
  deriving DecidableEq

def sobolevPoincareFiniteEnergyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevPoincareFiniteEnergyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevPoincareFiniteEnergyEncodeBHist h

def sobolevPoincareFiniteEnergyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevPoincareFiniteEnergyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevPoincareFiniteEnergyDecodeBHist tail)

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      sobolevPoincareFiniteEnergyDecodeBHist
          (sobolevPoincareFiniteEnergyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sobolevPoincareFiniteEnergyToEventFlow :
    SobolevPoincareFiniteEnergyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevPoincareFiniteEnergyUp.mk S Q D W Y A R Z H C P N =>
      [sobolevPoincareFiniteEnergyEncodeBHist S,
        sobolevPoincareFiniteEnergyEncodeBHist Q,
        sobolevPoincareFiniteEnergyEncodeBHist D,
        sobolevPoincareFiniteEnergyEncodeBHist W,
        sobolevPoincareFiniteEnergyEncodeBHist Y,
        sobolevPoincareFiniteEnergyEncodeBHist A,
        sobolevPoincareFiniteEnergyEncodeBHist R,
        sobolevPoincareFiniteEnergyEncodeBHist Z,
        sobolevPoincareFiniteEnergyEncodeBHist H,
        sobolevPoincareFiniteEnergyEncodeBHist C,
        sobolevPoincareFiniteEnergyEncodeBHist P,
        sobolevPoincareFiniteEnergyEncodeBHist N]

private def sobolevPoincareFiniteEnergyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      sobolevPoincareFiniteEnergyEventAtDefault index rest

def sobolevPoincareFiniteEnergyFromEventFlow
    (ef : EventFlow) : Option SobolevPoincareFiniteEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SobolevPoincareFiniteEnergyUp.mk
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 0 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 1 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 2 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 3 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 4 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 5 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 6 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 7 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 8 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 9 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 10 ef))
      (sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEventAtDefault 11 ef)))

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SobolevPoincareFiniteEnergyUp,
      sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q D W Y A R Z H C P N =>
      change
        some
          (SobolevPoincareFiniteEnergyUp.mk
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist S))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist Q))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist D))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist W))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist Y))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist A))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist R))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist Z))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist H))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist C))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist P))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist N))) =
          some (SobolevPoincareFiniteEnergyUp.mk S Q D W Y A R Z H C P N)
      rw [SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode S,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode Q,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode D,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode W,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode Y,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode A,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode R,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode Z,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode H,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode C,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode P,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode N]

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SobolevPoincareFiniteEnergyUp} :
    sobolevPoincareFiniteEnergyToEventFlow x =
      sobolevPoincareFiniteEnergyToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow y) :=
    congrArg sobolevPoincareFiniteEnergyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip y)))

instance sobolevPoincareFiniteEnergyBHistCarrier :
    BHistCarrier SobolevPoincareFiniteEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevPoincareFiniteEnergyToEventFlow
  fromEventFlow := sobolevPoincareFiniteEnergyFromEventFlow

instance sobolevPoincareFiniteEnergyChapterTasteGate :
    ChapterTasteGate SobolevPoincareFiniteEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        some x
    exact SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate SobolevPoincareFiniteEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevPoincareFiniteEnergyChapterTasteGate

theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier SobolevPoincareFiniteEnergyUp) ∧
      Nonempty (ChapterTasteGate SobolevPoincareFiniteEnergyUp) ∧
        (∀ x : SobolevPoincareFiniteEnergyUp,
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          sobolevPoincareFiniteEnergyEncodeBHist BHist.Empty = ([] : List BMark) ∧
            sobolevPoincareFiniteEnergyDecodeBHist [BMark.b1] = BHist.e1 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨sobolevPoincareFiniteEnergyBHistCarrier⟩,
      ⟨sobolevPoincareFiniteEnergyChapterTasteGate⟩,
      ChapterTasteGate.round_trip,
      rfl,
      rfl⟩

end BEDC.Derived.SobolevPoincareFiniteEnergyUp.TasteGate
