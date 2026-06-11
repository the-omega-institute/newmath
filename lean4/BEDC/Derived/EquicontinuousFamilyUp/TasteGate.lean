import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EquicontinuousFamilyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EquicontinuousFamilyUp : Type where
  | mk (X F J M S R V H C P N : BHist) : EquicontinuousFamilyUp
  deriving DecidableEq

def equicontinuousFamilyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: equicontinuousFamilyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: equicontinuousFamilyEncodeBHist h

def equicontinuousFamilyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (equicontinuousFamilyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (equicontinuousFamilyDecodeBHist tail)

private theorem EquicontinuousFamilyTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def equicontinuousFamilyFields : EquicontinuousFamilyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EquicontinuousFamilyUp.mk X F J M S R V H C P N => [X, F, J, M, S, R, V, H, C, P, N]

def equicontinuousFamilyToEventFlow : EquicontinuousFamilyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (equicontinuousFamilyFields x).map equicontinuousFamilyEncodeBHist

private def equicontinuousFamilyEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => equicontinuousFamilyEventAtDefault index rest

def equicontinuousFamilyFromEventFlow (ef : EventFlow) :
    Option EquicontinuousFamilyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (EquicontinuousFamilyUp.mk
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 0 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 1 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 2 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 3 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 4 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 5 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 6 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 7 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 8 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 9 ef))
      (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEventAtDefault 10 ef)))

private theorem EquicontinuousFamilyTasteGate_single_carrier_alignment_round_trip
    (x : EquicontinuousFamilyUp) :
    equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X F J M S R V H C P N =>
      change
        some
          (EquicontinuousFamilyUp.mk
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist X))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist F))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist J))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist M))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist S))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist R))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist V))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist H))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist C))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist P))
            (equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist N))) =
          some (EquicontinuousFamilyUp.mk X F J M S R V H C P N)
      rw [EquicontinuousFamilyTasteGate_single_carrier_alignment_decode X,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode F,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode J,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode M,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode S,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode R,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode V,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode H,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode C,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode P,
        EquicontinuousFamilyTasteGate_single_carrier_alignment_decode N]

private theorem EquicontinuousFamilyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EquicontinuousFamilyUp} :
    equicontinuousFamilyToEventFlow x = equicontinuousFamilyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) =
        equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow y) :=
    congrArg equicontinuousFamilyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EquicontinuousFamilyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (EquicontinuousFamilyTasteGate_single_carrier_alignment_round_trip y)))

instance equicontinuousFamilyBHistCarrier : BHistCarrier EquicontinuousFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := equicontinuousFamilyToEventFlow
  fromEventFlow := equicontinuousFamilyFromEventFlow

instance equicontinuousFamilyChapterTasteGate :
    ChapterTasteGate EquicontinuousFamilyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change equicontinuousFamilyFromEventFlow (equicontinuousFamilyToEventFlow x) = some x
    exact EquicontinuousFamilyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EquicontinuousFamilyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem EquicontinuousFamilyTasteGate_single_carrier_alignment :
    (forall h : BHist, equicontinuousFamilyDecodeBHist (equicontinuousFamilyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier EquicontinuousFamilyUp) ∧
        Nonempty (ChapterTasteGate EquicontinuousFamilyUp) ∧
          equicontinuousFamilyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨EquicontinuousFamilyTasteGate_single_carrier_alignment_decode,
      ⟨⟨equicontinuousFamilyBHistCarrier⟩,
        ⟨⟨equicontinuousFamilyChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.EquicontinuousFamilyUp
