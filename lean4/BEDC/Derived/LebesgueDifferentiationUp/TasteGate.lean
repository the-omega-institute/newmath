import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LebesgueDifferentiationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LebesgueDifferentiationUp : Type where
  | mk (M F V H0 A D E T C P N : BHist) : LebesgueDifferentiationUp
  deriving DecidableEq

def lebesgueDifferentiationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lebesgueDifferentiationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lebesgueDifferentiationEncodeBHist h

def lebesgueDifferentiationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lebesgueDifferentiationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lebesgueDifferentiationDecodeBHist tail)

private theorem LebesgueDifferentiationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lebesgueDifferentiationFields : LebesgueDifferentiationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LebesgueDifferentiationUp.mk M F V H0 A D E T C P N =>
      [M, F, V, H0, A, D, E, T, C, P, N]

def lebesgueDifferentiationToEventFlow : LebesgueDifferentiationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lebesgueDifferentiationFields x).map lebesgueDifferentiationEncodeBHist

private def lebesgueDifferentiationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lebesgueDifferentiationEventAt index rest

def lebesgueDifferentiationFromEventFlow : EventFlow → Option LebesgueDifferentiationUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (LebesgueDifferentiationUp.mk
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 0 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 1 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 2 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 3 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 4 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 5 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 6 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 7 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 8 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 9 flow))
          (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEventAt 10 flow)))

private theorem LebesgueDifferentiationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LebesgueDifferentiationUp,
      lebesgueDifferentiationFromEventFlow (lebesgueDifferentiationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M F V H0 A D E T C P N =>
      change
        some
          (LebesgueDifferentiationUp.mk
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist M))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist F))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist V))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist H0))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist A))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist D))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist E))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist T))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist C))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist P))
            (lebesgueDifferentiationDecodeBHist (lebesgueDifferentiationEncodeBHist N))) =
          some (LebesgueDifferentiationUp.mk M F V H0 A D E T C P N)
      rw [LebesgueDifferentiationTasteGate_single_carrier_alignment_decode M,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode F,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode V,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode H0,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode A,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode D,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode E,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode T,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode C,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode P,
        LebesgueDifferentiationTasteGate_single_carrier_alignment_decode N]

private theorem LebesgueDifferentiationTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LebesgueDifferentiationUp} :
    lebesgueDifferentiationToEventFlow x = lebesgueDifferentiationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lebesgueDifferentiationFromEventFlow (lebesgueDifferentiationToEventFlow x) =
        lebesgueDifferentiationFromEventFlow (lebesgueDifferentiationToEventFlow y) :=
    congrArg lebesgueDifferentiationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LebesgueDifferentiationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LebesgueDifferentiationTasteGate_single_carrier_alignment_round_trip y)))

instance lebesgueDifferentiationBHistCarrier : BHistCarrier LebesgueDifferentiationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lebesgueDifferentiationToEventFlow
  fromEventFlow := lebesgueDifferentiationFromEventFlow

instance lebesgueDifferentiationChapterTasteGate :
    ChapterTasteGate LebesgueDifferentiationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      lebesgueDifferentiationFromEventFlow (lebesgueDifferentiationToEventFlow x) =
        some x
    exact LebesgueDifferentiationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LebesgueDifferentiationTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LebesgueDifferentiationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lebesgueDifferentiationChapterTasteGate

theorem LebesgueDifferentiationTasteGate_single_carrier_alignment :
    (∀ h : BHist, lebesgueDifferentiationDecodeBHist
        (lebesgueDifferentiationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LebesgueDifferentiationUp) ∧
        Nonempty (ChapterTasteGate LebesgueDifferentiationUp) ∧
          lebesgueDifferentiationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LebesgueDifferentiationTasteGate_single_carrier_alignment_decode,
      ⟨lebesgueDifferentiationBHistCarrier⟩,
      ⟨lebesgueDifferentiationChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.LebesgueDifferentiationUp
