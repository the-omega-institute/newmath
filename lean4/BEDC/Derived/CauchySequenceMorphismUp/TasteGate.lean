import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySequenceMorphismUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchySequenceMorphismUp : Type where
  | mk (S T M D E H C P N : BHist) : CauchySequenceMorphismUp
  deriving DecidableEq

def cauchySequenceMorphismEncodeBHist : BHist -> RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySequenceMorphismEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySequenceMorphismEncodeBHist h

def cauchySequenceMorphismDecodeBHist : RawEvent -> BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySequenceMorphismDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySequenceMorphismDecodeBHist tail)

private theorem CauchySequenceMorphismTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySequenceMorphismFields : CauchySequenceMorphismUp -> List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CauchySequenceMorphismUp.mk S T M D E H C P N => [S, T, M, D, E, H, C, P, N]

def cauchySequenceMorphismToEventFlow : CauchySequenceMorphismUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => List.map cauchySequenceMorphismEncodeBHist (cauchySequenceMorphismFields x)

private def cauchySequenceMorphismEventAt : Nat -> EventFlow -> RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySequenceMorphismEventAt index rest

def cauchySequenceMorphismFromEventFlow : EventFlow -> Option CauchySequenceMorphismUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchySequenceMorphismUp.mk
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 0 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 1 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 2 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 3 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 4 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 5 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 6 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 7 ef))
        (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEventAt 8 ef)))

private theorem cauchySequenceMorphism_round_trip :
    forall x : CauchySequenceMorphismUp,
      cauchySequenceMorphismFromEventFlow (cauchySequenceMorphismToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T M D E H C P N =>
      change
        some
            (CauchySequenceMorphismUp.mk
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist S))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist T))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist M))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist D))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist E))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist H))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist C))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist P))
              (cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist N))) =
          some (CauchySequenceMorphismUp.mk S T M D E H C P N)
      rw [CauchySequenceMorphismTasteGate_single_carrier_alignment_decode S,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode T,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode M,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode D,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode E,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode H,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode C,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode P,
        CauchySequenceMorphismTasteGate_single_carrier_alignment_decode N]

private theorem cauchySequenceMorphismToEventFlow_injective {x y : CauchySequenceMorphismUp} :
    cauchySequenceMorphismToEventFlow x = cauchySequenceMorphismToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySequenceMorphismFromEventFlow (cauchySequenceMorphismToEventFlow x) =
        cauchySequenceMorphismFromEventFlow (cauchySequenceMorphismToEventFlow y) :=
    congrArg cauchySequenceMorphismFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchySequenceMorphism_round_trip x).symm
      (Eq.trans hread (cauchySequenceMorphism_round_trip y)))

instance cauchySequenceMorphismBHistCarrier : BHistCarrier CauchySequenceMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySequenceMorphismToEventFlow
  fromEventFlow := cauchySequenceMorphismFromEventFlow

instance cauchySequenceMorphismChapterTasteGate :
    ChapterTasteGate CauchySequenceMorphismUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySequenceMorphismFromEventFlow (cauchySequenceMorphismToEventFlow x) =
      some x
    exact cauchySequenceMorphism_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchySequenceMorphismToEventFlow_injective heq)

theorem CauchySequenceMorphismTasteGate_single_carrier_alignment :
    (forall h : BHist,
      cauchySequenceMorphismDecodeBHist (cauchySequenceMorphismEncodeBHist h) = h) /\
      (forall x : CauchySequenceMorphismUp,
        cauchySequenceMorphismFromEventFlow (cauchySequenceMorphismToEventFlow x) = some x) /\
        (forall x y : CauchySequenceMorphismUp,
          cauchySequenceMorphismToEventFlow x = cauchySequenceMorphismToEventFlow y ->
            x = y) /\
          cauchySequenceMorphismEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchySequenceMorphismTasteGate_single_carrier_alignment_decode,
      cauchySequenceMorphism_round_trip,
      by
        intro x y heq
        exact cauchySequenceMorphismToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchySequenceMorphismUp.TasteGate
