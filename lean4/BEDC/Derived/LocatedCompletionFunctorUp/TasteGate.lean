import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionFunctorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionFunctorUp : Type where
  | mk (L M U R E F H C P N : BHist) : LocatedCompletionFunctorUp
  deriving DecidableEq

def locatedCompletionFunctorEncodeBHist : BHist -> List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionFunctorEncodeBHist h

def locatedCompletionFunctorDecodeBHist : List BMark -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionFunctorDecodeBHist tail)

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedCompletionFunctorFields : LocatedCompletionFunctorUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionFunctorUp.mk L M U R E F H C P N => [L, M, U, R, E, F, H, C, P, N]

def locatedCompletionFunctorToEventFlow : LocatedCompletionFunctorUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map locatedCompletionFunctorEncodeBHist (locatedCompletionFunctorFields x)

private def locatedCompletionFunctorEventAt : Nat -> EventFlow -> List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedCompletionFunctorEventAt index rest

def locatedCompletionFunctorFromEventFlow (ef : EventFlow) :
    Option LocatedCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedCompletionFunctorUp.mk
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 0 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 1 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 2 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 3 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 4 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 5 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 6 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 7 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 8 ef))
      (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEventAt 9 ef)))

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip
    (x : LocatedCompletionFunctorUp) :
    locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L M U R E F H C P N =>
      change
        some
          (LocatedCompletionFunctorUp.mk
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist L))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist M))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist U))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist R))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist E))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist F))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist H))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist C))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist P))
            (locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist N))) =
          some (LocatedCompletionFunctorUp.mk L M U R E F H C P N)
      rw [LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode L,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode M,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode U,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode R,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode E,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode F,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode H,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode C,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode P,
        LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode N]

private theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompletionFunctorUp} :
    locatedCompletionFunctorToEventFlow x = locatedCompletionFunctorToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow x) =
        locatedCompletionFunctorFromEventFlow (locatedCompletionFunctorToEventFlow y) :=
    congrArg locatedCompletionFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompletionFunctorBHistCarrier : BHistCarrier LocatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionFunctorToEventFlow
  fromEventFlow := locatedCompletionFunctorFromEventFlow

instance locatedCompletionFunctorChapterTasteGate :
    ChapterTasteGate LocatedCompletionFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionFunctorFromEventFlow
      (locatedCompletionFunctorToEventFlow x) = some x
    exact LocatedCompletionFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedCompletionFunctorTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def LocatedCompletionFunctorTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate LocatedCompletionFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCompletionFunctorChapterTasteGate

theorem LocatedCompletionFunctorTasteGate_single_carrier_alignment :
    (∃ encode : BHist -> List BMark, encode = locatedCompletionFunctorEncodeBHist) ∧
      (∀ h : BHist,
        locatedCompletionFunctorDecodeBHist (locatedCompletionFunctorEncodeBHist h) = h) ∧
        Nonempty LocatedCompletionFunctorUp ∧ Nonempty (BHistCarrier LocatedCompletionFunctorUp) ∧
          Nonempty (ChapterTasteGate LocatedCompletionFunctorUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨locatedCompletionFunctorEncodeBHist, rfl⟩,
      LocatedCompletionFunctorTasteGate_single_carrier_alignment_decode,
      ⟨LocatedCompletionFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty⟩,
      ⟨locatedCompletionFunctorBHistCarrier⟩,
      ⟨locatedCompletionFunctorChapterTasteGate⟩⟩

end BEDC.Derived.LocatedCompletionFunctorUp.TasteGate
