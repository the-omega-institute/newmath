import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HahnBanachUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HahnBanachUp : Type where
  | mk (X B D F E L H C P N : BHist) : HahnBanachUp
  deriving DecidableEq

def hahnBanachEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hahnBanachEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hahnBanachEncodeBHist h

def hahnBanachDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hahnBanachDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hahnBanachDecodeBHist tail)

private theorem hahnBanach_decode_encode :
    forall h : BHist, hahnBanachDecodeBHist (hahnBanachEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hahnBanachFields : HahnBanachUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HahnBanachUp.mk X B D F E L H C P N => [X, B, D, F, E, L, H, C, P, N]

def hahnBanachToEventFlow : HahnBanachUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hahnBanachFields x).map hahnBanachEncodeBHist

private def hahnBanachEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hahnBanachEventAtDefault index rest

def hahnBanachFromEventFlow (ef : EventFlow) : Option HahnBanachUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HahnBanachUp.mk
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 0 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 1 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 2 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 3 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 4 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 5 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 6 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 7 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 8 ef))
      (hahnBanachDecodeBHist (hahnBanachEventAtDefault 9 ef)))

private theorem hahnBanach_round_trip :
    forall x : HahnBanachUp, hahnBanachFromEventFlow (hahnBanachToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X B D F E L H C P N =>
      change
        some
            (HahnBanachUp.mk
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist X))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist B))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist D))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist F))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist E))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist L))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist H))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist C))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist P))
              (hahnBanachDecodeBHist (hahnBanachEncodeBHist N))) =
          some (HahnBanachUp.mk X B D F E L H C P N)
      rw [hahnBanach_decode_encode X, hahnBanach_decode_encode B,
        hahnBanach_decode_encode D, hahnBanach_decode_encode F,
        hahnBanach_decode_encode E, hahnBanach_decode_encode L,
        hahnBanach_decode_encode H, hahnBanach_decode_encode C,
        hahnBanach_decode_encode P, hahnBanach_decode_encode N]

private theorem hahnBanachToEventFlow_injective {x y : HahnBanachUp} :
    hahnBanachToEventFlow x = hahnBanachToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hahnBanachFromEventFlow (hahnBanachToEventFlow x) =
        hahnBanachFromEventFlow (hahnBanachToEventFlow y) :=
    congrArg hahnBanachFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hahnBanach_round_trip x).symm
      (Eq.trans hread (hahnBanach_round_trip y)))

instance hahnBanachBHistCarrier : BHistCarrier HahnBanachUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hahnBanachToEventFlow
  fromEventFlow := hahnBanachFromEventFlow

instance hahnBanachChapterTasteGate : ChapterTasteGate HahnBanachUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hahnBanachFromEventFlow (hahnBanachToEventFlow x) = some x
    exact hahnBanach_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hahnBanachToEventFlow_injective heq)

def taste_gate : ChapterTasteGate HahnBanachUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hahnBanachChapterTasteGate

theorem HahnBanachTasteGate_single_carrier_alignment :
    (∃ carrier : BHistCarrier HahnBanachUp, Nonempty (@ChapterTasteGate HahnBanachUp carrier)) ∧
      (∀ h : BHist, hahnBanachDecodeBHist (hahnBanachEncodeBHist h) = h) ∧
        (∀ x : HahnBanachUp, hahnBanachFromEventFlow (hahnBanachToEventFlow x) = some x) ∧
          hahnBanachEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨hahnBanachBHistCarrier, ⟨hahnBanachChapterTasteGate⟩⟩,
      hahnBanach_decode_encode, hahnBanach_round_trip, rfl⟩

end BEDC.Derived.HahnBanachUp
