import BEDC.Derived.FormalTopologyUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalTopologyUp : Type where
  | mk (M B U R D S I H C P N : BHist) : FormalTopologyUp
  deriving DecidableEq

def formalTopologyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalTopologyEncodeBHist h

def formalTopologyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalTopologyDecodeBHist tail)

private theorem FormalTopologyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, formalTopologyDecodeBHist (formalTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def formalTopologyToEventFlow : FormalTopologyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalTopologyUp.mk M B U R D S I H C P N =>
      [formalTopologyEncodeBHist M,
        formalTopologyEncodeBHist B,
        formalTopologyEncodeBHist U,
        formalTopologyEncodeBHist R,
        formalTopologyEncodeBHist D,
        formalTopologyEncodeBHist S,
        formalTopologyEncodeBHist I,
        formalTopologyEncodeBHist H,
        formalTopologyEncodeBHist C,
        formalTopologyEncodeBHist P,
        formalTopologyEncodeBHist N]

private def formalTopologyEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => formalTopologyEventAtDefault index rest

def formalTopologyFromEventFlow (ef : EventFlow) : Option FormalTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FormalTopologyUp.mk
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 0 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 1 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 2 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 3 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 4 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 5 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 6 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 7 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 8 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 9 ef))
      (formalTopologyDecodeBHist (formalTopologyEventAtDefault 10 ef)))

private theorem FormalTopologyTasteGate_single_carrier_alignment_round_trip
    (x : FormalTopologyUp) :
    formalTopologyFromEventFlow (formalTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M B U R D S I H C P N =>
      change
        some
          (FormalTopologyUp.mk
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist M))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist B))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist U))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist R))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist D))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist S))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist I))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist H))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist C))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist P))
            (formalTopologyDecodeBHist (formalTopologyEncodeBHist N))) =
          some (FormalTopologyUp.mk M B U R D S I H C P N)
      rw [FormalTopologyTasteGate_single_carrier_alignment_decode M,
        FormalTopologyTasteGate_single_carrier_alignment_decode B,
        FormalTopologyTasteGate_single_carrier_alignment_decode U,
        FormalTopologyTasteGate_single_carrier_alignment_decode R,
        FormalTopologyTasteGate_single_carrier_alignment_decode D,
        FormalTopologyTasteGate_single_carrier_alignment_decode S,
        FormalTopologyTasteGate_single_carrier_alignment_decode I,
        FormalTopologyTasteGate_single_carrier_alignment_decode H,
        FormalTopologyTasteGate_single_carrier_alignment_decode C,
        FormalTopologyTasteGate_single_carrier_alignment_decode P,
        FormalTopologyTasteGate_single_carrier_alignment_decode N]

private theorem FormalTopologyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FormalTopologyUp} :
    formalTopologyToEventFlow x = formalTopologyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalTopologyFromEventFlow (formalTopologyToEventFlow x) =
        formalTopologyFromEventFlow (formalTopologyToEventFlow y) :=
    congrArg formalTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FormalTopologyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FormalTopologyTasteGate_single_carrier_alignment_round_trip y)))

instance formalTopologyBHistCarrier : BHistCarrier FormalTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalTopologyToEventFlow
  fromEventFlow := formalTopologyFromEventFlow

instance formalTopologyChapterTasteGate : ChapterTasteGate FormalTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change formalTopologyFromEventFlow (formalTopologyToEventFlow x) = some x
    exact FormalTopologyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FormalTopologyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FormalTopologyTasteGate_single_carrier_alignment :
    (∀ h : BHist, formalTopologyDecodeBHist (formalTopologyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier FormalTopologyUp) ∧
        Nonempty (ChapterTasteGate FormalTopologyUp) ∧
          formalTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FormalTopologyTasteGate_single_carrier_alignment_decode,
      ⟨formalTopologyBHistCarrier⟩,
      ⟨formalTopologyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FormalTopologyUp
