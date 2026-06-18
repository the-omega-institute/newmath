import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareTriangleDefectUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareTriangleDefectUp : Type where
  | mk (D G M X R H C P N : BHist) : PoincareTriangleDefectUp
  deriving DecidableEq

def poincareTriangleDefectEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareTriangleDefectEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareTriangleDefectEncodeBHist h

def poincareTriangleDefectDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareTriangleDefectDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareTriangleDefectDecodeBHist tail)

private theorem PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poincareTriangleDefectFields : PoincareTriangleDefectUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareTriangleDefectUp.mk D G M X R H C P N => [D, G, M, X, R, H, C, P, N]

def poincareTriangleDefectToEventFlow : PoincareTriangleDefectUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareTriangleDefectFields x).map poincareTriangleDefectEncodeBHist

private def poincareTriangleDefectEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => poincareTriangleDefectEventAt index rest

def poincareTriangleDefectFromEventFlow (ef : EventFlow) :
    Option PoincareTriangleDefectUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PoincareTriangleDefectUp.mk
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 0 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 1 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 2 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 3 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 4 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 5 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 6 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 7 ef))
      (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEventAt 8 ef)))

private theorem PoincareTriangleDefectTasteGate_single_carrier_alignment_round_trip
    (x : PoincareTriangleDefectUp) :
    poincareTriangleDefectFromEventFlow (poincareTriangleDefectToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D G M X R H C P N =>
      change
        some
          (PoincareTriangleDefectUp.mk
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist D))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist G))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist M))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist X))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist R))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist H))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist C))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist P))
            (poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist N))) =
          some (PoincareTriangleDefectUp.mk D G M X R H C P N)
      rw [PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode D,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode G,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode M,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode X,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode R,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode H,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode C,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode P,
        PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode N]

private theorem PoincareTriangleDefectTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PoincareTriangleDefectUp} :
    poincareTriangleDefectToEventFlow x = poincareTriangleDefectToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareTriangleDefectFromEventFlow (poincareTriangleDefectToEventFlow x) =
        poincareTriangleDefectFromEventFlow (poincareTriangleDefectToEventFlow y) :=
    congrArg poincareTriangleDefectFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PoincareTriangleDefectTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareTriangleDefectTasteGate_single_carrier_alignment_round_trip y)))

private theorem PoincareTriangleDefectTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : PoincareTriangleDefectUp,
      poincareTriangleDefectFields x = poincareTriangleDefectFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 G1 M1 X1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 G2 M2 X2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance poincareTriangleDefectBHistCarrier : BHistCarrier PoincareTriangleDefectUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareTriangleDefectToEventFlow
  fromEventFlow := poincareTriangleDefectFromEventFlow

instance poincareTriangleDefectChapterTasteGate :
    ChapterTasteGate PoincareTriangleDefectUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change poincareTriangleDefectFromEventFlow (poincareTriangleDefectToEventFlow x) = some x
    exact PoincareTriangleDefectTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PoincareTriangleDefectTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance poincareTriangleDefectFieldFaithful : FieldFaithful PoincareTriangleDefectUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := poincareTriangleDefectFields
  field_faithful := PoincareTriangleDefectTasteGate_single_carrier_alignment_fields_faithful

instance poincareTriangleDefectNontrivial :
    BEDC.Meta.TasteGate.Nontrivial PoincareTriangleDefectUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PoincareTriangleDefectUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PoincareTriangleDefectUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PoincareTriangleDefectTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PoincareTriangleDefectUp) ∧
      Nonempty (ChapterTasteGate PoincareTriangleDefectUp) ∧
        (∀ h : BHist,
          poincareTriangleDefectDecodeBHist (poincareTriangleDefectEncodeBHist h) = h) ∧
          (∀ x : PoincareTriangleDefectUp,
            poincareTriangleDefectFromEventFlow (poincareTriangleDefectToEventFlow x) = some x) ∧
            poincareTriangleDefectEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨Nonempty.intro poincareTriangleDefectBHistCarrier,
      Nonempty.intro poincareTriangleDefectChapterTasteGate,
      PoincareTriangleDefectTasteGate_single_carrier_alignment_decode_encode,
      PoincareTriangleDefectTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.PoincareTriangleDefectUp
