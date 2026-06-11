import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BooleanTriggerLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BooleanTriggerLatticeUp : Type where
  | mk
      (bool support rank join meet observed transport route provenance name : BHist) :
      BooleanTriggerLatticeUp
  deriving DecidableEq

def booleanTriggerLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: booleanTriggerLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: booleanTriggerLatticeEncodeBHist h

def booleanTriggerLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (booleanTriggerLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (booleanTriggerLatticeDecodeBHist tail)

private theorem booleanTriggerLattice_decode_encode_bhist :
    ∀ h : BHist,
      booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def booleanTriggerLatticeFields : BooleanTriggerLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BooleanTriggerLatticeUp.mk bool support rank join meet observed transport route
      provenance name =>
      [bool, support, rank, join, meet, observed, transport, route, provenance, name]

def booleanTriggerLatticeToEventFlow : BooleanTriggerLatticeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (booleanTriggerLatticeFields x).map booleanTriggerLatticeEncodeBHist

private def booleanTriggerLatticeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => booleanTriggerLatticeEventAtDefault index rest

def booleanTriggerLatticeFromEventFlow (ef : EventFlow) : Option BooleanTriggerLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BooleanTriggerLatticeUp.mk
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 0 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 1 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 2 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 3 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 4 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 5 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 6 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 7 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 8 ef))
      (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEventAtDefault 9 ef)))

private theorem booleanTriggerLattice_round_trip :
    ∀ x : BooleanTriggerLatticeUp,
      booleanTriggerLatticeFromEventFlow (booleanTriggerLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bool support rank join meet observed transport route provenance name =>
      change
        some
          (BooleanTriggerLatticeUp.mk
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist bool))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist support))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist rank))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist join))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist meet))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist observed))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist transport))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist route))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist provenance))
            (booleanTriggerLatticeDecodeBHist (booleanTriggerLatticeEncodeBHist name))) =
          some
            (BooleanTriggerLatticeUp.mk bool support rank join meet observed transport route
              provenance name)
      rw [booleanTriggerLattice_decode_encode_bhist bool,
        booleanTriggerLattice_decode_encode_bhist support,
        booleanTriggerLattice_decode_encode_bhist rank,
        booleanTriggerLattice_decode_encode_bhist join,
        booleanTriggerLattice_decode_encode_bhist meet,
        booleanTriggerLattice_decode_encode_bhist observed,
        booleanTriggerLattice_decode_encode_bhist transport,
        booleanTriggerLattice_decode_encode_bhist route,
        booleanTriggerLattice_decode_encode_bhist provenance,
        booleanTriggerLattice_decode_encode_bhist name]

private theorem booleanTriggerLatticeToEventFlow_injective
    {x y : BooleanTriggerLatticeUp} :
    booleanTriggerLatticeToEventFlow x = booleanTriggerLatticeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      booleanTriggerLatticeFromEventFlow (booleanTriggerLatticeToEventFlow x) =
        booleanTriggerLatticeFromEventFlow (booleanTriggerLatticeToEventFlow y) :=
    congrArg booleanTriggerLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (booleanTriggerLattice_round_trip x).symm
      (Eq.trans hread (booleanTriggerLattice_round_trip y)))

private theorem booleanTriggerLattice_fields_faithful :
    ∀ x y : BooleanTriggerLatticeUp,
      booleanTriggerLatticeFields x = booleanTriggerLatticeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk bool1 support1 rank1 join1 meet1 observed1 transport1 route1 provenance1 name1 =>
      cases y with
      | mk bool2 support2 rank2 join2 meet2 observed2 transport2 route2 provenance2 name2 =>
          cases hfields
          rfl

instance booleanTriggerLatticeBHistCarrier : BHistCarrier BooleanTriggerLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := booleanTriggerLatticeToEventFlow
  fromEventFlow := booleanTriggerLatticeFromEventFlow

instance booleanTriggerLatticeChapterTasteGate :
    ChapterTasteGate BooleanTriggerLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change booleanTriggerLatticeFromEventFlow (booleanTriggerLatticeToEventFlow x) = some x
    exact booleanTriggerLattice_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (booleanTriggerLatticeToEventFlow_injective heq)

instance booleanTriggerLatticeFieldFaithful : FieldFaithful BooleanTriggerLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := booleanTriggerLatticeFields
  field_faithful := booleanTriggerLattice_fields_faithful

private def booleanTriggerLatticeNontrivialDef : Nontrivial BooleanTriggerLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BooleanTriggerLatticeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BooleanTriggerLatticeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance booleanTriggerLatticeNontrivial : Nontrivial BooleanTriggerLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  booleanTriggerLatticeNontrivialDef

theorem BooleanTriggerLatticeTasteGate_single_carrier_alignment
    (bool support rank join meet observed transport route provenance name : BHist) :
    booleanTriggerLatticeFields
        (BooleanTriggerLatticeUp.mk bool support rank join meet observed transport route
          provenance name) =
      [bool, support, rank, join, meet, observed, transport, route, provenance, name] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  rfl

end BEDC.Derived.BooleanTriggerLatticeUp
