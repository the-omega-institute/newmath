import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FullAxisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FullAxisUp : Type where
  | mk (source boundary ledger route provenance name : BHist) : FullAxisUp
  deriving DecidableEq

def fullAxisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: fullAxisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: fullAxisEncodeBHist h

def fullAxisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (fullAxisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (fullAxisDecodeBHist tail)

private theorem fullAxisDecode_encode_bhist :
    ∀ h : BHist, fullAxisDecodeBHist (fullAxisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def fullAxisRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => fullAxisRawAt n rest

def fullAxisFields : FullAxisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FullAxisUp.mk source boundary ledger route provenance name =>
      [source, boundary, ledger, route, provenance, name]

def fullAxisToEventFlow : FullAxisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FullAxisUp.mk source boundary ledger route provenance name =>
      [fullAxisEncodeBHist source,
        fullAxisEncodeBHist boundary,
        fullAxisEncodeBHist ledger,
        fullAxisEncodeBHist route,
        fullAxisEncodeBHist provenance,
        fullAxisEncodeBHist name]

def fullAxisFromEventFlow (ef : EventFlow) : Option FullAxisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FullAxisUp.mk
      (fullAxisDecodeBHist (fullAxisRawAt 0 ef))
      (fullAxisDecodeBHist (fullAxisRawAt 1 ef))
      (fullAxisDecodeBHist (fullAxisRawAt 2 ef))
      (fullAxisDecodeBHist (fullAxisRawAt 3 ef))
      (fullAxisDecodeBHist (fullAxisRawAt 4 ef))
      (fullAxisDecodeBHist (fullAxisRawAt 5 ef)))

private theorem fullAxis_mk_congr
    {source source' boundary boundary' ledger ledger' route route' provenance provenance'
      name name' : BHist}
    (hSource : source' = source)
    (hBoundary : boundary' = boundary)
    (hLedger : ledger' = ledger)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    FullAxisUp.mk source' boundary' ledger' route' provenance' name' =
      FullAxisUp.mk source boundary ledger route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hBoundary
  cases hLedger
  cases hRoute
  cases hProvenance
  cases hName
  rfl

private theorem fullAxis_round_trip :
    ∀ x : FullAxisUp, fullAxisFromEventFlow (fullAxisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source boundary ledger route provenance name =>
      exact
        congrArg some
          (fullAxis_mk_congr
            (fullAxisDecode_encode_bhist source)
            (fullAxisDecode_encode_bhist boundary)
            (fullAxisDecode_encode_bhist ledger)
            (fullAxisDecode_encode_bhist route)
            (fullAxisDecode_encode_bhist provenance)
            (fullAxisDecode_encode_bhist name))

private theorem fullAxisToEventFlow_injective {x y : FullAxisUp} :
    fullAxisToEventFlow x = fullAxisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      fullAxisFromEventFlow (fullAxisToEventFlow x) =
        fullAxisFromEventFlow (fullAxisToEventFlow y) :=
    congrArg fullAxisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (fullAxis_round_trip x).symm
      (Eq.trans hread (fullAxis_round_trip y)))

private theorem fullAxis_field_faithful :
    ∀ x y : FullAxisUp, fullAxisFields x = fullAxisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source1 boundary1 ledger1 route1 provenance1 name1 =>
      cases y with
      | mk source2 boundary2 ledger2 route2 provenance2 name2 =>
          cases hfields
          rfl

instance fullAxisBHistCarrier : BHistCarrier FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := fullAxisToEventFlow
  fromEventFlow := fullAxisFromEventFlow

instance fullAxisChapterTasteGate : ChapterTasteGate FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change fullAxisFromEventFlow (fullAxisToEventFlow x) = some x
    exact fullAxis_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (fullAxisToEventFlow_injective heq)

instance fullAxisFieldFaithful : FieldFaithful FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fullAxisFields
  field_faithful := fullAxis_field_faithful

instance fullAxisNontrivial : Nontrivial FullAxisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FullAxisUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FullAxisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FullAxisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fullAxisChapterTasteGate

theorem FullAxisTasteGate_completion_sibling_separation :
    (∀ h : BHist, fullAxisDecodeBHist (fullAxisEncodeBHist h) = h) ∧
      (∀ x : FullAxisUp, fullAxisFromEventFlow (fullAxisToEventFlow x) = some x) ∧
        (∀ x y : FullAxisUp, fullAxisToEventFlow x = fullAxisToEventFlow y → x = y) ∧
          fullAxisToEventFlow
              (FullAxisUp.mk BHist.Empty (BHist.e1 (BHist.e0 BHist.Empty)) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty) ≠ [] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨fullAxisDecode_encode_bhist,
      ⟨fullAxis_round_trip,
        ⟨fun _x _y heq => fullAxisToEventFlow_injective heq, by
          intro h
          cases h⟩⟩⟩

end BEDC.Derived.FullAxisUp
