import BEDC.Derived.MetaCICParallelDiamondFrontierUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICParallelDiamondFrontierUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def metacicParallelDiamondFrontierEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicParallelDiamondFrontierEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicParallelDiamondFrontierEncodeBHist h

def metacicParallelDiamondFrontierDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicParallelDiamondFrontierDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicParallelDiamondFrontierDecodeBHist tail)

private theorem metacicParallelDiamondFrontier_decode_encode :
    ∀ h : BHist,
      metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metacicParallelDiamondFrontierFields :
    MetaCICParallelDiamondFrontierUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICParallelDiamondFrontierUp.mk premise peak join residual checker fragment
      bounded obstruction transport replay provenance localName =>
      [premise, peak, join, residual, checker, fragment, bounded, obstruction,
        transport, replay, provenance, localName]

def metacicParallelDiamondFrontierToEventFlow :
    MetaCICParallelDiamondFrontierUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metacicParallelDiamondFrontierFields x).map
      metacicParallelDiamondFrontierEncodeBHist

private def metacicParallelDiamondFrontierEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      metacicParallelDiamondFrontierEventAtDefault index rest

def metacicParallelDiamondFrontierFromEventFlow
    (ef : EventFlow) : Option MetaCICParallelDiamondFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MetaCICParallelDiamondFrontierUp.mk
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 0 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 1 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 2 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 3 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 4 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 5 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 6 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 7 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 8 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 9 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 10 ef))
      (metacicParallelDiamondFrontierDecodeBHist
        (metacicParallelDiamondFrontierEventAtDefault 11 ef)))

private theorem metacicParallelDiamondFrontier_round_trip
    (x : MetaCICParallelDiamondFrontierUp) :
    metacicParallelDiamondFrontierFromEventFlow
      (metacicParallelDiamondFrontierToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk premise peak join residual checker fragment bounded obstruction transport replay
      provenance localName =>
      change
        some
          (MetaCICParallelDiamondFrontierUp.mk
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist premise))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist peak))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist join))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist residual))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist checker))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist fragment))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist bounded))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist obstruction))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist transport))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist replay))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist provenance))
            (metacicParallelDiamondFrontierDecodeBHist
              (metacicParallelDiamondFrontierEncodeBHist localName))) =
          some (MetaCICParallelDiamondFrontierUp.mk premise peak join residual checker
            fragment bounded obstruction transport replay provenance localName)
      rw [metacicParallelDiamondFrontier_decode_encode premise,
        metacicParallelDiamondFrontier_decode_encode peak,
        metacicParallelDiamondFrontier_decode_encode join,
        metacicParallelDiamondFrontier_decode_encode residual,
        metacicParallelDiamondFrontier_decode_encode checker,
        metacicParallelDiamondFrontier_decode_encode fragment,
        metacicParallelDiamondFrontier_decode_encode bounded,
        metacicParallelDiamondFrontier_decode_encode obstruction,
        metacicParallelDiamondFrontier_decode_encode transport,
        metacicParallelDiamondFrontier_decode_encode replay,
        metacicParallelDiamondFrontier_decode_encode provenance,
        metacicParallelDiamondFrontier_decode_encode localName]

private theorem metacicParallelDiamondFrontierToEventFlow_injective
    {x y : MetaCICParallelDiamondFrontierUp} :
    metacicParallelDiamondFrontierToEventFlow x =
      metacicParallelDiamondFrontierToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicParallelDiamondFrontierFromEventFlow
          (metacicParallelDiamondFrontierToEventFlow x) =
        metacicParallelDiamondFrontierFromEventFlow
          (metacicParallelDiamondFrontierToEventFlow y) :=
    congrArg metacicParallelDiamondFrontierFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (metacicParallelDiamondFrontier_round_trip x).symm
      (Eq.trans hread (metacicParallelDiamondFrontier_round_trip y)))

private theorem metacicParallelDiamondFrontier_fields_faithful :
    ∀ x y : MetaCICParallelDiamondFrontierUp,
      metacicParallelDiamondFrontierFields x =
        metacicParallelDiamondFrontierFields y →
          x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk premise₁ peak₁ join₁ residual₁ checker₁ fragment₁ bounded₁ obstruction₁
      transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk premise₂ peak₂ join₂ residual₂ checker₂ fragment₂ bounded₂ obstruction₂
          transport₂ replay₂ provenance₂ localName₂ =>
          cases hfields
          rfl

instance metacicParallelDiamondFrontierBHistCarrier :
    BHistCarrier MetaCICParallelDiamondFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicParallelDiamondFrontierToEventFlow
  fromEventFlow := metacicParallelDiamondFrontierFromEventFlow

instance metacicParallelDiamondFrontierChapterTasteGate :
    ChapterTasteGate MetaCICParallelDiamondFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicParallelDiamondFrontierFromEventFlow
        (metacicParallelDiamondFrontierToEventFlow x) = some x
    exact metacicParallelDiamondFrontier_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicParallelDiamondFrontierToEventFlow_injective heq)

instance metacicParallelDiamondFrontierFieldFaithful :
    FieldFaithful MetaCICParallelDiamondFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicParallelDiamondFrontierFields
  field_faithful := metacicParallelDiamondFrontier_fields_faithful

instance metacicParallelDiamondFrontierNontrivial :
    BEDC.Meta.TasteGate.Nontrivial MetaCICParallelDiamondFrontierUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICParallelDiamondFrontierUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      MetaCICParallelDiamondFrontierUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICParallelDiamondFrontierUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicParallelDiamondFrontierChapterTasteGate

end BEDC.Derived.MetaCICParallelDiamondFrontierUp
