import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CalkinWilfTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CalkinWilfTreeUp : Type where
  | mk (address rationalReadback leftChild rightChild sternBrocot farey transports routes
      provenance name : BHist) : CalkinWilfTreeUp
  deriving DecidableEq

def calkinWilfTreeEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: calkinWilfTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: calkinWilfTreeEncodeBHist h

def calkinWilfTreeDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (calkinWilfTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (calkinWilfTreeDecodeBHist tail)

private theorem calkinWilfTree_decode_encode :
    ∀ h : BHist, calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def calkinWilfTreeFields : CalkinWilfTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CalkinWilfTreeUp.mk address rationalReadback leftChild rightChild sternBrocot farey
      transports routes provenance name =>
      [address, rationalReadback, leftChild, rightChild, sternBrocot, farey, transports,
        routes, provenance, name]

def calkinWilfTreeToEventFlow : CalkinWilfTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map calkinWilfTreeEncodeBHist (calkinWilfTreeFields x)

def calkinWilfTreeFromEventFlow : EventFlow → Option CalkinWilfTreeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [address, rationalReadback, leftChild, rightChild, sternBrocot, farey, transports,
      routes, provenance, name] =>
      some
        (CalkinWilfTreeUp.mk
          (calkinWilfTreeDecodeBHist address)
          (calkinWilfTreeDecodeBHist rationalReadback)
          (calkinWilfTreeDecodeBHist leftChild)
          (calkinWilfTreeDecodeBHist rightChild)
          (calkinWilfTreeDecodeBHist sternBrocot)
          (calkinWilfTreeDecodeBHist farey)
          (calkinWilfTreeDecodeBHist transports)
          (calkinWilfTreeDecodeBHist routes)
          (calkinWilfTreeDecodeBHist provenance)
          (calkinWilfTreeDecodeBHist name))
  | _ => none

private theorem calkinWilfTree_round_trip :
    ∀ x : CalkinWilfTreeUp,
      calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk address rationalReadback leftChild rightChild sternBrocot farey transports routes
      provenance name =>
      change
        some
          (CalkinWilfTreeUp.mk
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist address))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist rationalReadback))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist leftChild))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist rightChild))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist sternBrocot))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist farey))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist transports))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist routes))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist provenance))
            (calkinWilfTreeDecodeBHist (calkinWilfTreeEncodeBHist name))) =
          some
            (CalkinWilfTreeUp.mk address rationalReadback leftChild rightChild sternBrocot
              farey transports routes provenance name)
      rw [calkinWilfTree_decode_encode address,
        calkinWilfTree_decode_encode rationalReadback,
        calkinWilfTree_decode_encode leftChild,
        calkinWilfTree_decode_encode rightChild,
        calkinWilfTree_decode_encode sternBrocot,
        calkinWilfTree_decode_encode farey,
        calkinWilfTree_decode_encode transports,
        calkinWilfTree_decode_encode routes,
        calkinWilfTree_decode_encode provenance,
        calkinWilfTree_decode_encode name]

private theorem calkinWilfTreeToEventFlow_injective {x y : CalkinWilfTreeUp} :
    calkinWilfTreeToEventFlow x = calkinWilfTreeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow x) =
        calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow y) :=
    congrArg calkinWilfTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (calkinWilfTree_round_trip x).symm
      (Eq.trans hread (calkinWilfTree_round_trip y)))

private theorem calkinWilfTree_fields_faithful :
    ∀ x y : CalkinWilfTreeUp, calkinWilfTreeFields x = calkinWilfTreeFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk address₁ rationalReadback₁ leftChild₁ rightChild₁ sternBrocot₁ farey₁ transports₁
      routes₁ provenance₁ name₁ =>
      cases y with
      | mk address₂ rationalReadback₂ leftChild₂ rightChild₂ sternBrocot₂ farey₂ transports₂
          routes₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance calkinWilfTreeBHistCarrier : BHistCarrier CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := calkinWilfTreeToEventFlow
  fromEventFlow := calkinWilfTreeFromEventFlow

instance calkinWilfTreeChapterTasteGate : ChapterTasteGate CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change calkinWilfTreeFromEventFlow (calkinWilfTreeToEventFlow x) = some x
    exact calkinWilfTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (calkinWilfTreeToEventFlow_injective heq)

instance calkinWilfTreeFieldFaithful : FieldFaithful CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := calkinWilfTreeFields
  field_faithful := calkinWilfTree_fields_faithful

instance calkinWilfTreeNontrivial : Nontrivial CalkinWilfTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CalkinWilfTreeUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CalkinWilfTreeUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CalkinWilfTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  calkinWilfTreeChapterTasteGate

end BEDC.Derived.CalkinWilfTreeUp
