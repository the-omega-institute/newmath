import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BinaryTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BinaryTreeUp : Type where
  | mk (root nodeSpine leftIncidence rightIncidence transport replay provenance localName :
      BHist) : BinaryTreeUp
  deriving DecidableEq

def binaryTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: binaryTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: binaryTreeEncodeBHist h

def binaryTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (binaryTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (binaryTreeDecodeBHist tail)

private theorem BinaryTreeTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, binaryTreeDecodeBHist (binaryTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BinaryTreeTasteGate_single_carrier_alignment_fields :
    BinaryTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BinaryTreeUp.mk root nodeSpine leftIncidence rightIncidence transport replay provenance
      localName =>
      [root, nodeSpine, leftIncidence, rightIncidence, transport, replay, provenance, localName]

def BinaryTreeTasteGate_single_carrier_alignment_toEventFlow :
    BinaryTreeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (BinaryTreeTasteGate_single_carrier_alignment_fields x).map binaryTreeEncodeBHist

def BinaryTreeTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option BinaryTreeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
  | root :: nodeSpine :: leftIncidence :: rightIncidence :: transport :: replay :: provenance ::
      localName :: [] =>
      some
        (BinaryTreeUp.mk
          (binaryTreeDecodeBHist root)
          (binaryTreeDecodeBHist nodeSpine)
          (binaryTreeDecodeBHist leftIncidence)
          (binaryTreeDecodeBHist rightIncidence)
          (binaryTreeDecodeBHist transport)
          (binaryTreeDecodeBHist replay)
          (binaryTreeDecodeBHist provenance)
          (binaryTreeDecodeBHist localName))
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def BinaryTreeTasteGate_single_carrier_alignment_carrier :
    BHistCarrier BinaryTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BinaryTreeTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BinaryTreeTasteGate_single_carrier_alignment_fromEventFlow

instance BinaryTreeTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BinaryTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BinaryTreeTasteGate_single_carrier_alignment_carrier

private theorem BinaryTreeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BinaryTreeUp,
      @BHistCarrier.fromEventFlow BinaryTreeUp
          BinaryTreeTasteGate_single_carrier_alignment_carrier
          (@BHistCarrier.toEventFlow BinaryTreeUp
            BinaryTreeTasteGate_single_carrier_alignment_carrier x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk root nodeSpine leftIncidence rightIncidence transport replay provenance localName =>
      change
        some
            (BinaryTreeUp.mk
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist root))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist nodeSpine))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist leftIncidence))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist rightIncidence))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist transport))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist replay))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist provenance))
              (binaryTreeDecodeBHist (binaryTreeEncodeBHist localName))) =
          some
            (BinaryTreeUp.mk root nodeSpine leftIncidence rightIncidence transport replay
              provenance localName)
      rw [BinaryTreeTasteGate_single_carrier_alignment_decode_encode root,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode nodeSpine,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode leftIncidence,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode rightIncidence,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode transport,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode replay,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode provenance,
        BinaryTreeTasteGate_single_carrier_alignment_decode_encode localName]

private theorem BinaryTreeTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BinaryTreeUp} :
    @BHistCarrier.toEventFlow BinaryTreeUp
        BinaryTreeTasteGate_single_carrier_alignment_carrier x =
      @BHistCarrier.toEventFlow BinaryTreeUp
        BinaryTreeTasteGate_single_carrier_alignment_carrier y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          @BHistCarrier.fromEventFlow BinaryTreeUp
              BinaryTreeTasteGate_single_carrier_alignment_carrier
              (@BHistCarrier.toEventFlow BinaryTreeUp
                BinaryTreeTasteGate_single_carrier_alignment_carrier x) :=
        (BinaryTreeTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          @BHistCarrier.fromEventFlow BinaryTreeUp
              BinaryTreeTasteGate_single_carrier_alignment_carrier
              (@BHistCarrier.toEventFlow BinaryTreeUp
                BinaryTreeTasteGate_single_carrier_alignment_carrier y) :=
        congrArg
          (@BHistCarrier.fromEventFlow BinaryTreeUp
            BinaryTreeTasteGate_single_carrier_alignment_carrier) hxy
      _ = some y := BinaryTreeTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

def BinaryTreeTasteGate_single_carrier_alignment_gate :
    @ChapterTasteGate BinaryTreeUp BinaryTreeTasteGate_single_carrier_alignment_carrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact BinaryTreeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BinaryTreeTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance BinaryTreeTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BinaryTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BinaryTreeTasteGate_single_carrier_alignment_gate

theorem BinaryTreeTasteGate_single_carrier_alignment :
    (forall h : BHist, binaryTreeDecodeBHist (binaryTreeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BinaryTreeUp) ∧
      Nonempty (ChapterTasteGate BinaryTreeUp) ∧
      binaryTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BinaryTreeTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨BinaryTreeTasteGate_single_carrier_alignment_carrier⟩,
        ⟨⟨BinaryTreeTasteGate_single_carrier_alignment_gate⟩, rfl⟩⟩⟩

end BEDC.Derived.BinaryTreeUp
