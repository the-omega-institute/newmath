import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StoneWeierstrassUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StoneWeierstrassUp : Type where
  | mk (tag : BMark)
      (source algebra separates compactApprox dyadicLedger stream realSeal transport replay
        provenance localName : BHist) :
      StoneWeierstrassUp
  deriving DecidableEq

def stoneWeierstrassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stoneWeierstrassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stoneWeierstrassEncodeBHist h

def stoneWeierstrassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stoneWeierstrassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stoneWeierstrassDecodeBHist tail)

private theorem StoneWeierstrassTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stoneWeierstrassEncodeTag : BMark → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BMark.b0 => [BMark.b0]
  | BMark.b1 => [BMark.b1]

def stoneWeierstrassDecodeTag : RawEvent → BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BMark.b1 :: _ => BMark.b1
  | _ => BMark.b0

private theorem StoneWeierstrassTasteGate_single_carrier_alignment_decode_tag :
    ∀ tag : BMark, stoneWeierstrassDecodeTag (stoneWeierstrassEncodeTag tag) = tag := by
  -- BEDC touchpoint anchor: BHist BMark
  intro tag
  cases tag <;> rfl

def stoneWeierstrassTagBHist : BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BMark.b0 => BHist.Empty
  | BMark.b1 => BHist.e1 BHist.Empty

def stoneWeierstrassFields : StoneWeierstrassUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StoneWeierstrassUp.mk tag source algebra separates compactApprox dyadicLedger stream
      realSeal transport replay provenance localName =>
      [stoneWeierstrassTagBHist tag, source, algebra, separates, compactApprox, dyadicLedger,
        stream, realSeal, transport, replay, provenance, localName]

def stoneWeierstrassToEventFlow : StoneWeierstrassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | StoneWeierstrassUp.mk tag source algebra separates compactApprox dyadicLedger stream
      realSeal transport replay provenance localName =>
      [stoneWeierstrassEncodeTag tag,
        stoneWeierstrassEncodeBHist source,
        stoneWeierstrassEncodeBHist algebra,
        stoneWeierstrassEncodeBHist separates,
        stoneWeierstrassEncodeBHist compactApprox,
        stoneWeierstrassEncodeBHist dyadicLedger,
        stoneWeierstrassEncodeBHist stream,
        stoneWeierstrassEncodeBHist realSeal,
        stoneWeierstrassEncodeBHist transport,
        stoneWeierstrassEncodeBHist replay,
        stoneWeierstrassEncodeBHist provenance,
        stoneWeierstrassEncodeBHist localName]

private def stoneWeierstrassRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => stoneWeierstrassRawAt index rest

private def stoneWeierstrassLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _ :: rest => stoneWeierstrassLengthEq index rest

def stoneWeierstrassFromEventFlow : EventFlow → Option StoneWeierstrassUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match stoneWeierstrassLengthEq 12 flow with
      | true =>
          some
            (StoneWeierstrassUp.mk
              (stoneWeierstrassDecodeTag (stoneWeierstrassRawAt 0 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 1 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 2 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 3 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 4 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 5 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 6 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 7 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 8 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 9 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 10 flow))
              (stoneWeierstrassDecodeBHist (stoneWeierstrassRawAt 11 flow)))
      | false => none

private theorem StoneWeierstrassTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StoneWeierstrassUp,
      stoneWeierstrassFromEventFlow (stoneWeierstrassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tag source algebra separates compactApprox dyadicLedger stream realSeal transport replay
      provenance localName =>
      change
        some
          (StoneWeierstrassUp.mk
            (stoneWeierstrassDecodeTag (stoneWeierstrassEncodeTag tag))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist source))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist algebra))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist separates))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist compactApprox))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist dyadicLedger))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist stream))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist realSeal))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist transport))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist replay))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist provenance))
            (stoneWeierstrassDecodeBHist (stoneWeierstrassEncodeBHist localName))) =
          some
            (StoneWeierstrassUp.mk tag source algebra separates compactApprox dyadicLedger
              stream realSeal transport replay provenance localName)
      rw [StoneWeierstrassTasteGate_single_carrier_alignment_decode_tag tag,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode source,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode algebra,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode separates,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode compactApprox,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode dyadicLedger,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode stream,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode realSeal,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode transport,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode replay,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode provenance,
        StoneWeierstrassTasteGate_single_carrier_alignment_decode localName]

private theorem StoneWeierstrassToEventFlow_injective {x y : StoneWeierstrassUp} :
    stoneWeierstrassToEventFlow x = stoneWeierstrassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stoneWeierstrassFromEventFlow (stoneWeierstrassToEventFlow x) =
        stoneWeierstrassFromEventFlow (stoneWeierstrassToEventFlow y) :=
    congrArg stoneWeierstrassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StoneWeierstrassTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (StoneWeierstrassTasteGate_single_carrier_alignment_round_trip y)))

private theorem StoneWeierstrassTasteGate_single_carrier_alignment_fields :
    ∀ x y : StoneWeierstrassUp,
      stoneWeierstrassFields x = stoneWeierstrassFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tag₁ source₁ algebra₁ separates₁ compactApprox₁ dyadicLedger₁ stream₁ realSeal₁
      transport₁ replay₁ provenance₁ localName₁ =>
      cases y with
      | mk tag₂ source₂ algebra₂ separates₂ compactApprox₂ dyadicLedger₂ stream₂ realSeal₂
          transport₂ replay₂ provenance₂ localName₂ =>
          cases tag₁ <;> cases tag₂ <;> cases hfields <;> rfl

instance stoneWeierstrassBHistCarrier : BHistCarrier StoneWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stoneWeierstrassToEventFlow
  fromEventFlow := stoneWeierstrassFromEventFlow

instance stoneWeierstrassChapterTasteGate : ChapterTasteGate StoneWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change stoneWeierstrassFromEventFlow (stoneWeierstrassToEventFlow x) = some x
    exact StoneWeierstrassTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StoneWeierstrassToEventFlow_injective heq)

instance stoneWeierstrassFieldFaithful : FieldFaithful StoneWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := stoneWeierstrassFields
  field_faithful := StoneWeierstrassTasteGate_single_carrier_alignment_fields

instance stoneWeierstrassNontrivial : Nontrivial StoneWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StoneWeierstrassUp.mk BMark.b0 BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StoneWeierstrassUp.mk BMark.b1 BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate StoneWeierstrassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stoneWeierstrassChapterTasteGate

def taste_gate_witness : FieldFaithful StoneWeierstrassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stoneWeierstrassFieldFaithful

end BEDC.Derived.StoneWeierstrassUp
