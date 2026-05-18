import BEDC.Derived.ZCarryUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZCarryUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived.AxisZeckendorf.Carry
open BEDC.Derived.AxisZeckendorf.Zeckendorf

inductive ZCarryUp : Type where
  | mk
      (source target generated sourceLedger targetLedger boundary continuation provenance
        nameCert : BHist) : ZCarryUp
  deriving DecidableEq

def zCarryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zCarryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zCarryEncodeBHist h

def zCarryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zCarryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zCarryDecodeBHist tail)

private theorem zCarryDecode_encode_bhist :
    ∀ h : BHist, zCarryDecodeBHist (zCarryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem zCarry_mk_congr
    {source source' target target' generated generated' sourceLedger sourceLedger'
      targetLedger targetLedger' boundary boundary' continuation continuation'
      provenance provenance' nameCert nameCert' : BHist}
    (hSource : source' = source)
    (hTarget : target' = target)
    (hGenerated : generated' = generated)
    (hSourceLedger : sourceLedger' = sourceLedger)
    (hTargetLedger : targetLedger' = targetLedger)
    (hBoundary : boundary' = boundary)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    ZCarryUp.mk source' target' generated' sourceLedger' targetLedger' boundary'
        continuation' provenance' nameCert' =
      ZCarryUp.mk source target generated sourceLedger targetLedger boundary continuation
        provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTarget
  cases hGenerated
  cases hSourceLedger
  cases hTargetLedger
  cases hBoundary
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

def zCarryToEventFlow : ZCarryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ZCarryUp.mk source target generated sourceLedger targetLedger boundary continuation
      provenance nameCert =>
      [[BMark.b0],
        zCarryEncodeBHist source,
        [BMark.b1, BMark.b0],
        zCarryEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        zCarryEncodeBHist generated,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zCarryEncodeBHist sourceLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zCarryEncodeBHist targetLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zCarryEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        zCarryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        zCarryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        zCarryEncodeBHist nameCert]

def zCarryFromEventFlow : EventFlow → Option ZCarryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: source :: _tag1 :: target :: _tag2 :: generated :: _tag3 ::
      sourceLedger :: _tag4 :: targetLedger :: _tag5 :: boundary :: _tag6 ::
        continuation :: _tag7 :: provenance :: _tag8 :: nameCert :: [] =>
      some
        (ZCarryUp.mk
          (zCarryDecodeBHist source)
          (zCarryDecodeBHist target)
          (zCarryDecodeBHist generated)
          (zCarryDecodeBHist sourceLedger)
          (zCarryDecodeBHist targetLedger)
          (zCarryDecodeBHist boundary)
          (zCarryDecodeBHist continuation)
          (zCarryDecodeBHist provenance)
          (zCarryDecodeBHist nameCert))
  | _ => none

private theorem zCarry_round_trip :
    ∀ x : ZCarryUp, zCarryFromEventFlow (zCarryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target generated sourceLedger targetLedger boundary continuation provenance
      nameCert =>
      change
        some
          (ZCarryUp.mk
            (zCarryDecodeBHist (zCarryEncodeBHist source))
            (zCarryDecodeBHist (zCarryEncodeBHist target))
            (zCarryDecodeBHist (zCarryEncodeBHist generated))
            (zCarryDecodeBHist (zCarryEncodeBHist sourceLedger))
            (zCarryDecodeBHist (zCarryEncodeBHist targetLedger))
            (zCarryDecodeBHist (zCarryEncodeBHist boundary))
            (zCarryDecodeBHist (zCarryEncodeBHist continuation))
            (zCarryDecodeBHist (zCarryEncodeBHist provenance))
            (zCarryDecodeBHist (zCarryEncodeBHist nameCert))) =
          some
            (ZCarryUp.mk source target generated sourceLedger targetLedger boundary
              continuation provenance nameCert)
      exact
        congrArg some
          (zCarry_mk_congr
            (zCarryDecode_encode_bhist source)
            (zCarryDecode_encode_bhist target)
            (zCarryDecode_encode_bhist generated)
            (zCarryDecode_encode_bhist sourceLedger)
            (zCarryDecode_encode_bhist targetLedger)
            (zCarryDecode_encode_bhist boundary)
            (zCarryDecode_encode_bhist continuation)
            (zCarryDecode_encode_bhist provenance)
            (zCarryDecode_encode_bhist nameCert))

private theorem zCarryToEventFlow_injective {x y : ZCarryUp} :
    zCarryToEventFlow x = zCarryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zCarryFromEventFlow (zCarryToEventFlow x) =
        zCarryFromEventFlow (zCarryToEventFlow y) :=
    congrArg zCarryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zCarry_round_trip x).symm (Eq.trans hread (zCarry_round_trip y)))

instance zCarryBHistCarrier : BHistCarrier ZCarryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zCarryToEventFlow
  fromEventFlow := zCarryFromEventFlow

instance zCarryChapterTasteGate : ChapterTasteGate ZCarryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change zCarryFromEventFlow (zCarryToEventFlow x) = some x
    exact zCarry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zCarryToEventFlow_injective heq)

def zCarryFields : ZCarryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZCarryUp.mk source target generated sourceLedger targetLedger boundary continuation
      provenance nameCert =>
      [source, target, generated, sourceLedger, targetLedger, boundary, continuation,
        provenance, nameCert]

private theorem zCarry_fields_faithful :
    ∀ x y : ZCarryUp, zCarryFields x = zCarryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source target generated sourceLedger targetLedger boundary continuation provenance
      nameCert =>
      cases y with
      | mk source' target' generated' sourceLedger' targetLedger' boundary' continuation'
          provenance' nameCert' =>
          cases hfields
          rfl

instance zCarryFieldFaithful : FieldFaithful ZCarryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := zCarryFields
  field_faithful := zCarry_fields_faithful

instance zCarryNontrivial : Nontrivial ZCarryUp where
  witness_pair :=
    ⟨ZCarryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ZCarryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem ZCarryNormalTargetLedger {source target carryRoute : BHist}
    (generated : ZCarry source target) (carryReadback : Cont source target carryRoute) :
    source = word_011 ∧ target = word_100 ∧ ZCarrySourceSpec source ∧ ZNormal target ∧
      ¬ hsame source target ∧ Cont source target carryRoute := by
  -- BEDC touchpoint anchor: BHist BMark hsame Cont
  cases generated with
  | base =>
      exact
        ⟨rfl, rfl, znormal_word_011_absurd, znormal_word_100, zCarry_011_100_not_hsame,
          carryReadback⟩

end BEDC.Derived.ZCarryUp.TasteGate
