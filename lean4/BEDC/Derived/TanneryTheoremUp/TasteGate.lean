import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TanneryTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TanneryTheoremUp : Type where
  | mk
      (array limit majorant windows readback dyadic endpoint transport route provenance cert :
        BHist) : TanneryTheoremUp
  deriving DecidableEq

def tanneryTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tanneryTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tanneryTheoremEncodeBHist h

def tanneryTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tanneryTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tanneryTheoremDecodeBHist tail)

private theorem TanneryTheoremTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def tanneryTheoremFields : TanneryTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TanneryTheoremUp.mk array limit majorant windows readback dyadic endpoint transport route
      provenance cert =>
      [array, limit, majorant, windows, readback, dyadic, endpoint, transport, route, provenance,
        cert]

def tanneryTheoremToEventFlow : TanneryTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (tanneryTheoremFields x).map tanneryTheoremEncodeBHist

private def tanneryTheoremEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => tanneryTheoremEventAt index rest

def tanneryTheoremFromEventFlow (ef : EventFlow) : Option TanneryTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TanneryTheoremUp.mk
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 0 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 1 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 2 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 3 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 4 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 5 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 6 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 7 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 8 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 9 ef))
      (tanneryTheoremDecodeBHist (tanneryTheoremEventAt 10 ef)))

private theorem TanneryTheoremTasteGate_single_carrier_alignment_round_trip
    (x : TanneryTheoremUp) :
    tanneryTheoremFromEventFlow (tanneryTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk array limit majorant windows readback dyadic endpoint transport route provenance cert =>
      change
        some
          (TanneryTheoremUp.mk
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist array))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist limit))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist majorant))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist windows))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist readback))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist dyadic))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist endpoint))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist transport))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist route))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist provenance))
            (tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist cert))) =
          some
            (TanneryTheoremUp.mk array limit majorant windows readback dyadic endpoint
              transport route provenance cert)
      rw [TanneryTheoremTasteGate_single_carrier_alignment_decode_encode array,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode limit,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode majorant,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode windows,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode readback,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode dyadic,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode endpoint,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode transport,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode route,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode provenance,
        TanneryTheoremTasteGate_single_carrier_alignment_decode_encode cert]

private theorem TanneryTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TanneryTheoremUp} :
    tanneryTheoremToEventFlow x = tanneryTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      tanneryTheoremFromEventFlow (tanneryTheoremToEventFlow x) =
        tanneryTheoremFromEventFlow (tanneryTheoremToEventFlow y) :=
    congrArg tanneryTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TanneryTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TanneryTheoremTasteGate_single_carrier_alignment_round_trip y)))

private theorem TanneryTheoremTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : TanneryTheoremUp, tanneryTheoremFields x = tanneryTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk array₁ limit₁ majorant₁ windows₁ readback₁ dyadic₁ endpoint₁ transport₁ route₁
      provenance₁ cert₁ =>
      cases y with
      | mk array₂ limit₂ majorant₂ windows₂ readback₂ dyadic₂ endpoint₂ transport₂ route₂
          provenance₂ cert₂ =>
          cases hfields
          rfl

instance tanneryTheoremBHistCarrier : BHistCarrier TanneryTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tanneryTheoremToEventFlow
  fromEventFlow := tanneryTheoremFromEventFlow

instance tanneryTheoremChapterTasteGate : ChapterTasteGate TanneryTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change tanneryTheoremFromEventFlow (tanneryTheoremToEventFlow x) = some x
    exact TanneryTheoremTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TanneryTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance tanneryTheoremFieldFaithful : FieldFaithful TanneryTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := tanneryTheoremFields
  field_faithful := TanneryTheoremTasteGate_single_carrier_alignment_fields_faithful

instance tanneryTheoremNontrivial : Nontrivial TanneryTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TanneryTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TanneryTheoremUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def TanneryTheoremTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate TanneryTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tanneryTheoremChapterTasteGate

theorem TanneryTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, tanneryTheoremDecodeBHist (tanneryTheoremEncodeBHist h) = h) ∧
      tanneryTheoremFields
          (TanneryTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨TanneryTheoremTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.TanneryTheoremUp
