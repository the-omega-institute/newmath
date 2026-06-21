import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopDyadicSqueezeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopDyadicSqueezeUp : Type where
  | mk
      (lower upper precision window lowerBound upperBound readback sealRead transport replay
        provenance localName : BHist) : BishopDyadicSqueezeUp
  deriving DecidableEq

def BishopDyadicSqueezeUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: BishopDyadicSqueezeUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: BishopDyadicSqueezeUp_encodeBHist h

def BishopDyadicSqueezeUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (BishopDyadicSqueezeUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (BishopDyadicSqueezeUp_decodeBHist tail)

private theorem BishopDyadicSqueezeUp_decode_round_trip :
    ∀ h : BHist,
      BishopDyadicSqueezeUp_decodeBHist (BishopDyadicSqueezeUp_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BishopDyadicSqueezeUp_fields : BishopDyadicSqueezeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopDyadicSqueezeUp.mk lower upper precision window lowerBound upperBound readback sealRead
      transport replay provenance localName =>
      [lower, upper, precision, window, lowerBound, upperBound, readback, sealRead, transport,
        replay, provenance, localName]

def BishopDyadicSqueezeUp_toEventFlow : BishopDyadicSqueezeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (BishopDyadicSqueezeUp_fields x).map BishopDyadicSqueezeUp_encodeBHist

def BishopDyadicSqueezeUp_fromEventFlow : EventFlow → Option BishopDyadicSqueezeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [lower, upper, precision, window, lowerBound, upperBound, readback, sealRead, transport,
      replay, provenance, localName] =>
      some
        (BishopDyadicSqueezeUp.mk
          (BishopDyadicSqueezeUp_decodeBHist lower)
          (BishopDyadicSqueezeUp_decodeBHist upper)
          (BishopDyadicSqueezeUp_decodeBHist precision)
          (BishopDyadicSqueezeUp_decodeBHist window)
          (BishopDyadicSqueezeUp_decodeBHist lowerBound)
          (BishopDyadicSqueezeUp_decodeBHist upperBound)
          (BishopDyadicSqueezeUp_decodeBHist readback)
          (BishopDyadicSqueezeUp_decodeBHist sealRead)
          (BishopDyadicSqueezeUp_decodeBHist transport)
          (BishopDyadicSqueezeUp_decodeBHist replay)
          (BishopDyadicSqueezeUp_decodeBHist provenance)
          (BishopDyadicSqueezeUp_decodeBHist localName))
  | _ => none

private theorem BishopDyadicSqueezeUp_round_trip (x : BishopDyadicSqueezeUp) :
    BishopDyadicSqueezeUp_fromEventFlow (BishopDyadicSqueezeUp_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk lower upper precision window lowerBound upperBound readback sealRead transport replay
      provenance localName =>
      change
        some
          (BishopDyadicSqueezeUp.mk
            (BishopDyadicSqueezeUp_decodeBHist (BishopDyadicSqueezeUp_encodeBHist lower))
            (BishopDyadicSqueezeUp_decodeBHist (BishopDyadicSqueezeUp_encodeBHist upper))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist precision))
            (BishopDyadicSqueezeUp_decodeBHist (BishopDyadicSqueezeUp_encodeBHist window))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist lowerBound))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist upperBound))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist readback))
            (BishopDyadicSqueezeUp_decodeBHist (BishopDyadicSqueezeUp_encodeBHist sealRead))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist transport))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist replay))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist provenance))
            (BishopDyadicSqueezeUp_decodeBHist
              (BishopDyadicSqueezeUp_encodeBHist localName))) =
          some
            (BishopDyadicSqueezeUp.mk lower upper precision window lowerBound upperBound
              readback sealRead transport replay provenance localName)
      rw [BishopDyadicSqueezeUp_decode_round_trip lower,
        BishopDyadicSqueezeUp_decode_round_trip upper,
        BishopDyadicSqueezeUp_decode_round_trip precision,
        BishopDyadicSqueezeUp_decode_round_trip window,
        BishopDyadicSqueezeUp_decode_round_trip lowerBound,
        BishopDyadicSqueezeUp_decode_round_trip upperBound,
        BishopDyadicSqueezeUp_decode_round_trip readback,
        BishopDyadicSqueezeUp_decode_round_trip sealRead,
        BishopDyadicSqueezeUp_decode_round_trip transport,
        BishopDyadicSqueezeUp_decode_round_trip replay,
        BishopDyadicSqueezeUp_decode_round_trip provenance,
        BishopDyadicSqueezeUp_decode_round_trip localName]

private theorem BishopDyadicSqueezeUp_toEventFlow_injective
    {x y : BishopDyadicSqueezeUp} :
    BishopDyadicSqueezeUp_toEventFlow x = BishopDyadicSqueezeUp_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BishopDyadicSqueezeUp_fromEventFlow (BishopDyadicSqueezeUp_toEventFlow x) =
        BishopDyadicSqueezeUp_fromEventFlow (BishopDyadicSqueezeUp_toEventFlow y) :=
    congrArg BishopDyadicSqueezeUp_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopDyadicSqueezeUp_round_trip x).symm
      (Eq.trans hread (BishopDyadicSqueezeUp_round_trip y)))

instance BishopDyadicSqueezeUp_BHistCarrier : BHistCarrier BishopDyadicSqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BishopDyadicSqueezeUp_toEventFlow
  fromEventFlow := BishopDyadicSqueezeUp_fromEventFlow

instance BishopDyadicSqueezeUp_ChapterTasteGate :
    ChapterTasteGate BishopDyadicSqueezeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BishopDyadicSqueezeUp_fromEventFlow (BishopDyadicSqueezeUp_toEventFlow x) = some x
    exact BishopDyadicSqueezeUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopDyadicSqueezeUp_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopDyadicSqueezeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BishopDyadicSqueezeUp_ChapterTasteGate

end BEDC.Derived.BishopDyadicSqueezeUp
