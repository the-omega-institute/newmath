import BEDC.Derived.FiniteTailFilterUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteTailFilterUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTailFilterUp : Type where
  | mk :
      (stream dyadic regular budget commonTail sealRow transport classifier provenance name :
        BHist) →
      FiniteTailFilterUp
  deriving DecidableEq

def finiteTailFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTailFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTailFilterEncodeBHist h

def finiteTailFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTailFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTailFilterDecodeBHist tail)

private theorem finiteTailFilter_decode_encode_bhist :
    ∀ h : BHist, finiteTailFilterDecodeBHist (finiteTailFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteTailFilterToEventFlow : FiniteTailFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteTailFilterUp.mk stream dyadic regular budget commonTail sealRow transport classifier
      provenance name =>
      [finiteTailFilterEncodeBHist stream,
        finiteTailFilterEncodeBHist dyadic,
        finiteTailFilterEncodeBHist regular,
        finiteTailFilterEncodeBHist budget,
        finiteTailFilterEncodeBHist commonTail,
        finiteTailFilterEncodeBHist sealRow,
        finiteTailFilterEncodeBHist transport,
        finiteTailFilterEncodeBHist classifier,
        finiteTailFilterEncodeBHist provenance,
        finiteTailFilterEncodeBHist name]

private def finiteTailFilterNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => finiteTailFilterNthRawEvent tail n

def finiteTailFilterFromEventFlow (ef : EventFlow) : Option FiniteTailFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteTailFilterUp.mk
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 0))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 1))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 2))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 3))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 4))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 5))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 6))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 7))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 8))
      (finiteTailFilterDecodeBHist (finiteTailFilterNthRawEvent ef 9)))

private theorem finiteTailFilter_mk_congr
    {stream stream' dyadic dyadic' regular regular' budget budget' commonTail commonTail'
      sealRow sealRow' transport transport' classifier classifier' provenance provenance' name
      name' : BHist}
    (hStream : stream' = stream)
    (hDyadic : dyadic' = dyadic)
    (hRegular : regular' = regular)
    (hBudget : budget' = budget)
    (hCommonTail : commonTail' = commonTail)
    (hSealRow : sealRow' = sealRow)
    (hTransport : transport' = transport)
    (hClassifier : classifier' = classifier)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    FiniteTailFilterUp.mk stream' dyadic' regular' budget' commonTail' sealRow' transport'
        classifier' provenance' name' =
      FiniteTailFilterUp.mk stream dyadic regular budget commonTail sealRow transport classifier
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hStream
  cases hDyadic
  cases hRegular
  cases hBudget
  cases hCommonTail
  cases hSealRow
  cases hTransport
  cases hClassifier
  cases hProvenance
  cases hName
  rfl

private theorem finiteTailFilter_round_trip :
    ∀ x : FiniteTailFilterUp,
      finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream dyadic regular budget commonTail sealRow transport classifier provenance name =>
      exact
        congrArg some
          (finiteTailFilter_mk_congr
            (finiteTailFilter_decode_encode_bhist stream)
            (finiteTailFilter_decode_encode_bhist dyadic)
            (finiteTailFilter_decode_encode_bhist regular)
            (finiteTailFilter_decode_encode_bhist budget)
            (finiteTailFilter_decode_encode_bhist commonTail)
            (finiteTailFilter_decode_encode_bhist sealRow)
            (finiteTailFilter_decode_encode_bhist transport)
            (finiteTailFilter_decode_encode_bhist classifier)
            (finiteTailFilter_decode_encode_bhist provenance)
            (finiteTailFilter_decode_encode_bhist name))

private theorem finiteTailFilterToEventFlow_injective {x y : FiniteTailFilterUp} :
    finiteTailFilterToEventFlow x = finiteTailFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) =
        finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow y) :=
    congrArg finiteTailFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteTailFilter_round_trip x).symm
      (Eq.trans hread (finiteTailFilter_round_trip y)))

instance finiteTailFilterBHistCarrier : BHistCarrier FiniteTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTailFilterToEventFlow
  fromEventFlow := finiteTailFilterFromEventFlow

instance finiteTailFilterChapterTasteGate : ChapterTasteGate FiniteTailFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteTailFilterFromEventFlow (finiteTailFilterToEventFlow x) = some x
    exact finiteTailFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteTailFilterToEventFlow_injective heq)

theorem FiniteTailFilterUpTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier FiniteTailFilterUp) ∧
      Nonempty (ChapterTasteGate FiniteTailFilterUp) ∧
        ∃ x : FiniteTailFilterUp,
          BHistCarrier.toEventFlow x =
            finiteTailFilterToEventFlow
              (FiniteTailFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨finiteTailFilterBHistCarrier⟩, ⟨finiteTailFilterChapterTasteGate⟩,
      ⟨FiniteTailFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩⟩

end BEDC.Derived.FiniteTailFilterUp.TasteGate
