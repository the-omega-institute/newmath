import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCompletionSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCompletionSealUp : Type where
  | mk :
      (dyadic stream regular locatedSource tailEnvelope completionBoundary realSeal
        transport replay provenance localName : BHist) →
      LocatedCompletionSealUp
  deriving DecidableEq

def locatedCompletionSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCompletionSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCompletionSealEncodeBHist h

def locatedCompletionSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCompletionSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCompletionSealDecodeBHist tail)

private theorem LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedCompletionSealFields : LocatedCompletionSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCompletionSealUp.mk dyadic stream regular locatedSource tailEnvelope
      completionBoundary realSeal transport replay provenance localName =>
      [dyadic, stream, regular, locatedSource, tailEnvelope, completionBoundary, realSeal,
        transport, replay, provenance, localName]

def locatedCompletionSealToEventFlow : LocatedCompletionSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCompletionSealFields x).map locatedCompletionSealEncodeBHist

def locatedCompletionSealFromEventFlow : EventFlow → Option LocatedCompletionSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: [] => none
  | dyadic :: stream :: regular :: locatedSource :: tailEnvelope :: completionBoundary ::
      realSeal :: transport :: replay :: provenance :: localName :: [] =>
      some
        (LocatedCompletionSealUp.mk
          (locatedCompletionSealDecodeBHist dyadic)
          (locatedCompletionSealDecodeBHist stream)
          (locatedCompletionSealDecodeBHist regular)
          (locatedCompletionSealDecodeBHist locatedSource)
          (locatedCompletionSealDecodeBHist tailEnvelope)
          (locatedCompletionSealDecodeBHist completionBoundary)
          (locatedCompletionSealDecodeBHist realSeal)
          (locatedCompletionSealDecodeBHist transport)
          (locatedCompletionSealDecodeBHist replay)
          (locatedCompletionSealDecodeBHist provenance)
          (locatedCompletionSealDecodeBHist localName))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _l :: _rest =>
      none

private theorem LocatedCompletionSealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedCompletionSealUp,
      locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk dyadic stream regular locatedSource tailEnvelope completionBoundary realSeal
      transport replay provenance localName =>
      change
        some
          (LocatedCompletionSealUp.mk
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist dyadic))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist stream))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist regular))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist locatedSource))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist tailEnvelope))
            (locatedCompletionSealDecodeBHist
              (locatedCompletionSealEncodeBHist completionBoundary))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist realSeal))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist transport))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist replay))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist provenance))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist localName))) =
          some
            (LocatedCompletionSealUp.mk dyadic stream regular locatedSource tailEnvelope
              completionBoundary realSeal transport replay provenance localName)
      rw [LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode dyadic,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode stream,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode regular,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode locatedSource,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode tailEnvelope,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode completionBoundary,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode realSeal,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode transport,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode replay,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode provenance,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode localName]

private theorem LocatedCompletionSealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedCompletionSealUp} :
    locatedCompletionSealToEventFlow x = locatedCompletionSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) =
        locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow y) :=
    congrArg locatedCompletionSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LocatedCompletionSealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LocatedCompletionSealTasteGate_single_carrier_alignment_round_trip y)))

instance locatedCompletionSealBHistCarrier : BHistCarrier LocatedCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCompletionSealToEventFlow
  fromEventFlow := locatedCompletionSealFromEventFlow

instance locatedCompletionSealChapterTasteGate : ChapterTasteGate LocatedCompletionSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) = some x
    exact LocatedCompletionSealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedCompletionSealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LocatedCompletionSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist h) = h) ∧
      (∀ x : LocatedCompletionSealUp,
        locatedCompletionSealFromEventFlow (locatedCompletionSealToEventFlow x) = some x) ∧
        (∀ x y : LocatedCompletionSealUp,
          locatedCompletionSealToEventFlow x = locatedCompletionSealToEventFlow y → x = y) ∧
          locatedCompletionSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact LocatedCompletionSealTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact LocatedCompletionSealTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

theorem LocatedCompletionSealNameCert_obligation_rows_exact
    (D S R Q E A T H C P N : BHist) :
    locatedCompletionSealFields (LocatedCompletionSealUp.mk D S R Q E A T H C P N) =
        [D, S, R, Q, E, A, T, H, C, P, N] ∧
      locatedCompletionSealToEventFlow (LocatedCompletionSealUp.mk D S R Q E A T H C P N) =
        [locatedCompletionSealEncodeBHist D, locatedCompletionSealEncodeBHist S,
          locatedCompletionSealEncodeBHist R, locatedCompletionSealEncodeBHist Q,
          locatedCompletionSealEncodeBHist E, locatedCompletionSealEncodeBHist A,
          locatedCompletionSealEncodeBHist T, locatedCompletionSealEncodeBHist H,
          locatedCompletionSealEncodeBHist C, locatedCompletionSealEncodeBHist P,
          locatedCompletionSealEncodeBHist N] ∧
        locatedCompletionSealFromEventFlow
            [locatedCompletionSealEncodeBHist D, locatedCompletionSealEncodeBHist S,
              locatedCompletionSealEncodeBHist R, locatedCompletionSealEncodeBHist Q,
              locatedCompletionSealEncodeBHist E, locatedCompletionSealEncodeBHist A,
              locatedCompletionSealEncodeBHist T, locatedCompletionSealEncodeBHist H,
              locatedCompletionSealEncodeBHist C, locatedCompletionSealEncodeBHist P,
              locatedCompletionSealEncodeBHist N] =
          some (LocatedCompletionSealUp.mk D S R Q E A T H C P N) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · rfl
    · change
        some
          (LocatedCompletionSealUp.mk
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist D))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist S))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist R))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist Q))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist E))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist A))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist T))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist H))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist C))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist P))
            (locatedCompletionSealDecodeBHist (locatedCompletionSealEncodeBHist N))) =
          some (LocatedCompletionSealUp.mk D S R Q E A T H C P N)
      rw [LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode D,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode S,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode R,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode Q,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode E,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode A,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode T,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode H,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode C,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode P,
        LocatedCompletionSealTasteGate_single_carrier_alignment_decode_encode N]

end BEDC.Derived.LocatedCompletionSealUp
