import BEDC.Derived.CompactCauchyEquicontinuityUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactCauchyEquicontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def compactCauchyEquicontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactCauchyEquicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactCauchyEquicontinuityEncodeBHist h

def compactCauchyEquicontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactCauchyEquicontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactCauchyEquicontinuityDecodeBHist tail)

private theorem compactCauchyEquicontinuity_decode_encode_bhist :
    ∀ h : BHist,
      compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactCauchyEquicontinuityFields :
    CompactCauchyEquicontinuityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactCauchyEquicontinuityUp.mk compactSource finiteNet pointwiseModulus
      cauchyFamily toleranceLedger regSeqRoute realSeal transport replay provenance
      localName =>
      [compactSource, finiteNet, pointwiseModulus, cauchyFamily, toleranceLedger,
        regSeqRoute, realSeal, transport, replay, provenance, localName]

def compactCauchyEquicontinuityToEventFlow :
    CompactCauchyEquicontinuityUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (compactCauchyEquicontinuityFields x).map compactCauchyEquicontinuityEncodeBHist

private def compactCauchyEquicontinuityEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      compactCauchyEquicontinuityEventAtDefault index rest

def compactCauchyEquicontinuityFromEventFlow :
    EventFlow → Option CompactCauchyEquicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CompactCauchyEquicontinuityUp.mk
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 0 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 1 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 2 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 3 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 4 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 5 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 6 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 7 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 8 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 9 ef))
        (compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEventAtDefault 10 ef)))

private theorem compactCauchyEquicontinuity_round_trip :
    ∀ x : CompactCauchyEquicontinuityUp,
      compactCauchyEquicontinuityFromEventFlow
          (compactCauchyEquicontinuityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactSource finiteNet pointwiseModulus cauchyFamily toleranceLedger regSeqRoute
      realSeal transport replay provenance localName =>
      change
        some
            (CompactCauchyEquicontinuityUp.mk
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist compactSource))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist finiteNet))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist pointwiseModulus))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist cauchyFamily))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist toleranceLedger))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist regSeqRoute))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist realSeal))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist transport))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist replay))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist provenance))
              (compactCauchyEquicontinuityDecodeBHist
                (compactCauchyEquicontinuityEncodeBHist localName))) =
          some
            (CompactCauchyEquicontinuityUp.mk compactSource finiteNet pointwiseModulus
              cauchyFamily toleranceLedger regSeqRoute realSeal transport replay provenance
              localName)
      rw [compactCauchyEquicontinuity_decode_encode_bhist compactSource,
        compactCauchyEquicontinuity_decode_encode_bhist finiteNet,
        compactCauchyEquicontinuity_decode_encode_bhist pointwiseModulus,
        compactCauchyEquicontinuity_decode_encode_bhist cauchyFamily,
        compactCauchyEquicontinuity_decode_encode_bhist toleranceLedger,
        compactCauchyEquicontinuity_decode_encode_bhist regSeqRoute,
        compactCauchyEquicontinuity_decode_encode_bhist realSeal,
        compactCauchyEquicontinuity_decode_encode_bhist transport,
        compactCauchyEquicontinuity_decode_encode_bhist replay,
        compactCauchyEquicontinuity_decode_encode_bhist provenance,
        compactCauchyEquicontinuity_decode_encode_bhist localName]

private theorem compactCauchyEquicontinuityToEventFlow_injective
    {x y : CompactCauchyEquicontinuityUp} :
    compactCauchyEquicontinuityToEventFlow x =
      compactCauchyEquicontinuityToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactCauchyEquicontinuityFromEventFlow
          (compactCauchyEquicontinuityToEventFlow x) =
        compactCauchyEquicontinuityFromEventFlow
          (compactCauchyEquicontinuityToEventFlow y) :=
    congrArg compactCauchyEquicontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactCauchyEquicontinuity_round_trip x).symm
      (Eq.trans hread (compactCauchyEquicontinuity_round_trip y)))

instance compactCauchyEquicontinuityBHistCarrier :
    BHistCarrier CompactCauchyEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactCauchyEquicontinuityToEventFlow
  fromEventFlow := compactCauchyEquicontinuityFromEventFlow

instance compactCauchyEquicontinuityChapterTasteGate :
    ChapterTasteGate CompactCauchyEquicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactCauchyEquicontinuityFromEventFlow
          (compactCauchyEquicontinuityToEventFlow x) =
        some x
    exact compactCauchyEquicontinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactCauchyEquicontinuityToEventFlow_injective heq)

theorem CompactCauchyEquicontinuityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactCauchyEquicontinuityDecodeBHist
          (compactCauchyEquicontinuityEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier CompactCauchyEquicontinuityUp) ∧
        Nonempty (ChapterTasteGate CompactCauchyEquicontinuityUp) ∧
          compactCauchyEquicontinuityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactCauchyEquicontinuity_decode_encode_bhist
  · constructor
    · exact ⟨compactCauchyEquicontinuityBHistCarrier⟩
    · constructor
      · exact ⟨compactCauchyEquicontinuityChapterTasteGate⟩
      · rfl

end BEDC.Derived.CompactCauchyEquicontinuityUp
