import BEDC.Derived.FiniteDimensionalNormedCompletenessUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def finiteDimensionalNormedCompletenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteDimensionalNormedCompletenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteDimensionalNormedCompletenessEncodeBHist h

def finiteDimensionalNormedCompletenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteDimensionalNormedCompletenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteDimensionalNormedCompletenessDecodeBHist tail)

private theorem FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteDimensionalNormedCompletenessFields :
    FiniteDimensionalNormedCompletenessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteDimensionalNormedCompletenessUp.mk vecSpace normedSpace finiteBasis
      coordinateCauchy normStability regSeqRat realSeal completionOperator banachSeal
      transport replay provenance localNameCert =>
      [vecSpace, normedSpace, finiteBasis, coordinateCauchy, normStability, regSeqRat,
        realSeal, completionOperator, banachSeal, transport, replay, provenance,
        localNameCert]

def finiteDimensionalNormedCompletenessToEventFlow :
    FiniteDimensionalNormedCompletenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (finiteDimensionalNormedCompletenessFields x).map
        finiteDimensionalNormedCompletenessEncodeBHist

private def finiteDimensionalNormedCompletenessEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      finiteDimensionalNormedCompletenessEventAtDefault index rest

def finiteDimensionalNormedCompletenessFromEventFlow :
    EventFlow → Option FiniteDimensionalNormedCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (FiniteDimensionalNormedCompletenessUp.mk
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 0 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 1 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 2 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 3 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 4 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 5 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 6 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 7 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 8 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 9 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 10 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 11 ef))
        (finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEventAtDefault 12 ef)))

private theorem FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteDimensionalNormedCompletenessUp,
      finiteDimensionalNormedCompletenessFromEventFlow
          (finiteDimensionalNormedCompletenessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk vecSpace normedSpace finiteBasis coordinateCauchy normStability regSeqRat realSeal
      completionOperator banachSeal transport replay provenance localNameCert =>
      change
        some
          (FiniteDimensionalNormedCompletenessUp.mk
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist vecSpace))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist normedSpace))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist finiteBasis))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist coordinateCauchy))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist normStability))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist regSeqRat))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist realSeal))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist completionOperator))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist banachSeal))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist transport))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist replay))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist provenance))
            (finiteDimensionalNormedCompletenessDecodeBHist
              (finiteDimensionalNormedCompletenessEncodeBHist localNameCert))) =
          some
            (FiniteDimensionalNormedCompletenessUp.mk vecSpace normedSpace finiteBasis
              coordinateCauchy normStability regSeqRat realSeal completionOperator banachSeal
              transport replay provenance localNameCert)
      rw [FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode vecSpace,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode normedSpace,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode finiteBasis,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode
          coordinateCauchy,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode
          normStability,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode regSeqRat,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode realSeal,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode
          completionOperator,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode banachSeal,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode transport,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode replay,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode provenance,
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode
          localNameCert]

private theorem
    FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FiniteDimensionalNormedCompletenessUp} :
    finiteDimensionalNormedCompletenessToEventFlow x =
        finiteDimensionalNormedCompletenessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteDimensionalNormedCompletenessFromEventFlow
          (finiteDimensionalNormedCompletenessToEventFlow x) =
        finiteDimensionalNormedCompletenessFromEventFlow
          (finiteDimensionalNormedCompletenessToEventFlow y) :=
    congrArg finiteDimensionalNormedCompletenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_round_trip y)))

instance finiteDimensionalNormedCompletenessBHistCarrier :
    BHistCarrier FiniteDimensionalNormedCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteDimensionalNormedCompletenessToEventFlow
  fromEventFlow := finiteDimensionalNormedCompletenessFromEventFlow

instance finiteDimensionalNormedCompletenessChapterTasteGate :
    ChapterTasteGate FiniteDimensionalNormedCompletenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteDimensionalNormedCompletenessFromEventFlow
          (finiteDimensionalNormedCompletenessToEventFlow x) =
        some x
    exact FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def finiteDimensionalNormedCompletenessTasteGate :
    ChapterTasteGate FiniteDimensionalNormedCompletenessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteDimensionalNormedCompletenessChapterTasteGate

theorem FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteDimensionalNormedCompletenessDecodeBHist
          (finiteDimensionalNormedCompletenessEncodeBHist h) =
        h) ∧
      (∀ x : FiniteDimensionalNormedCompletenessUp,
        finiteDimensionalNormedCompletenessFromEventFlow
            (finiteDimensionalNormedCompletenessToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteDimensionalNormedCompletenessUp,
          finiteDimensionalNormedCompletenessToEventFlow x =
              finiteDimensionalNormedCompletenessToEventFlow y →
            x = y) ∧
          finiteDimensionalNormedCompletenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_decode,
      FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        FiniteDimensionalNormedCompletenessTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived
