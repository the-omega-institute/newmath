import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConvergentRealSequenceCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConvergentRealSequenceCauchyUp : Type where
  | mk :
      (limitRow windows readback dyadicLedger latePairTest consumerRow transport replay
        provenance localNameCert : BHist) →
      ConvergentRealSequenceCauchyUp
  deriving DecidableEq

def convergentRealSequenceCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: convergentRealSequenceCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: convergentRealSequenceCauchyEncodeBHist h

def convergentRealSequenceCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (convergentRealSequenceCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (convergentRealSequenceCauchyDecodeBHist tail)

theorem ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      convergentRealSequenceCauchyDecodeBHist (convergentRealSequenceCauchyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def convergentRealSequenceCauchyFields :
    ConvergentRealSequenceCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConvergentRealSequenceCauchyUp.mk limitRow windows readback dyadicLedger latePairTest
      consumerRow transport replay provenance localNameCert =>
      [limitRow, windows, readback, dyadicLedger, latePairTest, consumerRow, transport,
        replay, provenance, localNameCert]

def convergentRealSequenceCauchyToEventFlow :
    ConvergentRealSequenceCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map convergentRealSequenceCauchyEncodeBHist
      (convergentRealSequenceCauchyFields x)

private def ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault index rest

def convergentRealSequenceCauchyFromEventFlow :
    EventFlow → Option ConvergentRealSequenceCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ConvergentRealSequenceCauchyUp.mk
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 0 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 2 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 4 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 6 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 8 ef))
        (convergentRealSequenceCauchyDecodeBHist
          (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_eventAtDefault 9 ef)))

theorem ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConvergentRealSequenceCauchyUp,
      convergentRealSequenceCauchyFromEventFlow (convergentRealSequenceCauchyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk limitRow windows readback dyadicLedger latePairTest consumerRow transport replay
      provenance localNameCert =>
      change
        some
          (ConvergentRealSequenceCauchyUp.mk
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist limitRow))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist windows))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist readback))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist dyadicLedger))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist latePairTest))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist consumerRow))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist transport))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist replay))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist provenance))
            (convergentRealSequenceCauchyDecodeBHist
              (convergentRealSequenceCauchyEncodeBHist localNameCert))) =
          some
            (ConvergentRealSequenceCauchyUp.mk limitRow windows readback dyadicLedger
              latePairTest consumerRow transport replay provenance localNameCert)
      rw [ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          limitRow,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          windows,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          readback,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          dyadicLedger,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          latePairTest,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          consumerRow,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          transport,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          replay,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          provenance,
        ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
          localNameCert]

theorem ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConvergentRealSequenceCauchyUp} :
    convergentRealSequenceCauchyToEventFlow x = convergentRealSequenceCauchyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      convergentRealSequenceCauchyFromEventFlow (convergentRealSequenceCauchyToEventFlow x) =
        convergentRealSequenceCauchyFromEventFlow
          (convergentRealSequenceCauchyToEventFlow y) :=
    congrArg convergentRealSequenceCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_round_trip y)))

private theorem convergentRealSequenceCauchy_field_faithful :
    ∀ x y : ConvergentRealSequenceCauchyUp,
      convergentRealSequenceCauchyFields x = convergentRealSequenceCauchyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk limitRow₁ windows₁ readback₁ dyadicLedger₁ latePairTest₁ consumerRow₁ transport₁
      replay₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk limitRow₂ windows₂ readback₂ dyadicLedger₂ latePairTest₂ consumerRow₂ transport₂
          replay₂ provenance₂ localNameCert₂ =>
          injection hfields with hLimitRow tail0
          injection tail0 with hWindows tail1
          injection tail1 with hReadback tail2
          injection tail2 with hDyadicLedger tail3
          injection tail3 with hLatePairTest tail4
          injection tail4 with hConsumerRow tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalNameCert _
          subst hLimitRow
          subst hWindows
          subst hReadback
          subst hDyadicLedger
          subst hLatePairTest
          subst hConsumerRow
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalNameCert
          rfl

instance convergentRealSequenceCauchyBHistCarrier :
    BHistCarrier ConvergentRealSequenceCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := convergentRealSequenceCauchyToEventFlow
  fromEventFlow := convergentRealSequenceCauchyFromEventFlow

instance convergentRealSequenceCauchyChapterTasteGate :
    ChapterTasteGate ConvergentRealSequenceCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      convergentRealSequenceCauchyFromEventFlow (convergentRealSequenceCauchyToEventFlow x) =
        some x
    exact ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance convergentRealSequenceCauchyFieldFaithful :
    FieldFaithful ConvergentRealSequenceCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := convergentRealSequenceCauchyFields
  field_faithful := convergentRealSequenceCauchy_field_faithful

instance convergentRealSequenceCauchyNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ConvergentRealSequenceCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ConvergentRealSequenceCauchyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ConvergentRealSequenceCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ConvergentRealSequenceCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  convergentRealSequenceCauchyChapterTasteGate

theorem ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ConvergentRealSequenceCauchyUp) ∧
      Nonempty (FieldFaithful ConvergentRealSequenceCauchyUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ConvergentRealSequenceCauchyUp) ∧
          (∀ h : BHist,
            convergentRealSequenceCauchyDecodeBHist
                (convergentRealSequenceCauchyEncodeBHist h) =
              h) ∧
            (∀ x : ConvergentRealSequenceCauchyUp,
              convergentRealSequenceCauchyFromEventFlow
                  (convergentRealSequenceCauchyToEventFlow x) =
                some x) ∧
              (∀ x y : ConvergentRealSequenceCauchyUp,
                convergentRealSequenceCauchyToEventFlow x =
                    convergentRealSequenceCauchyToEventFlow y →
                  x = y) ∧
                convergentRealSequenceCauchyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact Nonempty.intro convergentRealSequenceCauchyChapterTasteGate
  · constructor
    · exact Nonempty.intro convergentRealSequenceCauchyFieldFaithful
    · constructor
      · exact Nonempty.intro convergentRealSequenceCauchyNontrivial
      · constructor
        · exact ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact
                ConvergentRealSequenceCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
                  heq
            · rfl

end BEDC.Derived.ConvergentRealSequenceCauchyUp
