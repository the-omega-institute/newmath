import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanCauchyCompleteFieldUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanCauchyCompleteFieldUp : Type where
  | mk :
      (real regular dyadic stream order complete archimedean transport replay provenance
        name : BHist) →
      ArchimedeanCauchyCompleteFieldUp
  deriving DecidableEq

def archimedeanCauchyCompleteFieldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanCauchyCompleteFieldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanCauchyCompleteFieldEncodeBHist h

def archimedeanCauchyCompleteFieldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanCauchyCompleteFieldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanCauchyCompleteFieldDecodeBHist tail)

private theorem ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def archimedeanCauchyCompleteFieldToEventFlow :
    ArchimedeanCauchyCompleteFieldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanCauchyCompleteFieldUp.mk real regular dyadic stream order complete
      archimedean transport replay provenance name =>
      [archimedeanCauchyCompleteFieldEncodeBHist real,
        archimedeanCauchyCompleteFieldEncodeBHist regular,
        archimedeanCauchyCompleteFieldEncodeBHist dyadic,
        archimedeanCauchyCompleteFieldEncodeBHist stream,
        archimedeanCauchyCompleteFieldEncodeBHist order,
        archimedeanCauchyCompleteFieldEncodeBHist complete,
        archimedeanCauchyCompleteFieldEncodeBHist archimedean,
        archimedeanCauchyCompleteFieldEncodeBHist transport,
        archimedeanCauchyCompleteFieldEncodeBHist replay,
        archimedeanCauchyCompleteFieldEncodeBHist provenance,
        archimedeanCauchyCompleteFieldEncodeBHist name]

private def archimedeanCauchyCompleteFieldEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      archimedeanCauchyCompleteFieldEventAtDefault index rest

def archimedeanCauchyCompleteFieldFromEventFlow
    (ef : EventFlow) : Option ArchimedeanCauchyCompleteFieldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ArchimedeanCauchyCompleteFieldUp.mk
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 0 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 1 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 2 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 3 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 4 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 5 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 6 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 7 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 8 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 9 ef))
      (archimedeanCauchyCompleteFieldDecodeBHist
        (archimedeanCauchyCompleteFieldEventAtDefault 10 ef)))

private theorem ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ArchimedeanCauchyCompleteFieldUp,
      archimedeanCauchyCompleteFieldFromEventFlow
        (archimedeanCauchyCompleteFieldToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk real regular dyadic stream order complete archimedean transport replay provenance name =>
      change
        some
            (ArchimedeanCauchyCompleteFieldUp.mk
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist real))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist regular))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist dyadic))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist stream))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist order))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist complete))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist archimedean))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist transport))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist replay))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist provenance))
              (archimedeanCauchyCompleteFieldDecodeBHist
                (archimedeanCauchyCompleteFieldEncodeBHist name))) =
          some
            (ArchimedeanCauchyCompleteFieldUp.mk real regular dyadic stream order complete
              archimedean transport replay provenance name)
      rw [ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode real,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode regular,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode dyadic,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode stream,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode order,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode complete,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode archimedean,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode transport,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode replay,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode provenance,
        ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode name]

private theorem ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_injective
    {x y : ArchimedeanCauchyCompleteFieldUp} :
    archimedeanCauchyCompleteFieldToEventFlow x =
      archimedeanCauchyCompleteFieldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanCauchyCompleteFieldFromEventFlow
          (archimedeanCauchyCompleteFieldToEventFlow x) =
        archimedeanCauchyCompleteFieldFromEventFlow
          (archimedeanCauchyCompleteFieldToEventFlow y) :=
    congrArg archimedeanCauchyCompleteFieldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_round_trip y)))

instance archimedeanCauchyCompleteFieldBHistCarrier :
    BHistCarrier ArchimedeanCauchyCompleteFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanCauchyCompleteFieldToEventFlow
  fromEventFlow := archimedeanCauchyCompleteFieldFromEventFlow

instance archimedeanCauchyCompleteFieldChapterTasteGate :
    ChapterTasteGate ArchimedeanCauchyCompleteFieldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanCauchyCompleteFieldFromEventFlow
      (archimedeanCauchyCompleteFieldToEventFlow x) = some x
    exact ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_injective heq)

theorem ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        archimedeanCauchyCompleteFieldDecodeBHist
            (archimedeanCauchyCompleteFieldEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ArchimedeanCauchyCompleteFieldUp) ∧
        Nonempty (ChapterTasteGate ArchimedeanCauchyCompleteFieldUp) ∧
          archimedeanCauchyCompleteFieldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨ArchimedeanCauchyCompleteFieldTasteGate_single_carrier_alignment_decode,
      ⟨archimedeanCauchyCompleteFieldBHistCarrier⟩,
      ⟨archimedeanCauchyCompleteFieldChapterTasteGate⟩, rfl⟩

end BEDC.Derived.ArchimedeanCauchyCompleteFieldUp.TasteGate
