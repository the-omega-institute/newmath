import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCutUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCutUp : Type where
  | mk :
      (lowerCut upperCut modulusLedger streamSchedule regularSource dyadicArithmetic realSeal
        transport replay provenance localCert : BHist) →
      CauchyCutUp
  deriving DecidableEq

def cauchyCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCutEncodeBHist h

def cauchyCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCutDecodeBHist tail)

theorem CauchyCutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchyCutDecodeBHist (cauchyCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCutFields : CauchyCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCutUp.mk lowerCut upperCut modulusLedger streamSchedule regularSource
      dyadicArithmetic realSeal transport replay provenance localCert =>
      [lowerCut, upperCut, modulusLedger, streamSchedule, regularSource, dyadicArithmetic,
        realSeal, transport, replay, provenance, localCert]

def cauchyCutToEventFlow : CauchyCutUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map cauchyCutEncodeBHist (cauchyCutFields x)

private def cauchyCutEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCutEventAtDefault index rest

def cauchyCutFromEventFlow : EventFlow → Option CauchyCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCutUp.mk
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 0 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 1 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 2 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 3 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 4 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 5 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 6 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 7 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 8 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 9 ef))
        (cauchyCutDecodeBHist (cauchyCutEventAtDefault 10 ef)))

private theorem cauchyCut_round_trip :
    ∀ x : CauchyCutUp, cauchyCutFromEventFlow (cauchyCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk lowerCut upperCut modulusLedger streamSchedule regularSource dyadicArithmetic realSeal
      transport replay provenance localCert =>
      change
        some
          (CauchyCutUp.mk
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist lowerCut))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist upperCut))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist modulusLedger))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist streamSchedule))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist regularSource))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist dyadicArithmetic))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist realSeal))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist transport))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist replay))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist provenance))
            (cauchyCutDecodeBHist (cauchyCutEncodeBHist localCert))) =
          some
            (CauchyCutUp.mk lowerCut upperCut modulusLedger streamSchedule regularSource
              dyadicArithmetic realSeal transport replay provenance localCert)
      rw [CauchyCutTasteGate_single_carrier_alignment_decode_encode lowerCut,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode upperCut,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode modulusLedger,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode streamSchedule,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode regularSource,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode dyadicArithmetic,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode realSeal,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyCutTasteGate_single_carrier_alignment_decode_encode localCert]

private theorem cauchyCutToEventFlow_injective {x y : CauchyCutUp} :
    cauchyCutToEventFlow x = cauchyCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCutFromEventFlow (cauchyCutToEventFlow x) =
        cauchyCutFromEventFlow (cauchyCutToEventFlow y) :=
    congrArg cauchyCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyCut_round_trip x).symm (Eq.trans hread (cauchyCut_round_trip y)))

instance cauchyCutBHistCarrier : BHistCarrier CauchyCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCutToEventFlow
  fromEventFlow := cauchyCutFromEventFlow

instance cauchyCutChapterTasteGate : ChapterTasteGate CauchyCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyCutFromEventFlow (cauchyCutToEventFlow x) = some x
    exact cauchyCut_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyCutToEventFlow_injective heq)

theorem CauchyCutTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyCutDecodeBHist (cauchyCutEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCutUp) ∧
      Nonempty (ChapterTasteGate CauchyCutUp) ∧
      cauchyCutEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyCutTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact Nonempty.intro cauchyCutBHistCarrier
    · constructor
      · exact Nonempty.intro cauchyCutChapterTasteGate
      · rfl

end BEDC.Derived.CauchyCutUp
