import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactUniformModulusCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactUniformModulusCertificateUp : Type where
  | mk (K F L Q S T U H C P N : BHist) : CompactUniformModulusCertificateUp
  deriving DecidableEq

def compactUniformModulusCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactUniformModulusCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactUniformModulusCertificateEncodeBHist h

def compactUniformModulusCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactUniformModulusCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactUniformModulusCertificateDecodeBHist tail)

private theorem compactUniformModulusCertificate_decode_encode_bhist :
    ∀ h : BHist,
      compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactUniformModulusCertificateFields :
    CompactUniformModulusCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactUniformModulusCertificateUp.mk K F L Q S T U H C P N =>
      [K, F, L, Q, S, T, U, H, C, P, N]

def compactUniformModulusCertificateToEventFlow :
    CompactUniformModulusCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactUniformModulusCertificateFields x).map
        compactUniformModulusCertificateEncodeBHist

private def compactUniformModulusCertificateEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => compactUniformModulusCertificateEventAt index rest

def compactUniformModulusCertificateFromEventFlow
    (ef : EventFlow) : Option CompactUniformModulusCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompactUniformModulusCertificateUp.mk
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 0 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 1 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 2 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 3 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 4 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 5 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 6 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 7 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 8 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 9 ef))
      (compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEventAt 10 ef)))

private theorem compactUniformModulusCertificate_round_trip
    (x : CompactUniformModulusCertificateUp) :
    compactUniformModulusCertificateFromEventFlow
        (compactUniformModulusCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F L Q S T U H C P N =>
      change
        some
          (CompactUniformModulusCertificateUp.mk
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist K))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist F))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist L))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist Q))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist S))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist T))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist U))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist H))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist C))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist P))
            (compactUniformModulusCertificateDecodeBHist
              (compactUniformModulusCertificateEncodeBHist N))) =
          some (CompactUniformModulusCertificateUp.mk K F L Q S T U H C P N)
      rw [compactUniformModulusCertificate_decode_encode_bhist K,
        compactUniformModulusCertificate_decode_encode_bhist F,
        compactUniformModulusCertificate_decode_encode_bhist L,
        compactUniformModulusCertificate_decode_encode_bhist Q,
        compactUniformModulusCertificate_decode_encode_bhist S,
        compactUniformModulusCertificate_decode_encode_bhist T,
        compactUniformModulusCertificate_decode_encode_bhist U,
        compactUniformModulusCertificate_decode_encode_bhist H,
        compactUniformModulusCertificate_decode_encode_bhist C,
        compactUniformModulusCertificate_decode_encode_bhist P,
        compactUniformModulusCertificate_decode_encode_bhist N]

private theorem compactUniformModulusCertificateToEventFlow_injective
    {x y : CompactUniformModulusCertificateUp} :
    compactUniformModulusCertificateToEventFlow x =
      compactUniformModulusCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactUniformModulusCertificateFromEventFlow
          (compactUniformModulusCertificateToEventFlow x) =
        compactUniformModulusCertificateFromEventFlow
          (compactUniformModulusCertificateToEventFlow y) :=
    congrArg compactUniformModulusCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactUniformModulusCertificate_round_trip x).symm
      (Eq.trans hread (compactUniformModulusCertificate_round_trip y)))

instance compactUniformModulusCertificateBHistCarrier :
    BHistCarrier CompactUniformModulusCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactUniformModulusCertificateToEventFlow
  fromEventFlow := compactUniformModulusCertificateFromEventFlow

instance compactUniformModulusCertificateChapterTasteGate :
    ChapterTasteGate CompactUniformModulusCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactUniformModulusCertificateFromEventFlow
          (compactUniformModulusCertificateToEventFlow x) =
        some x
    exact compactUniformModulusCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactUniformModulusCertificateToEventFlow_injective heq)

theorem CompactUniformModulusCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactUniformModulusCertificateDecodeBHist
        (compactUniformModulusCertificateEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CompactUniformModulusCertificateUp) ∧
        Nonempty (ChapterTasteGate CompactUniformModulusCertificateUp) ∧
          compactUniformModulusCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact compactUniformModulusCertificate_decode_encode_bhist
  · constructor
    · exact ⟨compactUniformModulusCertificateBHistCarrier⟩
    · constructor
      · exact ⟨compactUniformModulusCertificateChapterTasteGate⟩
      · rfl

end BEDC.Derived.CompactUniformModulusCertificateUp
