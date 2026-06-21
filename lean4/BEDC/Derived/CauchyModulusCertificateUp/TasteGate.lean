import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusCertificateUp : Type where
  | mk (D W Q M E H C P N : BHist) : CauchyModulusCertificateUp
  deriving DecidableEq

def cauchyModulusCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusCertificateEncodeBHist h

def cauchyModulusCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusCertificateDecodeBHist tail)

private theorem cauchyModulusCertificate_decode_encode :
    ∀ h : BHist,
      cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusCertificateToEventFlow : CauchyModulusCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusCertificateUp.mk D W Q M E H C P N =>
      [cauchyModulusCertificateEncodeBHist D,
        cauchyModulusCertificateEncodeBHist W,
        cauchyModulusCertificateEncodeBHist Q,
        cauchyModulusCertificateEncodeBHist M,
        cauchyModulusCertificateEncodeBHist E,
        cauchyModulusCertificateEncodeBHist H,
        cauchyModulusCertificateEncodeBHist C,
        cauchyModulusCertificateEncodeBHist P,
        cauchyModulusCertificateEncodeBHist N]

private def cauchyModulusCertificateEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusCertificateEventAt index rest

def cauchyModulusCertificateFromEventFlow
    (ef : EventFlow) : Option CauchyModulusCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusCertificateUp.mk
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 0 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 1 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 2 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 3 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 4 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 5 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 6 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 7 ef))
      (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEventAt 8 ef)))

private theorem cauchyModulusCertificate_round_trip (x : CauchyModulusCertificateUp) :
    cauchyModulusCertificateFromEventFlow (cauchyModulusCertificateToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D W Q M E H C P N =>
      change
        some
          (CauchyModulusCertificateUp.mk
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist D))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist W))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist Q))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist M))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist E))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist H))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist C))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist P))
            (cauchyModulusCertificateDecodeBHist (cauchyModulusCertificateEncodeBHist N))) =
          some (CauchyModulusCertificateUp.mk D W Q M E H C P N)
      rw [cauchyModulusCertificate_decode_encode D, cauchyModulusCertificate_decode_encode W,
        cauchyModulusCertificate_decode_encode Q, cauchyModulusCertificate_decode_encode M,
        cauchyModulusCertificate_decode_encode E, cauchyModulusCertificate_decode_encode H,
        cauchyModulusCertificate_decode_encode C, cauchyModulusCertificate_decode_encode P,
        cauchyModulusCertificate_decode_encode N]

private theorem cauchyModulusCertificateToEventFlow_injective
    {x y : CauchyModulusCertificateUp} :
    cauchyModulusCertificateToEventFlow x = cauchyModulusCertificateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusCertificateFromEventFlow (cauchyModulusCertificateToEventFlow x) =
        cauchyModulusCertificateFromEventFlow (cauchyModulusCertificateToEventFlow y) :=
    congrArg cauchyModulusCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyModulusCertificate_round_trip x).symm
      (Eq.trans hread (cauchyModulusCertificate_round_trip y)))

instance cauchyModulusCertificateBHistCarrier : BHistCarrier CauchyModulusCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusCertificateToEventFlow
  fromEventFlow := cauchyModulusCertificateFromEventFlow

instance cauchyModulusCertificateChapterTasteGate :
    ChapterTasteGate CauchyModulusCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyModulusCertificateFromEventFlow (cauchyModulusCertificateToEventFlow x) =
        some x
    exact cauchyModulusCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyModulusCertificateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusCertificateChapterTasteGate

theorem CauchyModulusCertificateTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyModulusCertificateUp) ∧
      Nonempty (ChapterTasteGate CauchyModulusCertificateUp) ∧
        cauchyModulusCertificateEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyModulusCertificateBHistCarrier⟩,
      ⟨cauchyModulusCertificateChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyModulusCertificateUp
