import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BairePointwiseOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BairePointwiseOscillationUp : Type where
  | mk (X F S Qm Qp Rm Rp B H C P N : BHist) : BairePointwiseOscillationUp

def bairePointwiseOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bairePointwiseOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bairePointwiseOscillationEncodeBHist h

def bairePointwiseOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bairePointwiseOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bairePointwiseOscillationDecodeBHist tail)

private theorem bairePointwiseOscillationDecodeEncode :
    ∀ h : BHist,
      bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bairePointwiseOscillationFields : BairePointwiseOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BairePointwiseOscillationUp.mk X F S Qm Qp Rm Rp B H C P N =>
      [X, F, S, Qm, Qp, Rm, Rp, B, H, C, P, N]

def bairePointwiseOscillationToEventFlow : BairePointwiseOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bairePointwiseOscillationFields x).map bairePointwiseOscillationEncodeBHist

private def bairePointwiseOscillationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bairePointwiseOscillationEventAtDefault index rest

def bairePointwiseOscillationFromEventFlow
    (ef : EventFlow) : Option BairePointwiseOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BairePointwiseOscillationUp.mk
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 0 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 1 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 2 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 3 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 4 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 5 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 6 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 7 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 8 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 9 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 10 ef))
      (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAtDefault 11 ef)))

private theorem bairePointwiseOscillation_round_trip (x : BairePointwiseOscillationUp) :
    bairePointwiseOscillationFromEventFlow (bairePointwiseOscillationToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X F S Qm Qp Rm Rp B H C P N =>
      change
        some
          (BairePointwiseOscillationUp.mk
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist X))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist F))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist S))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist Qm))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist Qp))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist Rm))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist Rp))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist B))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist H))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist C))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist P))
            (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist N))) =
          some (BairePointwiseOscillationUp.mk X F S Qm Qp Rm Rp B H C P N)
      rw [bairePointwiseOscillationDecodeEncode X, bairePointwiseOscillationDecodeEncode F,
        bairePointwiseOscillationDecodeEncode S, bairePointwiseOscillationDecodeEncode Qm,
        bairePointwiseOscillationDecodeEncode Qp, bairePointwiseOscillationDecodeEncode Rm,
        bairePointwiseOscillationDecodeEncode Rp, bairePointwiseOscillationDecodeEncode B,
        bairePointwiseOscillationDecodeEncode H, bairePointwiseOscillationDecodeEncode C,
        bairePointwiseOscillationDecodeEncode P, bairePointwiseOscillationDecodeEncode N]

private theorem bairePointwiseOscillationToEventFlow_injective
    {x y : BairePointwiseOscillationUp} :
    bairePointwiseOscillationToEventFlow x = bairePointwiseOscillationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bairePointwiseOscillationFromEventFlow (bairePointwiseOscillationToEventFlow x) =
        bairePointwiseOscillationFromEventFlow (bairePointwiseOscillationToEventFlow y) :=
    congrArg bairePointwiseOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bairePointwiseOscillation_round_trip x).symm
      (Eq.trans hread (bairePointwiseOscillation_round_trip y)))

instance bairePointwiseOscillationBHistCarrier : BHistCarrier BairePointwiseOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bairePointwiseOscillationToEventFlow
  fromEventFlow := bairePointwiseOscillationFromEventFlow

instance bairePointwiseOscillationChapterTasteGate :
    ChapterTasteGate BairePointwiseOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bairePointwiseOscillationFromEventFlow (bairePointwiseOscillationToEventFlow x) =
        some x
    exact bairePointwiseOscillation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bairePointwiseOscillationToEventFlow_injective heq)

theorem BairePointwiseOscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BairePointwiseOscillationUp) ∧
        Nonempty (ChapterTasteGate BairePointwiseOscillationUp) ∧
          bairePointwiseOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨bairePointwiseOscillationDecodeEncode,
      ⟨⟨bairePointwiseOscillationBHistCarrier⟩,
        ⟨⟨bairePointwiseOscillationChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.BairePointwiseOscillationUp
