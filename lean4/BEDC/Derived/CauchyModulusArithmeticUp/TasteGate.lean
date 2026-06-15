import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusArithmeticUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyModulusArithmeticUp : Type where
  | mk (S0 S1 mu0 mu1 muMeet sigma pi D W R E H C P N : BHist) :
      CauchyModulusArithmeticUp
  deriving DecidableEq

def cauchyModulusArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusArithmeticEncodeBHist h

def cauchyModulusArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusArithmeticDecodeBHist tail)

private theorem CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusArithmeticToEventFlow : CauchyModulusArithmeticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusArithmeticUp.mk S0 S1 mu0 mu1 muMeet sigma pi D W R E H C P N =>
      [cauchyModulusArithmeticEncodeBHist S0,
        cauchyModulusArithmeticEncodeBHist S1,
        cauchyModulusArithmeticEncodeBHist mu0,
        cauchyModulusArithmeticEncodeBHist mu1,
        cauchyModulusArithmeticEncodeBHist muMeet,
        cauchyModulusArithmeticEncodeBHist sigma,
        cauchyModulusArithmeticEncodeBHist pi,
        cauchyModulusArithmeticEncodeBHist D,
        cauchyModulusArithmeticEncodeBHist W,
        cauchyModulusArithmeticEncodeBHist R,
        cauchyModulusArithmeticEncodeBHist E,
        cauchyModulusArithmeticEncodeBHist H,
        cauchyModulusArithmeticEncodeBHist C,
        cauchyModulusArithmeticEncodeBHist P,
        cauchyModulusArithmeticEncodeBHist N]

private def cauchyModulusArithmeticEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusArithmeticEventAtDefault index rest

def cauchyModulusArithmeticFromEventFlow (ef : EventFlow) :
    Option CauchyModulusArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusArithmeticUp.mk
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 0 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 1 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 2 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 3 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 4 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 5 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 6 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 7 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 8 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 9 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 10 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 11 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 12 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 13 ef))
      (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEventAtDefault 14 ef)))

private theorem CauchyModulusArithmeticTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyModulusArithmeticUp,
      cauchyModulusArithmeticFromEventFlow (cauchyModulusArithmeticToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S0 S1 mu0 mu1 muMeet sigma pi D W R E H C P N =>
      change
        some
          (CauchyModulusArithmeticUp.mk
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist S0))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist S1))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist mu0))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist mu1))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist muMeet))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist sigma))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist pi))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist D))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist W))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist R))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist E))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist H))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist C))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist P))
            (cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist N))) =
          some (CauchyModulusArithmeticUp.mk S0 S1 mu0 mu1 muMeet sigma pi D W R E H C P N)
      rw [CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode S0,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode S1,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode mu0,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode mu1,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode muMeet,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode sigma,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode pi,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode D,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode W,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode R,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode E,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode H,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode C,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode P,
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchyModulusArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyModulusArithmeticUp} :
    cauchyModulusArithmeticToEventFlow x = cauchyModulusArithmeticToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusArithmeticFromEventFlow (cauchyModulusArithmeticToEventFlow x) =
        cauchyModulusArithmeticFromEventFlow (cauchyModulusArithmeticToEventFlow y) :=
    congrArg cauchyModulusArithmeticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyModulusArithmeticTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyModulusArithmeticTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyModulusArithmeticBHistCarrier : BHistCarrier CauchyModulusArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusArithmeticToEventFlow
  fromEventFlow := cauchyModulusArithmeticFromEventFlow

instance cauchyModulusArithmeticChapterTasteGate :
    ChapterTasteGate CauchyModulusArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyModulusArithmeticFromEventFlow (cauchyModulusArithmeticToEventFlow x) =
      some x
    exact CauchyModulusArithmeticTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyModulusArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyModulusArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyModulusArithmeticChapterTasteGate

theorem CauchyModulusArithmeticTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyModulusArithmeticDecodeBHist (cauchyModulusArithmeticEncodeBHist h) = h) ∧
      (∀ x : CauchyModulusArithmeticUp,
        cauchyModulusArithmeticFromEventFlow (cauchyModulusArithmeticToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyModulusArithmeticUp,
          cauchyModulusArithmeticToEventFlow x = cauchyModulusArithmeticToEventFlow y →
            x = y) ∧
          cauchyModulusArithmeticEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyModulusArithmeticTasteGate_single_carrier_alignment_decode_encode,
      CauchyModulusArithmeticTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        CauchyModulusArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyModulusArithmeticUp.TasteGate
