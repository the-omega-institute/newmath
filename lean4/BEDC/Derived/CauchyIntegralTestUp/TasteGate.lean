import BEDC.FKernel.Ask
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyIntegralTestUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyIntegralTestUp : Type where
  | mk (F I S W R H C P N : BHist) : CauchyIntegralTestUp

def cauchyIntegralTestEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyIntegralTestEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyIntegralTestEncodeBHist h

def cauchyIntegralTestDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyIntegralTestDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyIntegralTestDecodeBHist tail)

private theorem cauchyIntegralTest_decode_encode_bhist :
    ∀ h : BHist,
      cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyIntegralTestFields : CauchyIntegralTestUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyIntegralTestUp.mk F I S W R H C P N =>
      [F, I, S, W, R, H, C, P, N]

def cauchyIntegralTestToEventFlow : CauchyIntegralTestUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyIntegralTestFields x).map cauchyIntegralTestEncodeBHist

private def cauchyIntegralTestEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyIntegralTestEventAtDefault index rest

def cauchyIntegralTestFromEventFlow (flow : EventFlow) : Option CauchyIntegralTestUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyIntegralTestUp.mk
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 0 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 1 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 2 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 3 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 4 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 5 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 6 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 7 flow))
      (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEventAtDefault 8 flow)))

private theorem cauchyIntegralTest_round_trip :
    ∀ x : CauchyIntegralTestUp,
      cauchyIntegralTestFromEventFlow (cauchyIntegralTestToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I S W R H C P N =>
      change
        some
          (CauchyIntegralTestUp.mk
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist F))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist I))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist S))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist W))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist R))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist H))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist C))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist P))
            (cauchyIntegralTestDecodeBHist (cauchyIntegralTestEncodeBHist N))) =
          some (CauchyIntegralTestUp.mk F I S W R H C P N)
      rw [cauchyIntegralTest_decode_encode_bhist F,
        cauchyIntegralTest_decode_encode_bhist I,
        cauchyIntegralTest_decode_encode_bhist S,
        cauchyIntegralTest_decode_encode_bhist W,
        cauchyIntegralTest_decode_encode_bhist R,
        cauchyIntegralTest_decode_encode_bhist H,
        cauchyIntegralTest_decode_encode_bhist C,
        cauchyIntegralTest_decode_encode_bhist P,
        cauchyIntegralTest_decode_encode_bhist N]

private theorem cauchyIntegralTestToEventFlow_injective {x y : CauchyIntegralTestUp} :
    cauchyIntegralTestToEventFlow x = cauchyIntegralTestToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyIntegralTestFromEventFlow (cauchyIntegralTestToEventFlow x) =
        cauchyIntegralTestFromEventFlow (cauchyIntegralTestToEventFlow y) :=
    congrArg cauchyIntegralTestFromEventFlow heq
  exact
    Option.some.inj
      (Eq.trans (cauchyIntegralTest_round_trip x).symm
        (Eq.trans hread (cauchyIntegralTest_round_trip y)))

instance cauchyIntegralTestBHistCarrier : BHistCarrier CauchyIntegralTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyIntegralTestToEventFlow
  fromEventFlow := cauchyIntegralTestFromEventFlow

instance cauchyIntegralTestChapterTasteGate : ChapterTasteGate CauchyIntegralTestUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyIntegralTestFromEventFlow (cauchyIntegralTestToEventFlow x) = some x
    exact cauchyIntegralTest_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyIntegralTestToEventFlow_injective heq)

theorem CauchyIntegralTestCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (B : CauchyIntegralTestUp) :
    SemanticNameCert
        (fun row : BHist => row ∈ cauchyIntegralTestFields B)
        (fun row : BHist => row ∈ cauchyIntegralTestFields B)
        (fun row : BHist => row ∈ cauchyIntegralTestFields B)
        hsame ∧
      Nonempty (ChapterTasteGate CauchyIntegralTestUp) := by
  -- BEDC touchpoint anchor: BHist BMark SemanticNameCert hsame ChapterTasteGate
  have sourceWitness :
      ∃ row : BHist, row ∈ cauchyIntegralTestFields B := by
    cases B with
    | mk F I S W R H C P N =>
        exact Exists.intro F (List.Mem.head [I, S, W, R, H, C, P, N])
  have cert :
      SemanticNameCert
          (fun row : BHist => row ∈ cauchyIntegralTestFields B)
          (fun row : BHist => row ∈ cauchyIntegralTestFields B)
          (fun row : BHist => row ∈ cauchyIntegralTestFields B)
          hsame := {
    core := {
      carrier_inhabited := sourceWitness
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact ⟨cert, ⟨cauchyIntegralTestChapterTasteGate⟩⟩

end BEDC.Derived.CauchyIntegralTestUp
