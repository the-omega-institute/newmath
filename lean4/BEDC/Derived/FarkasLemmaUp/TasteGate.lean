import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FarkasLemmaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FarkasLemmaUp : Type where
  | mk (I J F A b rho nu eta H C P N : BHist) : FarkasLemmaUp
  deriving DecidableEq

def FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist h

def FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem FarkasLemmaTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist
          (FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def FarkasLemmaTasteGate_single_carrier_alignment_fields :
    FarkasLemmaUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FarkasLemmaUp.mk I J F A b rho nu eta H C P N =>
      [I, J, F, A, b, rho, nu, eta, H, C, P, N]

def FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow :
    FarkasLemmaUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (FarkasLemmaTasteGate_single_carrier_alignment_fields x).map
      FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist

def FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option FarkasLemmaUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | I :: J :: F :: A :: b :: rho :: nu :: eta :: H :: C :: P :: N :: [] =>
      some
        (FarkasLemmaUp.mk
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist I)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist J)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist F)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist A)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist b)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist rho)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist nu)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist eta)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist H)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist C)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist P)
          (FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist N))
  | _ => none

private theorem FarkasLemmaTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FarkasLemmaUp,
      FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow
          (FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J F A b rho nu eta H C P N =>
      simp only [FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow,
        FarkasLemmaTasteGate_single_carrier_alignment_fields,
        FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, FarkasLemmaTasteGate_single_carrier_alignment_decode_encode]

private theorem FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FarkasLemmaUp} :
    FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow x =
        FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow
            (FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow x) :=
        (FarkasLemmaTasteGate_single_carrier_alignment_round_trip x).symm
      _ =
          FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow
            (FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow y) :=
        congrArg FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow hxy
      _ = some y := FarkasLemmaTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

instance FarkasLemmaTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier FarkasLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow

instance FarkasLemmaTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate FarkasLemmaUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      FarkasLemmaTasteGate_single_carrier_alignment_fromEventFlow
          (FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact FarkasLemmaTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FarkasLemmaTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FarkasLemmaTasteGate_single_carrier_alignment :
    (∀ I J F A b rho nu eta H C P N : BHist,
      FarkasLemmaTasteGate_single_carrier_alignment_fields
          (FarkasLemmaUp.mk I J F A b rho nu eta H C P N) =
        [I, J, F, A, b, rho, nu, eta, H, C, P, N]) ∧
      (∀ h : BHist,
        FarkasLemmaTasteGate_single_carrier_alignment_decodeBHist
            (FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist h) =
          h) ∧
        FarkasLemmaTasteGate_single_carrier_alignment_encodeBHist (BHist.e1 BHist.Empty) =
          [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨(fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl),
      FarkasLemmaTasteGate_single_carrier_alignment_decode_encode, rfl⟩

end BEDC.Derived.FarkasLemmaUp
