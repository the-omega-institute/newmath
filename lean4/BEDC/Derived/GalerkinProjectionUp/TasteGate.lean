import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GalerkinProjectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GalerkinProjectionUp : Type where
  | mk (S H L M V B A b u r O T C P N : BHist) : GalerkinProjectionUp
  deriving DecidableEq

def GalerkinProjectionUp_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: GalerkinProjectionUp_encodeBHist h
  | BHist.e1 h => BMark.b1 :: GalerkinProjectionUp_encodeBHist h

def GalerkinProjectionUp_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (GalerkinProjectionUp_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (GalerkinProjectionUp_decodeBHist tail)

private theorem GalerkinProjectionUp_decode_round_trip :
    ∀ h : BHist,
      GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def GalerkinProjectionUp_fields : GalerkinProjectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GalerkinProjectionUp.mk S H L M V B A b u r O T C P N =>
      [S, H, L, M, V, B, A, b, u, r, O, T, C, P, N]

def GalerkinProjectionUp_toEventFlow : GalerkinProjectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (GalerkinProjectionUp_fields x).map GalerkinProjectionUp_encodeBHist

def GalerkinProjectionUp_fromEventFlow : EventFlow → Option GalerkinProjectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, H, L, M, V, B, A, b, u, r, O, T, C, P, N] =>
      some
        (GalerkinProjectionUp.mk
          (GalerkinProjectionUp_decodeBHist S)
          (GalerkinProjectionUp_decodeBHist H)
          (GalerkinProjectionUp_decodeBHist L)
          (GalerkinProjectionUp_decodeBHist M)
          (GalerkinProjectionUp_decodeBHist V)
          (GalerkinProjectionUp_decodeBHist B)
          (GalerkinProjectionUp_decodeBHist A)
          (GalerkinProjectionUp_decodeBHist b)
          (GalerkinProjectionUp_decodeBHist u)
          (GalerkinProjectionUp_decodeBHist r)
          (GalerkinProjectionUp_decodeBHist O)
          (GalerkinProjectionUp_decodeBHist T)
          (GalerkinProjectionUp_decodeBHist C)
          (GalerkinProjectionUp_decodeBHist P)
          (GalerkinProjectionUp_decodeBHist N))
  | _ => none

private theorem GalerkinProjectionUp_round_trip (x : GalerkinProjectionUp) :
    GalerkinProjectionUp_fromEventFlow (GalerkinProjectionUp_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S H L M V B A b u r O T C P N =>
      change
        some
          (GalerkinProjectionUp.mk
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist S))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist H))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist L))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist M))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist V))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist B))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist A))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist b))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist u))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist r))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist O))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist T))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist C))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist P))
            (GalerkinProjectionUp_decodeBHist (GalerkinProjectionUp_encodeBHist N))) =
          some (GalerkinProjectionUp.mk S H L M V B A b u r O T C P N)
      rw [GalerkinProjectionUp_decode_round_trip S,
        GalerkinProjectionUp_decode_round_trip H,
        GalerkinProjectionUp_decode_round_trip L,
        GalerkinProjectionUp_decode_round_trip M,
        GalerkinProjectionUp_decode_round_trip V,
        GalerkinProjectionUp_decode_round_trip B,
        GalerkinProjectionUp_decode_round_trip A,
        GalerkinProjectionUp_decode_round_trip b,
        GalerkinProjectionUp_decode_round_trip u,
        GalerkinProjectionUp_decode_round_trip r,
        GalerkinProjectionUp_decode_round_trip O,
        GalerkinProjectionUp_decode_round_trip T,
        GalerkinProjectionUp_decode_round_trip C,
        GalerkinProjectionUp_decode_round_trip P,
        GalerkinProjectionUp_decode_round_trip N]

private theorem GalerkinProjectionUp_toEventFlow_injective {x y : GalerkinProjectionUp} :
    GalerkinProjectionUp_toEventFlow x = GalerkinProjectionUp_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      GalerkinProjectionUp_fromEventFlow (GalerkinProjectionUp_toEventFlow x) =
        GalerkinProjectionUp_fromEventFlow (GalerkinProjectionUp_toEventFlow y) :=
    congrArg GalerkinProjectionUp_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GalerkinProjectionUp_round_trip x).symm
      (Eq.trans hread (GalerkinProjectionUp_round_trip y)))

instance GalerkinProjectionUp_BHistCarrier : BHistCarrier GalerkinProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := GalerkinProjectionUp_toEventFlow
  fromEventFlow := GalerkinProjectionUp_fromEventFlow

instance GalerkinProjectionUp_ChapterTasteGate : ChapterTasteGate GalerkinProjectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change GalerkinProjectionUp_fromEventFlow (GalerkinProjectionUp_toEventFlow x) = some x
    exact GalerkinProjectionUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GalerkinProjectionUp_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate GalerkinProjectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  GalerkinProjectionUp_ChapterTasteGate

end BEDC.Derived.GalerkinProjectionUp
