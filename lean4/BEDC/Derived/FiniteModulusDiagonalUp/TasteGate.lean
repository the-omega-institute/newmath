import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteModulusDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteModulusDiagonalUp : Type where
  | mk (M S T Q E H C P : BHist) : FiniteModulusDiagonalUp
  deriving DecidableEq

def finiteModulusDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteModulusDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteModulusDiagonalEncodeBHist h

def finiteModulusDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteModulusDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteModulusDiagonalDecodeBHist tail)

private theorem finiteModulusDiagonal_decode_encode :
    ∀ h : BHist, finiteModulusDiagonalDecodeBHist (finiteModulusDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteModulusDiagonalFields : FiniteModulusDiagonalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteModulusDiagonalUp.mk M S T Q E H C P => [M, S, T, Q, E, H, C, P]

def finiteModulusDiagonalToEventFlow : FiniteModulusDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteModulusDiagonalFields x).map finiteModulusDiagonalEncodeBHist

def finiteModulusDiagonalFromEventFlow : EventFlow → Option FiniteModulusDiagonalUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: S :: T :: Q :: E :: H :: C :: P :: [] =>
      some
        (FiniteModulusDiagonalUp.mk
          (finiteModulusDiagonalDecodeBHist M)
          (finiteModulusDiagonalDecodeBHist S)
          (finiteModulusDiagonalDecodeBHist T)
          (finiteModulusDiagonalDecodeBHist Q)
          (finiteModulusDiagonalDecodeBHist E)
          (finiteModulusDiagonalDecodeBHist H)
          (finiteModulusDiagonalDecodeBHist C)
          (finiteModulusDiagonalDecodeBHist P))
  | _ => none

private theorem finiteModulusDiagonal_round_trip (x : FiniteModulusDiagonalUp) :
    finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M S T Q E H C P =>
      simp only [finiteModulusDiagonalToEventFlow, finiteModulusDiagonalFields,
        finiteModulusDiagonalFromEventFlow, List.map_cons, List.map_nil,
        finiteModulusDiagonal_decode_encode]

private theorem finiteModulusDiagonalToEventFlow_injective
    {x y : FiniteModulusDiagonalUp} :
    finiteModulusDiagonalToEventFlow x = finiteModulusDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow x) :=
        (finiteModulusDiagonal_round_trip x).symm
      _ = finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow y) :=
        congrArg finiteModulusDiagonalFromEventFlow hxy
      _ = some y := finiteModulusDiagonal_round_trip y
  exact Option.some.inj optionEq

instance finiteModulusDiagonalBHistCarrier : BHistCarrier FiniteModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteModulusDiagonalToEventFlow
  fromEventFlow := finiteModulusDiagonalFromEventFlow

instance finiteModulusDiagonalChapterTasteGate :
    ChapterTasteGate FiniteModulusDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteModulusDiagonalFromEventFlow (finiteModulusDiagonalToEventFlow x) = some x
    exact finiteModulusDiagonal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteModulusDiagonalToEventFlow_injective heq)

theorem FiniteModulusDiagonalTasteGate_single_carrier_alignment :
    finiteModulusDiagonalFromEventFlow
        (finiteModulusDiagonalToEventFlow
          (FiniteModulusDiagonalUp.mk BHist.Empty (BHist.e0 BHist.Empty)
            (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty)) =
      some
        (FiniteModulusDiagonalUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty) ∧
    finiteModulusDiagonalFields
        (FiniteModulusDiagonalUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty) =
      [BHist.Empty, BHist.e0 BHist.Empty, BHist.e1 BHist.Empty, BHist.Empty,
        BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact
      finiteModulusDiagonal_round_trip
        (FiniteModulusDiagonalUp.mk BHist.Empty (BHist.e0 BHist.Empty)
          (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty)
  · rfl

end BEDC.Derived.FiniteModulusDiagonalUp
