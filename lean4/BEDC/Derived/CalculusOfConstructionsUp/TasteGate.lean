import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CalculusOfConstructionsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CalculusOfConstructionsUp : Type where
  | mk (S Pi L A Gamma Sigma B R H K P N : BHist) : CalculusOfConstructionsUp
  deriving DecidableEq

def calculusOfConstructionsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: calculusOfConstructionsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: calculusOfConstructionsEncodeBHist h

def calculusOfConstructionsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (calculusOfConstructionsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (calculusOfConstructionsDecodeBHist tail)

private theorem calculusOfConstructionsDecode_encode :
    ∀ h : BHist, calculusOfConstructionsDecodeBHist
      (calculusOfConstructionsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def calculusOfConstructionsFields : CalculusOfConstructionsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CalculusOfConstructionsUp.mk S Pi L A Gamma Sigma B R H K P N =>
      [S, Pi, L, A, Gamma, Sigma, B, R, H, K, P, N]

def calculusOfConstructionsToEventFlow : CalculusOfConstructionsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (calculusOfConstructionsFields x).map calculusOfConstructionsEncodeBHist

private def calculusOfConstructionsEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => calculusOfConstructionsEventAtDefault index rest

def calculusOfConstructionsFromEventFlow
    (ef : EventFlow) : Option CalculusOfConstructionsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CalculusOfConstructionsUp.mk
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 0 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 1 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 2 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 3 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 4 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 5 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 6 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 7 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 8 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 9 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 10 ef))
      (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEventAtDefault 11 ef)))

private theorem calculusOfConstructionsRoundTrip :
    ∀ x : CalculusOfConstructionsUp,
      calculusOfConstructionsFromEventFlow (calculusOfConstructionsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Pi L A Gamma Sigma B R H K P N =>
      change
        some
          (CalculusOfConstructionsUp.mk
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist S))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist Pi))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist L))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist A))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist Gamma))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist Sigma))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist B))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist R))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist H))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist K))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist P))
            (calculusOfConstructionsDecodeBHist (calculusOfConstructionsEncodeBHist N))) =
          some (CalculusOfConstructionsUp.mk S Pi L A Gamma Sigma B R H K P N)
      rw [calculusOfConstructionsDecode_encode S, calculusOfConstructionsDecode_encode Pi,
        calculusOfConstructionsDecode_encode L, calculusOfConstructionsDecode_encode A,
        calculusOfConstructionsDecode_encode Gamma, calculusOfConstructionsDecode_encode Sigma,
        calculusOfConstructionsDecode_encode B, calculusOfConstructionsDecode_encode R,
        calculusOfConstructionsDecode_encode H, calculusOfConstructionsDecode_encode K,
        calculusOfConstructionsDecode_encode P, calculusOfConstructionsDecode_encode N]

private theorem calculusOfConstructionsToEventFlow_injective
    {x y : CalculusOfConstructionsUp} :
    calculusOfConstructionsToEventFlow x = calculusOfConstructionsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      calculusOfConstructionsFromEventFlow (calculusOfConstructionsToEventFlow x) =
        calculusOfConstructionsFromEventFlow (calculusOfConstructionsToEventFlow y) :=
    congrArg calculusOfConstructionsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (calculusOfConstructionsRoundTrip x).symm
      (Eq.trans hread (calculusOfConstructionsRoundTrip y)))

instance calculusOfConstructionsBHistCarrier : BHistCarrier CalculusOfConstructionsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := calculusOfConstructionsToEventFlow
  fromEventFlow := calculusOfConstructionsFromEventFlow

instance calculusOfConstructionsChapterTasteGate :
    ChapterTasteGate CalculusOfConstructionsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      calculusOfConstructionsFromEventFlow (calculusOfConstructionsToEventFlow x) = some x
    exact calculusOfConstructionsRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (calculusOfConstructionsToEventFlow_injective heq)

theorem CalculusOfConstructionsTasteGate_single_carrier_alignment :
    calculusOfConstructionsEncodeBHist BHist.Empty = ([] : List BMark) ∧
      Nonempty CalculusOfConstructionsUp ∧ Nonempty (BHistCarrier CalculusOfConstructionsUp) ∧
        Nonempty (ChapterTasteGate CalculusOfConstructionsUp) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨rfl,
      ⟨CalculusOfConstructionsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty⟩,
      ⟨calculusOfConstructionsBHistCarrier⟩,
      ⟨calculusOfConstructionsChapterTasteGate⟩⟩

end BEDC.Derived.CalculusOfConstructionsUp
