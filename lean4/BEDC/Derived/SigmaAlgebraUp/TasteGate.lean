import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SigmaAlgebraUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SigmaAlgebraUp : Type where
  | mk (E Q Z K U H C P N : BHist) : SigmaAlgebraUp
  deriving DecidableEq

def sigmaAlgebraEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sigmaAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sigmaAlgebraEncodeBHist h

def sigmaAlgebraDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sigmaAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sigmaAlgebraDecodeBHist tail)

private theorem sigmaAlgebraDecode_encode_bhist :
    ∀ h : BHist, sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def sigmaAlgebraFields : SigmaAlgebraUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SigmaAlgebraUp.mk E Q Z K U H C P N => [E, Q, Z, K, U, H, C, P, N]

def sigmaAlgebraToEventFlow : SigmaAlgebraUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (sigmaAlgebraFields x).map sigmaAlgebraEncodeBHist

private def sigmaAlgebraEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => sigmaAlgebraEventAtDefault index rest

def sigmaAlgebraFromEventFlow (ef : EventFlow) : Option SigmaAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SigmaAlgebraUp.mk
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 0 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 1 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 2 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 3 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 4 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 5 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 6 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 7 ef))
      (sigmaAlgebraDecodeBHist (sigmaAlgebraEventAtDefault 8 ef)))

private theorem sigmaAlgebra_round_trip :
    ∀ x : SigmaAlgebraUp, sigmaAlgebraFromEventFlow (sigmaAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E Q Z K U H C P N =>
      change
        some
          (SigmaAlgebraUp.mk
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist E))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist Q))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist Z))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist K))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist U))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist H))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist C))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist P))
            (sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist N))) =
          some (SigmaAlgebraUp.mk E Q Z K U H C P N)
      rw [sigmaAlgebraDecode_encode_bhist E, sigmaAlgebraDecode_encode_bhist Q,
        sigmaAlgebraDecode_encode_bhist Z, sigmaAlgebraDecode_encode_bhist K,
        sigmaAlgebraDecode_encode_bhist U, sigmaAlgebraDecode_encode_bhist H,
        sigmaAlgebraDecode_encode_bhist C, sigmaAlgebraDecode_encode_bhist P,
        sigmaAlgebraDecode_encode_bhist N]

private theorem sigmaAlgebraToEventFlow_injective {x y : SigmaAlgebraUp} :
    sigmaAlgebraToEventFlow x = sigmaAlgebraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sigmaAlgebraFromEventFlow (sigmaAlgebraToEventFlow x) =
        sigmaAlgebraFromEventFlow (sigmaAlgebraToEventFlow y) :=
    congrArg sigmaAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sigmaAlgebra_round_trip x).symm
      (Eq.trans hread (sigmaAlgebra_round_trip y)))

instance sigmaAlgebraBHistCarrier : BHistCarrier SigmaAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sigmaAlgebraToEventFlow
  fromEventFlow := sigmaAlgebraFromEventFlow

instance sigmaAlgebraChapterTasteGate : ChapterTasteGate SigmaAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sigmaAlgebraFromEventFlow (sigmaAlgebraToEventFlow x) = some x
    exact sigmaAlgebra_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sigmaAlgebraToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SigmaAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sigmaAlgebraChapterTasteGate

theorem SigmaAlgebraTasteGate_single_carrier_alignment :
    (∀ h : BHist, sigmaAlgebraDecodeBHist (sigmaAlgebraEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SigmaAlgebraUp) ∧
        Nonempty (ChapterTasteGate SigmaAlgebraUp) ∧
          sigmaAlgebraEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨sigmaAlgebraDecode_encode_bhist, ⟨sigmaAlgebraBHistCarrier⟩,
      ⟨sigmaAlgebraChapterTasteGate⟩, rfl⟩

end BEDC.Derived.SigmaAlgebraUp
