import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ZeckendorfPrimeEdgeUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ZeckendorfPrimeEdgeUp : Type where
  | mk
      (sourceWindow targetWindow recursiveOperation atomicOperation edge nondegeneracy
        irreducibility primeDivisibility ledger transport replay provenance name : BHist) :
      ZeckendorfPrimeEdgeUp
  deriving DecidableEq

def zeckendorfPrimeEdgeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: zeckendorfPrimeEdgeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: zeckendorfPrimeEdgeEncodeBHist h

def zeckendorfPrimeEdgeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (zeckendorfPrimeEdgeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (zeckendorfPrimeEdgeDecodeBHist tail)

private theorem zeckendorfPrimeEdgeDecodeEncode :
    ∀ h : BHist,
      zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def zeckendorfPrimeEdgeFields : ZeckendorfPrimeEdgeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ZeckendorfPrimeEdgeUp.mk sourceWindow targetWindow recursiveOperation atomicOperation
      edge nondegeneracy irreducibility primeDivisibility ledger transport replay provenance
      name =>
      [sourceWindow, targetWindow, recursiveOperation, atomicOperation, edge, nondegeneracy,
        irreducibility, primeDivisibility, ledger, transport, replay, provenance, name]

def zeckendorfPrimeEdgeToEventFlow : ZeckendorfPrimeEdgeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (zeckendorfPrimeEdgeFields x).map zeckendorfPrimeEdgeEncodeBHist

private def zeckendorfPrimeEdgeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => zeckendorfPrimeEdgeEventAtDefault index rest

def zeckendorfPrimeEdgeFromEventFlow (ef : EventFlow) : Option ZeckendorfPrimeEdgeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ZeckendorfPrimeEdgeUp.mk
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 0 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 1 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 2 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 3 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 4 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 5 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 6 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 7 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 8 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 9 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 10 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 11 ef))
      (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEventAtDefault 12 ef)))

private theorem zeckendorfPrimeEdgeRoundTrip :
    ∀ x : ZeckendorfPrimeEdgeUp,
      zeckendorfPrimeEdgeFromEventFlow (zeckendorfPrimeEdgeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sourceWindow targetWindow recursiveOperation atomicOperation edge nondegeneracy
      irreducibility primeDivisibility ledger transport replay provenance name =>
      change
        some
          (ZeckendorfPrimeEdgeUp.mk
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist sourceWindow))
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist targetWindow))
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist recursiveOperation))
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist atomicOperation))
            (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist edge))
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist nondegeneracy))
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist irreducibility))
            (zeckendorfPrimeEdgeDecodeBHist
              (zeckendorfPrimeEdgeEncodeBHist primeDivisibility))
            (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist ledger))
            (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist transport))
            (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist replay))
            (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist provenance))
            (zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist name))) =
          some
            (ZeckendorfPrimeEdgeUp.mk sourceWindow targetWindow recursiveOperation
              atomicOperation edge nondegeneracy irreducibility primeDivisibility ledger
              transport replay provenance name)
      rw [zeckendorfPrimeEdgeDecodeEncode sourceWindow,
        zeckendorfPrimeEdgeDecodeEncode targetWindow,
        zeckendorfPrimeEdgeDecodeEncode recursiveOperation,
        zeckendorfPrimeEdgeDecodeEncode atomicOperation,
        zeckendorfPrimeEdgeDecodeEncode edge,
        zeckendorfPrimeEdgeDecodeEncode nondegeneracy,
        zeckendorfPrimeEdgeDecodeEncode irreducibility,
        zeckendorfPrimeEdgeDecodeEncode primeDivisibility,
        zeckendorfPrimeEdgeDecodeEncode ledger,
        zeckendorfPrimeEdgeDecodeEncode transport,
        zeckendorfPrimeEdgeDecodeEncode replay,
        zeckendorfPrimeEdgeDecodeEncode provenance,
        zeckendorfPrimeEdgeDecodeEncode name]

private theorem zeckendorfPrimeEdgeToEventFlow_injective_private
    {x y : ZeckendorfPrimeEdgeUp} :
    zeckendorfPrimeEdgeToEventFlow x = zeckendorfPrimeEdgeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      zeckendorfPrimeEdgeFromEventFlow (zeckendorfPrimeEdgeToEventFlow x) =
        zeckendorfPrimeEdgeFromEventFlow (zeckendorfPrimeEdgeToEventFlow y) :=
    congrArg zeckendorfPrimeEdgeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (zeckendorfPrimeEdgeRoundTrip x).symm
      (Eq.trans hread (zeckendorfPrimeEdgeRoundTrip y)))

instance zeckendorfPrimeEdgeBHistCarrier : BHistCarrier ZeckendorfPrimeEdgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := zeckendorfPrimeEdgeToEventFlow
  fromEventFlow := zeckendorfPrimeEdgeFromEventFlow

instance zeckendorfPrimeEdgeChapterTasteGate :
    ChapterTasteGate ZeckendorfPrimeEdgeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      zeckendorfPrimeEdgeFromEventFlow (zeckendorfPrimeEdgeToEventFlow x) = some x
    exact zeckendorfPrimeEdgeRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (zeckendorfPrimeEdgeToEventFlow_injective_private heq)

theorem ZeckendorfPrimeEdgeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        zeckendorfPrimeEdgeDecodeBHist (zeckendorfPrimeEdgeEncodeBHist h) = h) ∧
      (∀ x : ZeckendorfPrimeEdgeUp,
        zeckendorfPrimeEdgeFromEventFlow (zeckendorfPrimeEdgeToEventFlow x) = some x) ∧
        (∀ x y : ZeckendorfPrimeEdgeUp,
          zeckendorfPrimeEdgeToEventFlow x = zeckendorfPrimeEdgeToEventFlow y → x = y) ∧
          zeckendorfPrimeEdgeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨zeckendorfPrimeEdgeDecodeEncode,
      zeckendorfPrimeEdgeRoundTrip,
      fun _x _y heq => zeckendorfPrimeEdgeToEventFlow_injective_private heq,
      rfl⟩

end BEDC.Derived.ZeckendorfPrimeEdgeUp.TasteGate
