import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusCauchyCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusCauchyCompletionUp : Type where
  | mk
      (modulus stream regular dyadic endpoint transport replay provenance localName :
        BHist) : ModulusCauchyCompletionUp
  deriving DecidableEq

def modulusCauchyCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusCauchyCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusCauchyCompletionEncodeBHist h

def modulusCauchyCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusCauchyCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusCauchyCompletionDecodeBHist tail)

private theorem ModulusCauchyCompletionUp_decode :
    ∀ h : BHist,
      modulusCauchyCompletionDecodeBHist
          (modulusCauchyCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusCauchyCompletionFields : ModulusCauchyCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusCauchyCompletionUp.mk modulus stream regular dyadic endpoint transport replay
      provenance localName =>
      [modulus, stream, regular, dyadic, endpoint, transport, replay, provenance,
        localName]

def modulusCauchyCompletionToEventFlow :
    ModulusCauchyCompletionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (modulusCauchyCompletionFields x).map modulusCauchyCompletionEncodeBHist

private def modulusCauchyCompletionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      modulusCauchyCompletionEventAtDefault index rest

def modulusCauchyCompletionFromEventFlow
    (ef : EventFlow) : Option ModulusCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ModulusCauchyCompletionUp.mk
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 0 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 1 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 2 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 3 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 4 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 5 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 6 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 7 ef))
      (modulusCauchyCompletionDecodeBHist
        (modulusCauchyCompletionEventAtDefault 8 ef)))

private theorem ModulusCauchyCompletionUp_round_trip
    (x : ModulusCauchyCompletionUp) :
    modulusCauchyCompletionFromEventFlow
        (modulusCauchyCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk modulus stream regular dyadic endpoint transport replay provenance localName =>
      change
        some
          (ModulusCauchyCompletionUp.mk
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist modulus))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist stream))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist regular))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist dyadic))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist endpoint))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist transport))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist replay))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist provenance))
            (modulusCauchyCompletionDecodeBHist
              (modulusCauchyCompletionEncodeBHist localName))) =
          some
            (ModulusCauchyCompletionUp.mk modulus stream regular dyadic endpoint
              transport replay provenance localName)
      rw [ModulusCauchyCompletionUp_decode modulus,
        ModulusCauchyCompletionUp_decode stream,
        ModulusCauchyCompletionUp_decode regular,
        ModulusCauchyCompletionUp_decode dyadic,
        ModulusCauchyCompletionUp_decode endpoint,
        ModulusCauchyCompletionUp_decode transport,
        ModulusCauchyCompletionUp_decode replay,
        ModulusCauchyCompletionUp_decode provenance,
        ModulusCauchyCompletionUp_decode localName]

private theorem ModulusCauchyCompletionUp_toEventFlow_injective
    {x y : ModulusCauchyCompletionUp} :
    modulusCauchyCompletionToEventFlow x =
      modulusCauchyCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusCauchyCompletionFromEventFlow
          (modulusCauchyCompletionToEventFlow x) =
        modulusCauchyCompletionFromEventFlow
          (modulusCauchyCompletionToEventFlow y) :=
    congrArg modulusCauchyCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ModulusCauchyCompletionUp_round_trip x).symm
      (Eq.trans hread (ModulusCauchyCompletionUp_round_trip y)))

instance modulusCauchyCompletionBHistCarrier :
    BHistCarrier ModulusCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusCauchyCompletionToEventFlow
  fromEventFlow := modulusCauchyCompletionFromEventFlow

instance modulusCauchyCompletionChapterTasteGate :
    ChapterTasteGate ModulusCauchyCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusCauchyCompletionFromEventFlow
          (modulusCauchyCompletionToEventFlow x) = some x
    exact ModulusCauchyCompletionUp_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ModulusCauchyCompletionUp_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate ModulusCauchyCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modulusCauchyCompletionChapterTasteGate

theorem ModulusCauchyCompletionTasteGate_single_carrier_alignment :
    ChapterTasteGate ModulusCauchyCompletionUp ∧
      modulusCauchyCompletionFromEventFlow
          (modulusCauchyCompletionToEventFlow
            (ModulusCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty)) =
        some
          (ModulusCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨modulusCauchyCompletionChapterTasteGate,
      ModulusCauchyCompletionUp_round_trip
        (ModulusCauchyCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty)⟩

end BEDC.Derived.ModulusCauchyCompletionUp
