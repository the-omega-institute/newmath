import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompletionUniversalPropertyUp : Type where
  | mk (U D T E L M W H C P N : BHist) : UniformCompletionUniversalPropertyUp
  deriving DecidableEq

def uniformCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionUniversalPropertyEncodeBHist h

def uniformCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionUniversalPropertyDecodeBHist tail)

private theorem UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionUniversalPropertyFields :
    UniformCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionUniversalPropertyUp.mk U D T E L M W H C P N =>
      [U, D, T, E, L, M, W, H, C, P, N]

def uniformCompletionUniversalPropertyToEventFlow :
    UniformCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (uniformCompletionUniversalPropertyFields x).map
      uniformCompletionUniversalPropertyEncodeBHist

private def uniformCompletionUniversalPropertyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      uniformCompletionUniversalPropertyEventAtDefault index rest

def uniformCompletionUniversalPropertyFromEventFlow
    (ef : EventFlow) : Option UniformCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCompletionUniversalPropertyUp.mk
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 0 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 1 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 2 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 3 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 4 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 5 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 6 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 7 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 8 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 9 ef))
      (uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEventAtDefault 10 ef)))

private theorem UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCompletionUniversalPropertyUp,
      uniformCompletionUniversalPropertyFromEventFlow
        (uniformCompletionUniversalPropertyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk U D T E L M W H C P N =>
      change
        some
          (UniformCompletionUniversalPropertyUp.mk
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist U))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist D))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist T))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist E))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist L))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist M))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist W))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist H))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist C))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist P))
            (uniformCompletionUniversalPropertyDecodeBHist
              (uniformCompletionUniversalPropertyEncodeBHist N))) =
          some (UniformCompletionUniversalPropertyUp.mk U D T E L M W H C P N)
      rw [UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode U,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode D,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode T,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode E,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode L,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode M,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode W,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode H,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode C,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode P,
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode N]

private theorem
    UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCompletionUniversalPropertyUp} :
    uniformCompletionUniversalPropertyToEventFlow x =
      uniformCompletionUniversalPropertyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompletionUniversalPropertyFromEventFlow
          (uniformCompletionUniversalPropertyToEventFlow x) =
        uniformCompletionUniversalPropertyFromEventFlow
          (uniformCompletionUniversalPropertyToEventFlow y) :=
    congrArg uniformCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip
        x).symm
      (Eq.trans hread
        (UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance uniformCompletionUniversalPropertyBHistCarrier :
    BHistCarrier UniformCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionUniversalPropertyToEventFlow
  fromEventFlow := uniformCompletionUniversalPropertyFromEventFlow

instance uniformCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate UniformCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionUniversalPropertyFromEventFlow
        (uniformCompletionUniversalPropertyToEventFlow x) = some x
    exact UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate UniformCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionUniversalPropertyChapterTasteGate

theorem UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      uniformCompletionUniversalPropertyDecodeBHist
        (uniformCompletionUniversalPropertyEncodeBHist h) = h) ∧
      (∀ x : UniformCompletionUniversalPropertyUp,
        uniformCompletionUniversalPropertyFromEventFlow
          (uniformCompletionUniversalPropertyToEventFlow x) = some x) ∧
        (∀ x y : UniformCompletionUniversalPropertyUp,
          uniformCompletionUniversalPropertyToEventFlow x =
            uniformCompletionUniversalPropertyToEventFlow y → x = y) ∧
          uniformCompletionUniversalPropertyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode,
      UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        UniformCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.UniformCompletionUniversalPropertyUp
