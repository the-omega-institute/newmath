import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PackingNumberUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PackingNumberUp : Type where
  | mk
      (source tolerance centers distance budget transport replay provenance name :
        BHist) : PackingNumberUp
  deriving DecidableEq

def packingNumberEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: packingNumberEncodeBHist h
  | BHist.e1 h => BMark.b1 :: packingNumberEncodeBHist h

def packingNumberDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (packingNumberDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (packingNumberDecodeBHist tail)

private theorem packingNumberDecode_encode_bhist :
    ∀ h : BHist, packingNumberDecodeBHist (packingNumberEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def packingNumberToEventFlow : PackingNumberUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PackingNumberUp.mk source tolerance centers distance budget transport replay provenance name =>
      [[BMark.b0],
        packingNumberEncodeBHist source,
        [BMark.b1, BMark.b0],
        packingNumberEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b0],
        packingNumberEncodeBHist centers,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packingNumberEncodeBHist distance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packingNumberEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packingNumberEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        packingNumberEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        packingNumberEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        packingNumberEncodeBHist name]

private def packingNumberEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => packingNumberEventAtDefault index rest

def packingNumberFromEventFlow (ef : EventFlow) : Option PackingNumberUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PackingNumberUp.mk
      (packingNumberDecodeBHist (packingNumberEventAtDefault 1 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 3 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 5 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 7 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 9 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 11 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 13 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 15 ef))
      (packingNumberDecodeBHist (packingNumberEventAtDefault 17 ef)))

private theorem packingNumber_round_trip :
    ∀ x : PackingNumberUp,
      packingNumberFromEventFlow (packingNumberToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source tolerance centers distance budget transport replay provenance name =>
      change
        some
          (PackingNumberUp.mk
            (packingNumberDecodeBHist (packingNumberEncodeBHist source))
            (packingNumberDecodeBHist (packingNumberEncodeBHist tolerance))
            (packingNumberDecodeBHist (packingNumberEncodeBHist centers))
            (packingNumberDecodeBHist (packingNumberEncodeBHist distance))
            (packingNumberDecodeBHist (packingNumberEncodeBHist budget))
            (packingNumberDecodeBHist (packingNumberEncodeBHist transport))
            (packingNumberDecodeBHist (packingNumberEncodeBHist replay))
            (packingNumberDecodeBHist (packingNumberEncodeBHist provenance))
            (packingNumberDecodeBHist (packingNumberEncodeBHist name))) =
          some
            (PackingNumberUp.mk source tolerance centers distance budget transport replay
              provenance name)
      rw [packingNumberDecode_encode_bhist source,
        packingNumberDecode_encode_bhist tolerance,
        packingNumberDecode_encode_bhist centers,
        packingNumberDecode_encode_bhist distance,
        packingNumberDecode_encode_bhist budget,
        packingNumberDecode_encode_bhist transport,
        packingNumberDecode_encode_bhist replay,
        packingNumberDecode_encode_bhist provenance,
        packingNumberDecode_encode_bhist name]

private theorem packingNumberToEventFlow_injective {x y : PackingNumberUp} :
    packingNumberToEventFlow x = packingNumberToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      packingNumberFromEventFlow (packingNumberToEventFlow x) =
        packingNumberFromEventFlow (packingNumberToEventFlow y) :=
    congrArg packingNumberFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (packingNumber_round_trip x).symm
      (Eq.trans hread (packingNumber_round_trip y)))

instance packingNumberBHistCarrier : BHistCarrier PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := packingNumberToEventFlow
  fromEventFlow := packingNumberFromEventFlow

instance packingNumberChapterTasteGate : ChapterTasteGate PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change packingNumberFromEventFlow (packingNumberToEventFlow x) = some x
    exact packingNumber_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (packingNumberToEventFlow_injective heq)

instance packingNumberFieldFaithful : FieldFaithful PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PackingNumberUp.mk source tolerance centers distance budget transport replay provenance name =>
        [source, tolerance, centers, distance, budget, transport, replay, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk source₁ tolerance₁ centers₁ distance₁ budget₁ transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk source₂ tolerance₂ centers₂ distance₂ budget₂ transport₂ replay₂ provenance₂ name₂ =>
            injection h with hSource rest₁
            injection rest₁ with hTolerance rest₂
            injection rest₂ with hCenters rest₃
            injection rest₃ with hDistance rest₄
            injection rest₄ with hBudget rest₅
            injection rest₅ with hTransport rest₆
            injection rest₆ with hReplay rest₇
            injection rest₇ with hProvenance rest₈
            injection rest₈ with hName _
            cases hSource
            cases hTolerance
            cases hCenters
            cases hDistance
            cases hBudget
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

instance packingNumberNontrivial : Nontrivial PackingNumberUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PackingNumberUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      PackingNumberUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hSource _ _ _ _ _ _ _ _
        cases hSource⟩

theorem PackingNumberTasteGate_single_carrier_alignment :
    (∀ h : BHist, packingNumberDecodeBHist (packingNumberEncodeBHist h) = h) ∧
      (∀ x : PackingNumberUp,
        packingNumberFromEventFlow (packingNumberToEventFlow x) = some x) ∧
        (∀ x y : PackingNumberUp,
          packingNumberToEventFlow x = packingNumberToEventFlow y → x = y) ∧
          packingNumberEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact packingNumberDecode_encode_bhist
  · constructor
    · exact packingNumber_round_trip
    · constructor
      · intro x y heq
        exact packingNumberToEventFlow_injective heq
      · rfl

end BEDC.Derived.PackingNumberUp.TasteGate
