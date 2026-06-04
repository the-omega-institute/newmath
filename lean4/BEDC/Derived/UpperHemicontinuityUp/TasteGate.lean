import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpperHemicontinuityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpperHemicontinuityUp : Type where
  | mk
      (source codomain graph compactValue readback dependency optimization transport replay
        provenance name : BHist) : UpperHemicontinuityUp
  deriving DecidableEq

def upperHemicontinuityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upperHemicontinuityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upperHemicontinuityEncodeBHist h

def upperHemicontinuityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upperHemicontinuityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upperHemicontinuityDecodeBHist tail)

private theorem upperHemicontinuityDecode_encode_bhist :
    ∀ h : BHist, upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def upperHemicontinuityToEventFlow : UpperHemicontinuityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | UpperHemicontinuityUp.mk source codomain graph compactValue readback dependency
      optimization transport replay provenance name =>
      [[BMark.b0],
        upperHemicontinuityEncodeBHist source,
        [BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist codomain,
        [BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist graph,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist compactValue,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist dependency,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist optimization,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        upperHemicontinuityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        upperHemicontinuityEncodeBHist name]

private def upperHemicontinuityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => upperHemicontinuityEventAtDefault index rest

def upperHemicontinuityFromEventFlow (ef : EventFlow) : Option UpperHemicontinuityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UpperHemicontinuityUp.mk
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 1 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 3 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 5 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 7 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 9 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 11 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 13 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 15 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 17 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 19 ef))
      (upperHemicontinuityDecodeBHist (upperHemicontinuityEventAtDefault 21 ef)))

private theorem upperHemicontinuity_round_trip :
    ∀ x : UpperHemicontinuityUp,
      upperHemicontinuityFromEventFlow (upperHemicontinuityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source codomain graph compactValue readback dependency optimization transport replay
      provenance name =>
      change
        some
          (UpperHemicontinuityUp.mk
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist source))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist codomain))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist graph))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist compactValue))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist readback))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist dependency))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist optimization))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist transport))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist replay))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist provenance))
            (upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist name))) =
          some
            (UpperHemicontinuityUp.mk source codomain graph compactValue readback dependency
              optimization transport replay provenance name)
      rw [upperHemicontinuityDecode_encode_bhist source,
        upperHemicontinuityDecode_encode_bhist codomain,
        upperHemicontinuityDecode_encode_bhist graph,
        upperHemicontinuityDecode_encode_bhist compactValue,
        upperHemicontinuityDecode_encode_bhist readback,
        upperHemicontinuityDecode_encode_bhist dependency,
        upperHemicontinuityDecode_encode_bhist optimization,
        upperHemicontinuityDecode_encode_bhist transport,
        upperHemicontinuityDecode_encode_bhist replay,
        upperHemicontinuityDecode_encode_bhist provenance,
        upperHemicontinuityDecode_encode_bhist name]

private theorem upperHemicontinuityToEventFlow_injective {x y : UpperHemicontinuityUp} :
    upperHemicontinuityToEventFlow x = upperHemicontinuityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upperHemicontinuityFromEventFlow (upperHemicontinuityToEventFlow x) =
        upperHemicontinuityFromEventFlow (upperHemicontinuityToEventFlow y) :=
    congrArg upperHemicontinuityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (upperHemicontinuity_round_trip x).symm
      (Eq.trans hread (upperHemicontinuity_round_trip y)))

instance upperHemicontinuityBHistCarrier : BHistCarrier UpperHemicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upperHemicontinuityToEventFlow
  fromEventFlow := upperHemicontinuityFromEventFlow

instance upperHemicontinuityChapterTasteGate : ChapterTasteGate UpperHemicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upperHemicontinuityFromEventFlow (upperHemicontinuityToEventFlow x) = some x
    exact upperHemicontinuity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (upperHemicontinuityToEventFlow_injective heq)

instance upperHemicontinuityFieldFaithful : FieldFaithful UpperHemicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | UpperHemicontinuityUp.mk source codomain graph compactValue readback dependency
        optimization transport replay provenance name =>
        [source, codomain, graph, compactValue, readback, dependency, optimization, transport,
          replay, provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk source₁ codomain₁ graph₁ compactValue₁ readback₁ dependency₁ optimization₁
        transport₁ replay₁ provenance₁ name₁ =>
        cases y with
        | mk source₂ codomain₂ graph₂ compactValue₂ readback₂ dependency₂ optimization₂
            transport₂ replay₂ provenance₂ name₂ =>
            injection h with hSource rest₁
            injection rest₁ with hCodomain rest₂
            injection rest₂ with hGraph rest₃
            injection rest₃ with hCompactValue rest₄
            injection rest₄ with hReadback rest₅
            injection rest₅ with hDependency rest₆
            injection rest₆ with hOptimization rest₇
            injection rest₇ with hTransport rest₈
            injection rest₈ with hReplay rest₉
            injection rest₉ with hProvenance rest₁₀
            injection rest₁₀ with hName _
            cases hSource
            cases hCodomain
            cases hGraph
            cases hCompactValue
            cases hReadback
            cases hDependency
            cases hOptimization
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

instance upperHemicontinuityNontrivial : Nontrivial UpperHemicontinuityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpperHemicontinuityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpperHemicontinuityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, by
        intro h
        injection h with hSource _ _ _ _ _ _ _ _ _ _
        cases hSource⟩

theorem UpperHemicontinuityTasteGate_single_carrier_alignment :
    upperHemicontinuityDecodeBHist (upperHemicontinuityEncodeBHist .Empty) = .Empty ∧
      Nonempty (BHistCarrier UpperHemicontinuityUp) ∧
        Nonempty (ChapterTasteGate UpperHemicontinuityUp) ∧
          Nonempty (FieldFaithful UpperHemicontinuityUp) ∧
            Nonempty (Nontrivial UpperHemicontinuityUp) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨rfl, ⟨upperHemicontinuityBHistCarrier⟩, ⟨upperHemicontinuityChapterTasteGate⟩,
      ⟨upperHemicontinuityFieldFaithful⟩, ⟨upperHemicontinuityNontrivial⟩⟩

end BEDC.Derived.UpperHemicontinuityUp
