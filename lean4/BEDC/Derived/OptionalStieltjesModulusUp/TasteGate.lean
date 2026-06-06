import BEDC.Derived.OptionalStieltjesModulusUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OptionalStieltjesModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def optionalStieltjesModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: optionalStieltjesModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: optionalStieltjesModulusEncodeBHist h

def optionalStieltjesModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (optionalStieltjesModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (optionalStieltjesModulusDecodeBHist tail)

private theorem optionalStieltjesModulusDecode_encode_bhist :
    ∀ h : BHist,
      optionalStieltjesModulusDecodeBHist
          (optionalStieltjesModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def optionalStieltjesModulusFields : OptionalStieltjesModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OptionalStieltjesModulusUp.mk integrand integrator variation partition step modulus
      readback realSeal transport replay provenance localName =>
      [integrand, integrator, variation, partition, step, modulus, readback, realSeal,
        transport, replay, provenance, localName]

def optionalStieltjesModulusToEventFlow :
    OptionalStieltjesModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (optionalStieltjesModulusFields x).map optionalStieltjesModulusEncodeBHist

private def optionalStieltjesModulusEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      optionalStieltjesModulusEventAtDefault index rest

def optionalStieltjesModulusFromEventFlow
    (ef : EventFlow) : Option OptionalStieltjesModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (OptionalStieltjesModulusUp.mk
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 0 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 1 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 2 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 3 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 4 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 5 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 6 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 7 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 8 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 9 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 10 ef))
      (optionalStieltjesModulusDecodeBHist
        (optionalStieltjesModulusEventAtDefault 11 ef)))

private theorem optionalStieltjesModulus_round_trip
    (x : OptionalStieltjesModulusUp) :
    optionalStieltjesModulusFromEventFlow
        (optionalStieltjesModulusToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk integrand integrator variation partition step modulus readback realSeal transport replay
      provenance localName =>
      change
        some
          (OptionalStieltjesModulusUp.mk
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist integrand))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist integrator))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist variation))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist partition))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist step))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist modulus))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist readback))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist realSeal))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist transport))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist replay))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist provenance))
            (optionalStieltjesModulusDecodeBHist
              (optionalStieltjesModulusEncodeBHist localName))) =
          some
            (OptionalStieltjesModulusUp.mk integrand integrator variation partition step
              modulus readback realSeal transport replay provenance localName)
      rw [optionalStieltjesModulusDecode_encode_bhist integrand,
        optionalStieltjesModulusDecode_encode_bhist integrator,
        optionalStieltjesModulusDecode_encode_bhist variation,
        optionalStieltjesModulusDecode_encode_bhist partition,
        optionalStieltjesModulusDecode_encode_bhist step,
        optionalStieltjesModulusDecode_encode_bhist modulus,
        optionalStieltjesModulusDecode_encode_bhist readback,
        optionalStieltjesModulusDecode_encode_bhist realSeal,
        optionalStieltjesModulusDecode_encode_bhist transport,
        optionalStieltjesModulusDecode_encode_bhist replay,
        optionalStieltjesModulusDecode_encode_bhist provenance,
        optionalStieltjesModulusDecode_encode_bhist localName]

private theorem optionalStieltjesModulusToEventFlow_injective
    {x y : OptionalStieltjesModulusUp} :
    optionalStieltjesModulusToEventFlow x =
        optionalStieltjesModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      optionalStieltjesModulusFromEventFlow
          (optionalStieltjesModulusToEventFlow x) =
        optionalStieltjesModulusFromEventFlow
          (optionalStieltjesModulusToEventFlow y) :=
    congrArg optionalStieltjesModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (optionalStieltjesModulus_round_trip x).symm
      (Eq.trans hread (optionalStieltjesModulus_round_trip y)))

instance optionalStieltjesModulusBHistCarrier :
    BHistCarrier OptionalStieltjesModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := optionalStieltjesModulusToEventFlow
  fromEventFlow := optionalStieltjesModulusFromEventFlow

instance optionalStieltjesModulusChapterTasteGate :
    ChapterTasteGate OptionalStieltjesModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      optionalStieltjesModulusFromEventFlow
          (optionalStieltjesModulusToEventFlow x) =
        some x
    exact optionalStieltjesModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (optionalStieltjesModulusToEventFlow_injective heq)

instance optionalStieltjesModulusFieldFaithful :
    FieldFaithful OptionalStieltjesModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := optionalStieltjesModulusFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk integrand₁ integrator₁ variation₁ partition₁ step₁ modulus₁ readback₁ realSeal₁
        transport₁ replay₁ provenance₁ localName₁ =>
        cases y with
        | mk integrand₂ integrator₂ variation₂ partition₂ step₂ modulus₂ readback₂ realSeal₂
            transport₂ replay₂ provenance₂ localName₂ =>
            injection h with hIntegrand rest₁
            injection rest₁ with hIntegrator rest₂
            injection rest₂ with hVariation rest₃
            injection rest₃ with hPartition rest₄
            injection rest₄ with hStep rest₅
            injection rest₅ with hModulus rest₆
            injection rest₆ with hReadback rest₇
            injection rest₇ with hRealSeal rest₈
            injection rest₈ with hTransport rest₉
            injection rest₉ with hReplay rest₁₀
            injection rest₁₀ with hProvenance rest₁₁
            injection rest₁₁ with hLocalName _
            cases hIntegrand
            cases hIntegrator
            cases hVariation
            cases hPartition
            cases hStep
            cases hModulus
            cases hReadback
            cases hRealSeal
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

def taste_gate : ChapterTasteGate OptionalStieltjesModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  optionalStieltjesModulusChapterTasteGate

theorem OptionalStieltjesModulusTasteGate_single_carrier_alignment :
    (forall x : OptionalStieltjesModulusUp,
      optionalStieltjesModulusFromEventFlow
          (optionalStieltjesModulusToEventFlow x) =
        some x) ∧
      (forall x y : OptionalStieltjesModulusUp,
        optionalStieltjesModulusToEventFlow x =
            optionalStieltjesModulusToEventFlow y ->
          x = y) ∧
        optionalStieltjesModulusFields
            (OptionalStieltjesModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact optionalStieltjesModulus_round_trip
  · constructor
    · intro x y heq
      exact optionalStieltjesModulusToEventFlow_injective heq
    · rfl

end BEDC.Derived.OptionalStieltjesModulusUp
