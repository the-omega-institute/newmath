import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteNetMinimumFoldUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteNetMinimumFoldUp : Type where
  | mk :
      (bundle radius accumulator lower transport continuation provenance localName : BHist) →
        FiniteNetMinimumFoldUp
  deriving DecidableEq

def finiteNetMinimumFoldEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteNetMinimumFoldEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteNetMinimumFoldEncodeBHist h

def finiteNetMinimumFoldDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteNetMinimumFoldDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteNetMinimumFoldDecodeBHist tail)

private theorem finiteNetMinimumFoldDecodeEncodeBHist :
    ∀ h : BHist, finiteNetMinimumFoldDecodeBHist
      (finiteNetMinimumFoldEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteNetMinimumFoldFields : FiniteNetMinimumFoldUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteNetMinimumFoldUp.mk bundle radius accumulator lower transport continuation
      provenance localName =>
      [bundle, radius, accumulator, lower, transport, continuation, provenance, localName]

def finiteNetMinimumFoldToEventFlow : FiniteNetMinimumFoldUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteNetMinimumFoldFields x).map finiteNetMinimumFoldEncodeBHist

def finiteNetMinimumFoldFromEventFlow : EventFlow → Option FiniteNetMinimumFoldUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | bundle :: rest0 =>
      match rest0 with
      | [] => none
      | radius :: rest1 =>
          match rest1 with
          | [] => none
          | accumulator :: rest2 =>
              match rest2 with
              | [] => none
              | lower :: rest3 =>
                  match rest3 with
                  | [] => none
                  | transport :: rest4 =>
                      match rest4 with
                      | [] => none
                      | continuation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | provenance :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localName :: rest7 =>
                                  match rest7 with
                                  | [] =>
                                      some
                                        (FiniteNetMinimumFoldUp.mk
                                          (finiteNetMinimumFoldDecodeBHist bundle)
                                          (finiteNetMinimumFoldDecodeBHist radius)
                                          (finiteNetMinimumFoldDecodeBHist accumulator)
                                          (finiteNetMinimumFoldDecodeBHist lower)
                                          (finiteNetMinimumFoldDecodeBHist transport)
                                          (finiteNetMinimumFoldDecodeBHist continuation)
                                          (finiteNetMinimumFoldDecodeBHist provenance)
                                          (finiteNetMinimumFoldDecodeBHist localName))
                                  | _ :: _ => none

private theorem finiteNetMinimumFold_round_trip :
    ∀ x : FiniteNetMinimumFoldUp,
      finiteNetMinimumFoldFromEventFlow (finiteNetMinimumFoldToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bundle radius accumulator lower transport continuation provenance localName =>
      change
        some
          (FiniteNetMinimumFoldUp.mk
            (finiteNetMinimumFoldDecodeBHist (finiteNetMinimumFoldEncodeBHist bundle))
            (finiteNetMinimumFoldDecodeBHist (finiteNetMinimumFoldEncodeBHist radius))
            (finiteNetMinimumFoldDecodeBHist
              (finiteNetMinimumFoldEncodeBHist accumulator))
            (finiteNetMinimumFoldDecodeBHist (finiteNetMinimumFoldEncodeBHist lower))
            (finiteNetMinimumFoldDecodeBHist (finiteNetMinimumFoldEncodeBHist transport))
            (finiteNetMinimumFoldDecodeBHist
              (finiteNetMinimumFoldEncodeBHist continuation))
            (finiteNetMinimumFoldDecodeBHist
              (finiteNetMinimumFoldEncodeBHist provenance))
            (finiteNetMinimumFoldDecodeBHist
              (finiteNetMinimumFoldEncodeBHist localName))) =
          some
            (FiniteNetMinimumFoldUp.mk bundle radius accumulator lower transport
              continuation provenance localName)
      rw [finiteNetMinimumFoldDecodeEncodeBHist bundle,
        finiteNetMinimumFoldDecodeEncodeBHist radius,
        finiteNetMinimumFoldDecodeEncodeBHist accumulator,
        finiteNetMinimumFoldDecodeEncodeBHist lower,
        finiteNetMinimumFoldDecodeEncodeBHist transport,
        finiteNetMinimumFoldDecodeEncodeBHist continuation,
        finiteNetMinimumFoldDecodeEncodeBHist provenance,
        finiteNetMinimumFoldDecodeEncodeBHist localName]

private theorem finiteNetMinimumFoldToEventFlow_injective {x y : FiniteNetMinimumFoldUp} :
    finiteNetMinimumFoldToEventFlow x = finiteNetMinimumFoldToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteNetMinimumFoldFromEventFlow (finiteNetMinimumFoldToEventFlow x) =
        finiteNetMinimumFoldFromEventFlow (finiteNetMinimumFoldToEventFlow y) :=
    congrArg finiteNetMinimumFoldFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteNetMinimumFold_round_trip x).symm
      (Eq.trans hread (finiteNetMinimumFold_round_trip y)))

private theorem finiteNetMinimumFoldFieldsFaithful :
    ∀ x y : FiniteNetMinimumFoldUp,
      finiteNetMinimumFoldFields x = finiteNetMinimumFoldFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk bundle₁ radius₁ accumulator₁ lower₁ transport₁ continuation₁ provenance₁
      localName₁ =>
      cases y with
      | mk bundle₂ radius₂ accumulator₂ lower₂ transport₂ continuation₂ provenance₂
          localName₂ =>
          cases hfields
          rfl

instance finiteNetMinimumFoldBHistCarrier :
    BHistCarrier FiniteNetMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteNetMinimumFoldToEventFlow
  fromEventFlow := finiteNetMinimumFoldFromEventFlow

instance finiteNetMinimumFoldChapterTasteGate :
    ChapterTasteGate FiniteNetMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteNetMinimumFoldFromEventFlow (finiteNetMinimumFoldToEventFlow x) = some x
    exact finiteNetMinimumFold_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteNetMinimumFoldToEventFlow_injective heq)

instance finiteNetMinimumFoldFieldFaithful :
    FieldFaithful FiniteNetMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteNetMinimumFoldFields
  field_faithful := finiteNetMinimumFoldFieldsFaithful

instance finiteNetMinimumFoldNontrivial : Nontrivial FiniteNetMinimumFoldUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteNetMinimumFoldUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      FiniteNetMinimumFoldUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteNetMinimumFoldUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteNetMinimumFoldChapterTasteGate

theorem FiniteNetMinimumFoldTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteNetMinimumFoldDecodeBHist (finiteNetMinimumFoldEncodeBHist h) = h) ∧
      (∀ x : FiniteNetMinimumFoldUp,
        finiteNetMinimumFoldFromEventFlow (finiteNetMinimumFoldToEventFlow x) = some x) ∧
      (∀ x y : FiniteNetMinimumFoldUp,
        finiteNetMinimumFoldToEventFlow x = finiteNetMinimumFoldToEventFlow y → x = y) ∧
      (∀ x y : FiniteNetMinimumFoldUp,
        finiteNetMinimumFoldFields x = finiteNetMinimumFoldFields y → x = y) ∧
      finiteNetMinimumFoldEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨finiteNetMinimumFoldDecodeEncodeBHist,
      finiteNetMinimumFold_round_trip,
      (fun _ _ heq => finiteNetMinimumFoldToEventFlow_injective heq),
      finiteNetMinimumFoldFieldsFaithful,
      rfl⟩

end BEDC.Derived.FiniteNetMinimumFoldUp.TasteGate
