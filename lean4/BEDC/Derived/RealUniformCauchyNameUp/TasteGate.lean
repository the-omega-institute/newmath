import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealUniformCauchyNameUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealUniformCauchyNameUp : Type where
  | mk (S R M Q D E H C P N : BHist) : RealUniformCauchyNameUp
  deriving DecidableEq

def realUniformCauchyNameEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realUniformCauchyNameEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realUniformCauchyNameEncodeBHist h

def realUniformCauchyNameDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realUniformCauchyNameDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realUniformCauchyNameDecodeBHist tail)

private theorem realUniformCauchyNameDecode_encode :
    ∀ h : BHist, realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realUniformCauchyNameFields : RealUniformCauchyNameUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealUniformCauchyNameUp.mk S R M Q D E H C P N => [S, R, M, Q, D, E, H, C, P, N]

def realUniformCauchyNameToEventFlow : RealUniformCauchyNameUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realUniformCauchyNameFields x).map realUniformCauchyNameEncodeBHist

def realUniformCauchyNameFromEventFlow : EventFlow → Option RealUniformCauchyNameUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: restS =>
      match restS with
      | R :: restR =>
          match restR with
          | M :: restM =>
              match restM with
              | Q :: restQ =>
                  match restQ with
                  | D :: restD =>
                      match restD with
                      | E :: restE =>
                          match restE with
                          | H :: restH =>
                              match restH with
                              | C :: restC =>
                                  match restC with
                                  | P :: restP =>
                                      match restP with
                                      | N :: restN =>
                                          match restN with
                                          | [] =>
                                              some
                                                (RealUniformCauchyNameUp.mk
                                                  (realUniformCauchyNameDecodeBHist S)
                                                  (realUniformCauchyNameDecodeBHist R)
                                                  (realUniformCauchyNameDecodeBHist M)
                                                  (realUniformCauchyNameDecodeBHist Q)
                                                  (realUniformCauchyNameDecodeBHist D)
                                                  (realUniformCauchyNameDecodeBHist E)
                                                  (realUniformCauchyNameDecodeBHist H)
                                                  (realUniformCauchyNameDecodeBHist C)
                                                  (realUniformCauchyNameDecodeBHist P)
                                                  (realUniformCauchyNameDecodeBHist N))
                                          | _ :: _ => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem realUniformCauchyName_round_trip :
    ∀ x : RealUniformCauchyNameUp,
      realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R M Q D E H C P N =>
      change
        some
          (RealUniformCauchyNameUp.mk
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist S))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist R))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist M))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist Q))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist D))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist E))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist H))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist C))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist P))
            (realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist N))) =
          some (RealUniformCauchyNameUp.mk S R M Q D E H C P N)
      rw [realUniformCauchyNameDecode_encode S, realUniformCauchyNameDecode_encode R,
        realUniformCauchyNameDecode_encode M, realUniformCauchyNameDecode_encode Q,
        realUniformCauchyNameDecode_encode D, realUniformCauchyNameDecode_encode E,
        realUniformCauchyNameDecode_encode H, realUniformCauchyNameDecode_encode C,
        realUniformCauchyNameDecode_encode P, realUniformCauchyNameDecode_encode N]

private theorem realUniformCauchyNameToEventFlow_injective
    {x y : RealUniformCauchyNameUp} :
    realUniformCauchyNameToEventFlow x = realUniformCauchyNameToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) =
        realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow y) :=
    congrArg realUniformCauchyNameFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realUniformCauchyName_round_trip x).symm
      (Eq.trans hread (realUniformCauchyName_round_trip y)))

private theorem realUniformCauchyName_field_faithful :
    ∀ x y : RealUniformCauchyNameUp,
      realUniformCauchyNameFields x = realUniformCauchyNameFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ M₁ Q₁ D₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ M₂ Q₂ D₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance realUniformCauchyNameBHistCarrier :
    BHistCarrier RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realUniformCauchyNameToEventFlow
  fromEventFlow := realUniformCauchyNameFromEventFlow

instance realUniformCauchyNameChapterTasteGate :
    ChapterTasteGate RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) = some x
    exact realUniformCauchyName_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realUniformCauchyNameToEventFlow_injective heq)

instance realUniformCauchyNameFieldFaithful :
    FieldFaithful RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realUniformCauchyNameFields
  field_faithful := realUniformCauchyName_field_faithful

instance realUniformCauchyNameNontrivial :
    Nontrivial RealUniformCauchyNameUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealUniformCauchyNameUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealUniformCauchyNameUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealUniformCauchyNameUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realUniformCauchyNameChapterTasteGate

theorem RealUniformCauchyNameTasteGate_single_carrier_alignment :
    (∀ h : BHist, realUniformCauchyNameDecodeBHist (realUniformCauchyNameEncodeBHist h) = h) ∧
      (∀ x : RealUniformCauchyNameUp,
        realUniformCauchyNameFromEventFlow (realUniformCauchyNameToEventFlow x) = some x) ∧
        (∀ x y : RealUniformCauchyNameUp,
          realUniformCauchyNameToEventFlow x = realUniformCauchyNameToEventFlow y → x = y) ∧
          realUniformCauchyNameEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨realUniformCauchyNameDecode_encode, realUniformCauchyName_round_trip,
      (fun _ _ heq => realUniformCauchyNameToEventFlow_injective heq), rfl⟩

end BEDC.Derived.RealUniformCauchyNameUp
