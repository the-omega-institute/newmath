import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICNormalizationWindowConfluenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICNormalizationWindowConfluenceUp : Type where
  | mk (T R K Q S A B D E Z H C P N : BHist) : MetaCICNormalizationWindowConfluenceUp
  deriving DecidableEq

def metacicNormalizationWindowConfluenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metacicNormalizationWindowConfluenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metacicNormalizationWindowConfluenceEncodeBHist h

def metacicNormalizationWindowConfluenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metacicNormalizationWindowConfluenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metacicNormalizationWindowConfluenceDecodeBHist tail)

private theorem metacicNormalizationWindowConfluence_decode_encode :
    ∀ h : BHist,
      metacicNormalizationWindowConfluenceDecodeBHist
        (metacicNormalizationWindowConfluenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def metacicNormalizationWindowConfluenceFields :
    MetaCICNormalizationWindowConfluenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICNormalizationWindowConfluenceUp.mk T R K Q S A B D E Z H C P N =>
      [T, R, K, Q, S, A, B, D, E, Z, H, C, P, N]

def metacicNormalizationWindowConfluenceToEventFlow :
    MetaCICNormalizationWindowConfluenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (metacicNormalizationWindowConfluenceFields x).map
        metacicNormalizationWindowConfluenceEncodeBHist

def metacicNormalizationWindowConfluenceFromEventFlow :
    EventFlow → Option MetaCICNormalizationWindowConfluenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | K :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | S :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | B :: rest6 =>
                              match rest6 with
                              | [] => none
                              | D :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | E :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | Z :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | H :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | P :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (MetaCICNormalizationWindowConfluenceUp.mk
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist T)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist R)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist K)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist Q)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist S)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist A)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist B)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist D)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist E)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist Z)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist H)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist C)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist P)
                                                                  (metacicNormalizationWindowConfluenceDecodeBHist N))
                                                          | _ :: _ => none

private theorem metacicNormalizationWindowConfluence_round_trip
    (x : MetaCICNormalizationWindowConfluenceUp) :
    metacicNormalizationWindowConfluenceFromEventFlow
        (metacicNormalizationWindowConfluenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T R K Q S A B D E Z H C P N =>
      change
        some
          (MetaCICNormalizationWindowConfluenceUp.mk
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist T))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist R))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist K))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist Q))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist S))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist A))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist B))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist D))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist E))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist Z))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist H))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist C))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist P))
            (metacicNormalizationWindowConfluenceDecodeBHist
              (metacicNormalizationWindowConfluenceEncodeBHist N))) =
          some (MetaCICNormalizationWindowConfluenceUp.mk T R K Q S A B D E Z H C P N)
      rw [metacicNormalizationWindowConfluence_decode_encode T,
        metacicNormalizationWindowConfluence_decode_encode R,
        metacicNormalizationWindowConfluence_decode_encode K,
        metacicNormalizationWindowConfluence_decode_encode Q,
        metacicNormalizationWindowConfluence_decode_encode S,
        metacicNormalizationWindowConfluence_decode_encode A,
        metacicNormalizationWindowConfluence_decode_encode B,
        metacicNormalizationWindowConfluence_decode_encode D,
        metacicNormalizationWindowConfluence_decode_encode E,
        metacicNormalizationWindowConfluence_decode_encode Z,
        metacicNormalizationWindowConfluence_decode_encode H,
        metacicNormalizationWindowConfluence_decode_encode C,
        metacicNormalizationWindowConfluence_decode_encode P,
        metacicNormalizationWindowConfluence_decode_encode N]

private theorem metacicNormalizationWindowConfluenceToEventFlow_injective
    {x y : MetaCICNormalizationWindowConfluenceUp} :
    metacicNormalizationWindowConfluenceToEventFlow x =
        metacicNormalizationWindowConfluenceToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metacicNormalizationWindowConfluenceFromEventFlow
          (metacicNormalizationWindowConfluenceToEventFlow x) =
        metacicNormalizationWindowConfluenceFromEventFlow
          (metacicNormalizationWindowConfluenceToEventFlow y) :=
    congrArg metacicNormalizationWindowConfluenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metacicNormalizationWindowConfluence_round_trip x).symm
      (Eq.trans hread (metacicNormalizationWindowConfluence_round_trip y)))

private theorem metacicNormalizationWindowConfluenceFields_faithful :
    ∀ x y : MetaCICNormalizationWindowConfluenceUp,
      metacicNormalizationWindowConfluenceFields x =
          metacicNormalizationWindowConfluenceFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T₁ R₁ K₁ Q₁ S₁ A₁ B₁ D₁ E₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk T₂ R₂ K₂ Q₂ S₂ A₂ B₂ D₂ E₂ Z₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance metacicNormalizationWindowConfluenceBHistCarrier :
    BHistCarrier MetaCICNormalizationWindowConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metacicNormalizationWindowConfluenceToEventFlow
  fromEventFlow := metacicNormalizationWindowConfluenceFromEventFlow

instance metacicNormalizationWindowConfluenceChapterTasteGate :
    ChapterTasteGate MetaCICNormalizationWindowConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metacicNormalizationWindowConfluenceFromEventFlow
          (metacicNormalizationWindowConfluenceToEventFlow x) = some x
    exact metacicNormalizationWindowConfluence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metacicNormalizationWindowConfluenceToEventFlow_injective heq)

instance metacicNormalizationWindowConfluenceFieldFaithful :
    FieldFaithful MetaCICNormalizationWindowConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metacicNormalizationWindowConfluenceFields
  field_faithful := metacicNormalizationWindowConfluenceFields_faithful

instance metacicNormalizationWindowConfluenceNontrivial :
    Nontrivial MetaCICNormalizationWindowConfluenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICNormalizationWindowConfluenceUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICNormalizationWindowConfluenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICNormalizationWindowConfluenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metacicNormalizationWindowConfluenceChapterTasteGate

theorem MetaCICNormalizationWindowConfluenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metacicNormalizationWindowConfluenceDecodeBHist
        (metacicNormalizationWindowConfluenceEncodeBHist h) = h) ∧
      (∀ x : MetaCICNormalizationWindowConfluenceUp,
        metacicNormalizationWindowConfluenceFromEventFlow
            (metacicNormalizationWindowConfluenceToEventFlow x) = some x) ∧
        (∀ x y : MetaCICNormalizationWindowConfluenceUp,
          metacicNormalizationWindowConfluenceToEventFlow x =
              metacicNormalizationWindowConfluenceToEventFlow y →
            x = y) ∧
          metacicNormalizationWindowConfluenceEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨metacicNormalizationWindowConfluence_decode_encode,
      metacicNormalizationWindowConfluence_round_trip,
      (fun x y heq => metacicNormalizationWindowConfluenceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MetaCICNormalizationWindowConfluenceUp
