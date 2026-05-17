import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophyGovernanceExportUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophyGovernanceExportUp : Type where
  | mk : (P R L S C X T O H K N : BHist) → PhilosophyGovernanceExportUp
  deriving DecidableEq

def philosophyGovernanceExportEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophyGovernanceExportEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophyGovernanceExportEncodeBHist h

def philosophyGovernanceExportDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophyGovernanceExportDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophyGovernanceExportDecodeBHist tail)

theorem PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def philosophyGovernanceExportFields : PhilosophyGovernanceExportUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyGovernanceExportUp.mk P R L S C X T O H K N =>
      [P, R, L, S, C, X, T, O, H, K, N]

def philosophyGovernanceExportToEventFlow : PhilosophyGovernanceExportUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophyGovernanceExportUp.mk P R L S C X T O H K N =>
      [[BMark.b0],
        philosophyGovernanceExportEncodeBHist P,
        [BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        philosophyGovernanceExportEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        philosophyGovernanceExportEncodeBHist N]

def philosophyGovernanceExportFromEventFlow :
    EventFlow → Option PhilosophyGovernanceExportUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | P :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | L :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | S :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | X :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | T :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | O :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | K :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (PhilosophyGovernanceExportUp.mk
                                                                                                  (philosophyGovernanceExportDecodeBHist P)
                                                                                                  (philosophyGovernanceExportDecodeBHist R)
                                                                                                  (philosophyGovernanceExportDecodeBHist L)
                                                                                                  (philosophyGovernanceExportDecodeBHist S)
                                                                                                  (philosophyGovernanceExportDecodeBHist C)
                                                                                                  (philosophyGovernanceExportDecodeBHist X)
                                                                                                  (philosophyGovernanceExportDecodeBHist T)
                                                                                                  (philosophyGovernanceExportDecodeBHist O)
                                                                                                  (philosophyGovernanceExportDecodeBHist H)
                                                                                                  (philosophyGovernanceExportDecodeBHist K)
                                                                                                  (philosophyGovernanceExportDecodeBHist N))
                                                                                          | _ :: _ => none

theorem PhilosophyGovernanceExportTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PhilosophyGovernanceExportUp,
      philosophyGovernanceExportFromEventFlow
        (philosophyGovernanceExportToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P R L S C X T O H K N =>
      change
        some
          (PhilosophyGovernanceExportUp.mk
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist P))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist R))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist L))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist S))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist C))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist X))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist T))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist O))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist H))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist K))
            (philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist N))) =
          some (PhilosophyGovernanceExportUp.mk P R L S C X T O H K N)
      rw [PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode P,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode R,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode L,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode S,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode C,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode X,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode T,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode O,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode H,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode K,
        PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode N]

theorem PhilosophyGovernanceExportTasteGate_single_carrier_alignment_injective
    {x y : PhilosophyGovernanceExportUp} :
    philosophyGovernanceExportToEventFlow x =
      philosophyGovernanceExportToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophyGovernanceExportFromEventFlow (philosophyGovernanceExportToEventFlow x) =
        philosophyGovernanceExportFromEventFlow (philosophyGovernanceExportToEventFlow y) :=
    congrArg philosophyGovernanceExportFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PhilosophyGovernanceExportTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PhilosophyGovernanceExportTasteGate_single_carrier_alignment_round_trip y)))

private theorem PhilosophyGovernanceExportTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : PhilosophyGovernanceExportUp,
      philosophyGovernanceExportFields x = philosophyGovernanceExportFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P R L S C X T O H K N =>
      cases y with
      | mk P' R' L' S' C' X' T' O' H' K' N' =>
          cases hfields
          rfl

instance philosophyGovernanceExportBHistCarrier :
    BHistCarrier PhilosophyGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophyGovernanceExportToEventFlow
  fromEventFlow := philosophyGovernanceExportFromEventFlow

instance philosophyGovernanceExportChapterTasteGate :
    ChapterTasteGate PhilosophyGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      philosophyGovernanceExportFromEventFlow
        (philosophyGovernanceExportToEventFlow x) = some x
    exact PhilosophyGovernanceExportTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PhilosophyGovernanceExportTasteGate_single_carrier_alignment_injective heq)

instance philosophyGovernanceExportFieldFaithful :
    FieldFaithful PhilosophyGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophyGovernanceExportFields
  field_faithful := PhilosophyGovernanceExportTasteGate_single_carrier_alignment_field_faithful

instance philosophyGovernanceExportNontrivial :
    Nontrivial PhilosophyGovernanceExportUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophyGovernanceExportUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophyGovernanceExportUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        injection h with hP
        cases hP⟩

def taste_gate : ChapterTasteGate PhilosophyGovernanceExportUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophyGovernanceExportChapterTasteGate

theorem PhilosophyGovernanceExportTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      philosophyGovernanceExportDecodeBHist (philosophyGovernanceExportEncodeBHist h) = h) ∧
      (∀ x : PhilosophyGovernanceExportUp,
        philosophyGovernanceExportFromEventFlow
          (philosophyGovernanceExportToEventFlow x) = some x) ∧
        (∀ x y : PhilosophyGovernanceExportUp,
          philosophyGovernanceExportToEventFlow x =
            philosophyGovernanceExportToEventFlow y → x = y) ∧
          philosophyGovernanceExportEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact PhilosophyGovernanceExportTasteGate_single_carrier_alignment_decode
  · constructor
    · exact PhilosophyGovernanceExportTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact PhilosophyGovernanceExportTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.PhilosophyGovernanceExportUp
