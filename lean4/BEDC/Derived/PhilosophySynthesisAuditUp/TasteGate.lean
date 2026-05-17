import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhilosophySynthesisAuditUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhilosophySynthesisAuditUp : Type where
  | mk (R E G A L Q H C P N : BHist) : PhilosophySynthesisAuditUp
  deriving DecidableEq

def philosophySynthesisAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: philosophySynthesisAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: philosophySynthesisAuditEncodeBHist h

def philosophySynthesisAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (philosophySynthesisAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (philosophySynthesisAuditDecodeBHist tail)

private theorem PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      philosophySynthesisAuditDecodeBHist
        (philosophySynthesisAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def philosophySynthesisAuditFields : PhilosophySynthesisAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophySynthesisAuditUp.mk R E G A L Q H C P N => [R, E, G, A, L, Q, H, C, P, N]

def philosophySynthesisAuditToEventFlow : PhilosophySynthesisAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhilosophySynthesisAuditUp.mk R E G A L Q H C P N =>
      [philosophySynthesisAuditEncodeBHist R,
        philosophySynthesisAuditEncodeBHist E,
        philosophySynthesisAuditEncodeBHist G,
        philosophySynthesisAuditEncodeBHist A,
        philosophySynthesisAuditEncodeBHist L,
        philosophySynthesisAuditEncodeBHist Q,
        philosophySynthesisAuditEncodeBHist H,
        philosophySynthesisAuditEncodeBHist C,
        philosophySynthesisAuditEncodeBHist P,
        philosophySynthesisAuditEncodeBHist N]

def philosophySynthesisAuditFromEventFlow : EventFlow → Option PhilosophySynthesisAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | R :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | G :: rest2 =>
              match rest2 with
              | [] => none
              | A :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Q :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | P :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | N :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (PhilosophySynthesisAuditUp.mk
                                                  (philosophySynthesisAuditDecodeBHist R)
                                                  (philosophySynthesisAuditDecodeBHist E)
                                                  (philosophySynthesisAuditDecodeBHist G)
                                                  (philosophySynthesisAuditDecodeBHist A)
                                                  (philosophySynthesisAuditDecodeBHist L)
                                                  (philosophySynthesisAuditDecodeBHist Q)
                                                  (philosophySynthesisAuditDecodeBHist H)
                                                  (philosophySynthesisAuditDecodeBHist C)
                                                  (philosophySynthesisAuditDecodeBHist P)
                                                  (philosophySynthesisAuditDecodeBHist N))
                                          | _ :: _ => none

private theorem PhilosophySynthesisAuditTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PhilosophySynthesisAuditUp,
      philosophySynthesisAuditFromEventFlow
        (philosophySynthesisAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R E G A L Q H C P N =>
      change
        some
          (PhilosophySynthesisAuditUp.mk
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist R))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist E))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist G))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist A))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist L))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist Q))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist H))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist C))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist P))
            (philosophySynthesisAuditDecodeBHist (philosophySynthesisAuditEncodeBHist N))) =
          some (PhilosophySynthesisAuditUp.mk R E G A L Q H C P N)
      rw [PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode R,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode E,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode G,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode A,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode L,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode Q,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode H,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode C,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode P,
        PhilosophySynthesisAuditTasteGate_single_carrier_alignment_decode N]

private theorem PhilosophySynthesisAuditTasteGate_single_carrier_alignment_injective
    {x y : PhilosophySynthesisAuditUp} :
    philosophySynthesisAuditToEventFlow x =
      philosophySynthesisAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      philosophySynthesisAuditFromEventFlow (philosophySynthesisAuditToEventFlow x) =
        philosophySynthesisAuditFromEventFlow (philosophySynthesisAuditToEventFlow y) :=
    congrArg philosophySynthesisAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PhilosophySynthesisAuditTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PhilosophySynthesisAuditTasteGate_single_carrier_alignment_round_trip y)))

private theorem PhilosophySynthesisAuditTasteGate_single_carrier_alignment_fields :
    ∀ x y : PhilosophySynthesisAuditUp,
      philosophySynthesisAuditFields x = philosophySynthesisAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ E₁ G₁ A₁ L₁ Q₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ E₂ G₂ A₂ L₂ Q₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance philosophySynthesisAuditBHistCarrier :
    BHistCarrier PhilosophySynthesisAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := philosophySynthesisAuditToEventFlow
  fromEventFlow := philosophySynthesisAuditFromEventFlow

instance philosophySynthesisAuditChapterTasteGate :
    ChapterTasteGate PhilosophySynthesisAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change philosophySynthesisAuditFromEventFlow (philosophySynthesisAuditToEventFlow x) =
      some x
    exact PhilosophySynthesisAuditTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PhilosophySynthesisAuditTasteGate_single_carrier_alignment_injective heq)

instance philosophySynthesisAuditFieldFaithful :
    FieldFaithful PhilosophySynthesisAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := philosophySynthesisAuditFields
  field_faithful := PhilosophySynthesisAuditTasteGate_single_carrier_alignment_fields

instance philosophySynthesisAuditNontrivial : Nontrivial PhilosophySynthesisAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhilosophySynthesisAuditUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PhilosophySynthesisAuditUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhilosophySynthesisAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  philosophySynthesisAuditChapterTasteGate

theorem PhilosophySynthesisAuditTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier PhilosophySynthesisAuditUp) ∧
      Nonempty (ChapterTasteGate PhilosophySynthesisAuditUp) ∧
        Nonempty (FieldFaithful PhilosophySynthesisAuditUp) ∧
          Nonempty (Nontrivial PhilosophySynthesisAuditUp) ∧
            philosophySynthesisAuditEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨philosophySynthesisAuditBHistCarrier⟩,
      ⟨philosophySynthesisAuditChapterTasteGate⟩,
      ⟨philosophySynthesisAuditFieldFaithful⟩,
      ⟨philosophySynthesisAuditNontrivial⟩,
      rfl⟩

end BEDC.Derived.PhilosophySynthesisAuditUp
