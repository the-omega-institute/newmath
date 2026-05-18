import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.QuadrantSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive QuadrantSubstrateUp : Type where
  | mk (U K L S C H R P N : BHist) : QuadrantSubstrateUp
  deriving DecidableEq

def quadrantSubstrateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: quadrantSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: quadrantSubstrateEncodeBHist h

def quadrantSubstrateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (quadrantSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (quadrantSubstrateDecodeBHist tail)

private theorem QuadrantSubstrateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def quadrantSubstrateToEventFlow : QuadrantSubstrateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | QuadrantSubstrateUp.mk U K L S C H R P N =>
      [[BMark.b0],
        quadrantSubstrateEncodeBHist U,
        [BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        quadrantSubstrateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        quadrantSubstrateEncodeBHist N]

def quadrantSubstrateFromEventFlow : EventFlow → Option QuadrantSubstrateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagU :: restU =>
      match restU with
      | [] => none
      | U :: restKTag =>
          match restKTag with
          | [] => none
          | _tagK :: restK =>
              match restK with
              | [] => none
              | K :: restLTag =>
                  match restLTag with
                  | [] => none
                  | _tagL :: restL =>
                      match restL with
                      | [] => none
                      | L :: restSTag =>
                          match restSTag with
                          | [] => none
                          | _tagS :: restS =>
                              match restS with
                              | [] => none
                              | S :: restCTag =>
                                  match restCTag with
                                  | [] => none
                                  | _tagC :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restHTag =>
                                          match restHTag with
                                          | [] => none
                                          | _tagH :: restH =>
                                              match restH with
                                              | [] => none
                                              | H :: restRTag =>
                                                  match restRTag with
                                                  | [] => none
                                                  | _tagR :: restR =>
                                                      match restR with
                                                      | [] => none
                                                      | R :: restPTag =>
                                                          match restPTag with
                                                          | [] => none
                                                          | _tagP :: restP =>
                                                              match restP with
                                                              | [] => none
                                                              | P :: restNTag =>
                                                                  match restNTag with
                                                                  | [] => none
                                                                  | _tagN :: restN =>
                                                                      match restN with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (QuadrantSubstrateUp.mk
                                                                                  (quadrantSubstrateDecodeBHist U)
                                                                                  (quadrantSubstrateDecodeBHist K)
                                                                                  (quadrantSubstrateDecodeBHist L)
                                                                                  (quadrantSubstrateDecodeBHist S)
                                                                                  (quadrantSubstrateDecodeBHist C)
                                                                                  (quadrantSubstrateDecodeBHist H)
                                                                                  (quadrantSubstrateDecodeBHist R)
                                                                                  (quadrantSubstrateDecodeBHist P)
                                                                                  (quadrantSubstrateDecodeBHist N))
                                                                          | _ :: _ => none

private theorem QuadrantSubstrateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : QuadrantSubstrateUp,
      quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U K L S C H R P N =>
      change
        some
          (QuadrantSubstrateUp.mk
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist U))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist K))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist L))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist S))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist C))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist H))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist R))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist P))
            (quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist N))) =
          some (QuadrantSubstrateUp.mk U K L S C H R P N)
      rw [QuadrantSubstrateTasteGate_single_carrier_alignment_decode U,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode K,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode L,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode S,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode C,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode H,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode R,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode P,
        QuadrantSubstrateTasteGate_single_carrier_alignment_decode N]

private theorem QuadrantSubstrateTasteGate_single_carrier_alignment_injective
    {x y : QuadrantSubstrateUp} :
    quadrantSubstrateToEventFlow x = quadrantSubstrateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) =
        quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow y) :=
    congrArg quadrantSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (QuadrantSubstrateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (QuadrantSubstrateTasteGate_single_carrier_alignment_round_trip y)))

private def quadrantSubstrateFields : QuadrantSubstrateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | QuadrantSubstrateUp.mk U K L S C H R P N => [U, K, L, S, C, H, R, P, N]

private theorem QuadrantSubstrateTasteGate_single_carrier_alignment_fields :
    ∀ x y : QuadrantSubstrateUp,
      quadrantSubstrateFields x = quadrantSubstrateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk U1 K1 L1 S1 C1 H1 R1 P1 N1 =>
      cases y with
      | mk U2 K2 L2 S2 C2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance quadrantSubstrateBHistCarrier : BHistCarrier QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := quadrantSubstrateToEventFlow
  fromEventFlow := quadrantSubstrateFromEventFlow

instance quadrantSubstrateChapterTasteGate :
    ChapterTasteGate QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) = some x
    exact QuadrantSubstrateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (QuadrantSubstrateTasteGate_single_carrier_alignment_injective heq)

instance quadrantSubstrateFieldFaithful : FieldFaithful QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := quadrantSubstrateFields
  field_faithful := QuadrantSubstrateTasteGate_single_carrier_alignment_fields

instance quadrantSubstrateNontrivial : Nontrivial QuadrantSubstrateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨QuadrantSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      QuadrantSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate QuadrantSubstrateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  quadrantSubstrateChapterTasteGate

theorem QuadrantSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist, quadrantSubstrateDecodeBHist (quadrantSubstrateEncodeBHist h) = h) ∧
      (∀ x : QuadrantSubstrateUp,
        quadrantSubstrateFromEventFlow (quadrantSubstrateToEventFlow x) = some x) ∧
        (∀ x y : QuadrantSubstrateUp,
          quadrantSubstrateToEventFlow x = quadrantSubstrateToEventFlow y → x = y) ∧
          quadrantSubstrateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact QuadrantSubstrateTasteGate_single_carrier_alignment_decode
  constructor
  · exact QuadrantSubstrateTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact QuadrantSubstrateTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.QuadrantSubstrateUp
