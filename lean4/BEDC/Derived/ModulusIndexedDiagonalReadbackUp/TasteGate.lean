import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusIndexedDiagonalReadbackUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusIndexedDiagonalReadbackUp : Type where
  | mk (M S R Q E H C P N : BHist) : ModulusIndexedDiagonalReadbackUp
  deriving DecidableEq

def modulusIndexedDiagonalReadbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusIndexedDiagonalReadbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusIndexedDiagonalReadbackEncodeBHist h

def modulusIndexedDiagonalReadbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusIndexedDiagonalReadbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusIndexedDiagonalReadbackDecodeBHist tail)

private theorem ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      modulusIndexedDiagonalReadbackDecodeBHist
        (modulusIndexedDiagonalReadbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusIndexedDiagonalReadbackToEventFlow :
    ModulusIndexedDiagonalReadbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusIndexedDiagonalReadbackUp.mk M S R Q E H C P N =>
      [[BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist M,
        [BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        modulusIndexedDiagonalReadbackEncodeBHist N]

def modulusIndexedDiagonalReadbackFromEventFlow :
    EventFlow → Option ModulusIndexedDiagonalReadbackUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagM :: restM =>
      match restM with
      | [] => none
      | M :: restSTag =>
          match restSTag with
          | [] => none
          | _tagS :: restS =>
              match restS with
              | [] => none
              | S :: restRTag =>
                  match restRTag with
                  | [] => none
                  | _tagR :: restR =>
                      match restR with
                      | [] => none
                      | R :: restQTag =>
                          match restQTag with
                          | [] => none
                          | _tagQ :: restQ =>
                              match restQ with
                              | [] => none
                              | Q :: restETag =>
                                  match restETag with
                                  | [] => none
                                  | _tagE :: restE =>
                                      match restE with
                                      | [] => none
                                      | E :: restHTag =>
                                          match restHTag with
                                          | [] => none
                                          | _tagH :: restH =>
                                              match restH with
                                              | [] => none
                                              | H :: restCTag =>
                                                  match restCTag with
                                                  | [] => none
                                                  | _tagC :: restC =>
                                                      match restC with
                                                      | [] => none
                                                      | C :: restPTag =>
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
                                                                                (ModulusIndexedDiagonalReadbackUp.mk
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist M)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist S)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist R)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist Q)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist E)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist H)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist C)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist P)
                                                                                  (modulusIndexedDiagonalReadbackDecodeBHist N))
                                                                          | _ :: _ => none

private theorem ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ModulusIndexedDiagonalReadbackUp,
      modulusIndexedDiagonalReadbackFromEventFlow
        (modulusIndexedDiagonalReadbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M S R Q E H C P N =>
      change
        some
          (ModulusIndexedDiagonalReadbackUp.mk
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist M))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist S))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist R))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist Q))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist E))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist H))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist C))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist P))
            (modulusIndexedDiagonalReadbackDecodeBHist
              (modulusIndexedDiagonalReadbackEncodeBHist N))) =
          some (ModulusIndexedDiagonalReadbackUp.mk M S R Q E H C P N)
      rw [ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode M,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode S,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode R,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode Q,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode E,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode H,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode C,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode P,
        ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode N]

private theorem ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_injective
    {x y : ModulusIndexedDiagonalReadbackUp} :
    modulusIndexedDiagonalReadbackToEventFlow x =
      modulusIndexedDiagonalReadbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusIndexedDiagonalReadbackFromEventFlow
          (modulusIndexedDiagonalReadbackToEventFlow x) =
        modulusIndexedDiagonalReadbackFromEventFlow
          (modulusIndexedDiagonalReadbackToEventFlow y) :=
    congrArg modulusIndexedDiagonalReadbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_round_trip y)))

private def modulusIndexedDiagonalReadbackFields :
    ModulusIndexedDiagonalReadbackUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusIndexedDiagonalReadbackUp.mk M S R Q E H C P N => [M, S, R, Q, E, H, C, P, N]

private theorem ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_fields :
    ∀ x y : ModulusIndexedDiagonalReadbackUp,
      modulusIndexedDiagonalReadbackFields x = modulusIndexedDiagonalReadbackFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M1 S1 R1 Q1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk M2 S2 R2 Q2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance modulusIndexedDiagonalReadbackBHistCarrier :
    BHistCarrier ModulusIndexedDiagonalReadbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusIndexedDiagonalReadbackToEventFlow
  fromEventFlow := modulusIndexedDiagonalReadbackFromEventFlow

instance modulusIndexedDiagonalReadbackChapterTasteGate :
    ChapterTasteGate ModulusIndexedDiagonalReadbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusIndexedDiagonalReadbackFromEventFlow
        (modulusIndexedDiagonalReadbackToEventFlow x) = some x
    exact ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_injective heq)

instance modulusIndexedDiagonalReadbackFieldFaithful :
    FieldFaithful ModulusIndexedDiagonalReadbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modulusIndexedDiagonalReadbackFields
  field_faithful := ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_fields

instance modulusIndexedDiagonalReadbackNontrivial :
    Nontrivial ModulusIndexedDiagonalReadbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModulusIndexedDiagonalReadbackUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ModulusIndexedDiagonalReadbackUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment :
    (forall h : BHist,
      modulusIndexedDiagonalReadbackDecodeBHist
        (modulusIndexedDiagonalReadbackEncodeBHist h) = h) /\
      (forall x : ModulusIndexedDiagonalReadbackUp,
        modulusIndexedDiagonalReadbackFromEventFlow
          (modulusIndexedDiagonalReadbackToEventFlow x) = some x) /\
        (forall x y : ModulusIndexedDiagonalReadbackUp,
          modulusIndexedDiagonalReadbackToEventFlow x =
            modulusIndexedDiagonalReadbackToEventFlow y -> x = y) /\
          modulusIndexedDiagonalReadbackEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_decode
  constructor
  · exact ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact ModulusIndexedDiagonalReadbackTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.ModulusIndexedDiagonalReadbackUp
