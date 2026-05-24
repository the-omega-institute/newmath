import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicEmbeddingUniquenessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicEmbeddingUniquenessUp : Type where
  | mk (D S Q R E H C P N : BHist) : DyadicEmbeddingUniquenessUp
  deriving DecidableEq

def dyadicEmbeddingUniquenessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicEmbeddingUniquenessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicEmbeddingUniquenessEncodeBHist h

def dyadicEmbeddingUniquenessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicEmbeddingUniquenessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicEmbeddingUniquenessDecodeBHist tail)

private theorem DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicEmbeddingUniquenessDecodeBHist
        (dyadicEmbeddingUniquenessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicEmbeddingUniquenessToEventFlow : DyadicEmbeddingUniquenessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicEmbeddingUniquenessUp.mk D S Q R E H C P N =>
      [[BMark.b0, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist D,
        [BMark.b0, BMark.b1],
        dyadicEmbeddingUniquenessEncodeBHist S,
        [BMark.b1, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicEmbeddingUniquenessEncodeBHist N]

def dyadicEmbeddingUniquenessFromEventFlow :
    EventFlow → Option DyadicEmbeddingUniquenessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagD :: restD =>
      match restD with
      | [] => none
      | D :: restS =>
          match restS with
          | [] => none
          | _tagS :: restSRow =>
              match restSRow with
              | [] => none
              | S :: restQ =>
                  match restQ with
                  | [] => none
                  | _tagQ :: restQRow =>
                      match restQRow with
                      | [] => none
                      | Q :: restR =>
                          match restR with
                          | [] => none
                          | _tagR :: restRRow =>
                              match restRRow with
                              | [] => none
                              | R :: restE =>
                                  match restE with
                                  | [] => none
                                  | _tagE :: restERow =>
                                      match restERow with
                                      | [] => none
                                      | E :: restH =>
                                          match restH with
                                          | [] => none
                                          | _tagH :: restHRow =>
                                              match restHRow with
                                              | [] => none
                                              | H :: restC =>
                                                  match restC with
                                                  | [] => none
                                                  | _tagC :: restCRow =>
                                                      match restCRow with
                                                      | [] => none
                                                      | C :: restP =>
                                                          match restP with
                                                          | [] => none
                                                          | _tagP :: restPRow =>
                                                              match restPRow with
                                                              | [] => none
                                                              | P :: restN =>
                                                                  match restN with
                                                                  | [] => none
                                                                  | _tagN :: restNRow =>
                                                                      match restNRow with
                                                                      | [] => none
                                                                      | N :: rest =>
                                                                          match rest with
                                                                          | [] =>
                                                                              some
                                                                                (DyadicEmbeddingUniquenessUp.mk
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist D)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist S)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist Q)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist R)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist E)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist H)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist C)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist P)
                                                                                  (dyadicEmbeddingUniquenessDecodeBHist N))
                                                                          | _ :: _ => none

private theorem DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicEmbeddingUniquenessUp,
      dyadicEmbeddingUniquenessFromEventFlow
        (dyadicEmbeddingUniquenessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S Q R E H C P N =>
      change
        some
          (DyadicEmbeddingUniquenessUp.mk
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist D))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist S))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist Q))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist R))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist E))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist H))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist C))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist P))
            (dyadicEmbeddingUniquenessDecodeBHist
              (dyadicEmbeddingUniquenessEncodeBHist N))) =
          some (DyadicEmbeddingUniquenessUp.mk D S Q R E H C P N)
      rw [DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode D,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode S,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode R,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode E,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode H,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode C,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode P,
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicEmbeddingUniquenessUp} :
    dyadicEmbeddingUniquenessToEventFlow x =
      dyadicEmbeddingUniquenessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicEmbeddingUniquenessFromEventFlow
          (dyadicEmbeddingUniquenessToEventFlow x) =
        dyadicEmbeddingUniquenessFromEventFlow
          (dyadicEmbeddingUniquenessToEventFlow y) :=
    congrArg dyadicEmbeddingUniquenessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicEmbeddingUniquenessBHistCarrier :
    BHistCarrier DyadicEmbeddingUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicEmbeddingUniquenessToEventFlow
  fromEventFlow := dyadicEmbeddingUniquenessFromEventFlow

instance dyadicEmbeddingUniquenessChapterTasteGate :
    ChapterTasteGate DyadicEmbeddingUniquenessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicEmbeddingUniquenessFromEventFlow
        (dyadicEmbeddingUniquenessToEventFlow x) = some x
    exact DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicEmbeddingUniquenessDecodeBHist
      (dyadicEmbeddingUniquenessEncodeBHist h) = h) ∧
      (∀ x : DyadicEmbeddingUniquenessUp,
        dyadicEmbeddingUniquenessFromEventFlow
          (dyadicEmbeddingUniquenessToEventFlow x) = some x) ∧
        (∀ x y : DyadicEmbeddingUniquenessUp,
          dyadicEmbeddingUniquenessToEventFlow x =
            dyadicEmbeddingUniquenessToEventFlow y → x = y) ∧
          dyadicEmbeddingUniquenessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_decode_encode,
      DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        DyadicEmbeddingUniquenessTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.DyadicEmbeddingUniquenessUp
