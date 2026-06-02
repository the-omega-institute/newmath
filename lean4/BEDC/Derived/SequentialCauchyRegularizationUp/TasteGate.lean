import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SequentialCauchyRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SequentialCauchyRegularizationUp : Type where
  | mk (X T W R D E H C P N : BHist) : SequentialCauchyRegularizationUp
  deriving DecidableEq

def sequentialCauchyRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sequentialCauchyRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sequentialCauchyRegularizationEncodeBHist h

def sequentialCauchyRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sequentialCauchyRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sequentialCauchyRegularizationDecodeBHist tail)

private theorem sequentialCauchyRegularizationDecode_encode_bhist :
    ∀ h : BHist,
      sequentialCauchyRegularizationDecodeBHist
        (sequentialCauchyRegularizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sequentialCauchyRegularizationToEventFlow :
    SequentialCauchyRegularizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SequentialCauchyRegularizationUp.mk X T W R D E H C P N =>
      [sequentialCauchyRegularizationEncodeBHist X,
        sequentialCauchyRegularizationEncodeBHist T,
        sequentialCauchyRegularizationEncodeBHist W,
        sequentialCauchyRegularizationEncodeBHist R,
        sequentialCauchyRegularizationEncodeBHist D,
        sequentialCauchyRegularizationEncodeBHist E,
        sequentialCauchyRegularizationEncodeBHist H,
        sequentialCauchyRegularizationEncodeBHist C,
        sequentialCauchyRegularizationEncodeBHist P,
        sequentialCauchyRegularizationEncodeBHist N]

def sequentialCauchyRegularizationFromEventFlow :
    EventFlow → Option SequentialCauchyRegularizationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | W :: rest2 =>
              match rest2 with
              | [] => none
              | R :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
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
                                                (SequentialCauchyRegularizationUp.mk
                                                  (sequentialCauchyRegularizationDecodeBHist X)
                                                  (sequentialCauchyRegularizationDecodeBHist T)
                                                  (sequentialCauchyRegularizationDecodeBHist W)
                                                  (sequentialCauchyRegularizationDecodeBHist R)
                                                  (sequentialCauchyRegularizationDecodeBHist D)
                                                  (sequentialCauchyRegularizationDecodeBHist E)
                                                  (sequentialCauchyRegularizationDecodeBHist H)
                                                  (sequentialCauchyRegularizationDecodeBHist C)
                                                  (sequentialCauchyRegularizationDecodeBHist P)
                                                  (sequentialCauchyRegularizationDecodeBHist N))
                                          | _ :: _ => none

private theorem sequentialCauchyRegularization_round_trip :
    ∀ x : SequentialCauchyRegularizationUp,
      sequentialCauchyRegularizationFromEventFlow
        (sequentialCauchyRegularizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X T W R D E H C P N =>
      change
        some
          (SequentialCauchyRegularizationUp.mk
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist X))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist T))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist W))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist R))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist D))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist E))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist H))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist C))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist P))
            (sequentialCauchyRegularizationDecodeBHist
              (sequentialCauchyRegularizationEncodeBHist N))) =
          some (SequentialCauchyRegularizationUp.mk X T W R D E H C P N)
      rw [sequentialCauchyRegularizationDecode_encode_bhist X,
        sequentialCauchyRegularizationDecode_encode_bhist T,
        sequentialCauchyRegularizationDecode_encode_bhist W,
        sequentialCauchyRegularizationDecode_encode_bhist R,
        sequentialCauchyRegularizationDecode_encode_bhist D,
        sequentialCauchyRegularizationDecode_encode_bhist E,
        sequentialCauchyRegularizationDecode_encode_bhist H,
        sequentialCauchyRegularizationDecode_encode_bhist C,
        sequentialCauchyRegularizationDecode_encode_bhist P,
        sequentialCauchyRegularizationDecode_encode_bhist N]

private theorem sequentialCauchyRegularizationToEventFlow_injective
    {x y : SequentialCauchyRegularizationUp} :
    sequentialCauchyRegularizationToEventFlow x =
      sequentialCauchyRegularizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sequentialCauchyRegularizationFromEventFlow
          (sequentialCauchyRegularizationToEventFlow x) =
        sequentialCauchyRegularizationFromEventFlow
          (sequentialCauchyRegularizationToEventFlow y) :=
    congrArg sequentialCauchyRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sequentialCauchyRegularization_round_trip x).symm
      (Eq.trans hread (sequentialCauchyRegularization_round_trip y)))

instance sequentialCauchyRegularizationBHistCarrier :
    BHistCarrier SequentialCauchyRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sequentialCauchyRegularizationToEventFlow
  fromEventFlow := sequentialCauchyRegularizationFromEventFlow

instance sequentialCauchyRegularizationChapterTasteGate :
    ChapterTasteGate SequentialCauchyRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sequentialCauchyRegularizationFromEventFlow
        (sequentialCauchyRegularizationToEventFlow x) = some x
    exact sequentialCauchyRegularization_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sequentialCauchyRegularizationToEventFlow_injective heq)

theorem SequentialCauchyRegularizationTasteGate_single_carrier_alignment :
    Nonempty
      (Σ' (X : Type), Σ' (_carrier : BHistCarrier X), ChapterTasteGate X) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨SequentialCauchyRegularizationUp,
      sequentialCauchyRegularizationBHistCarrier,
      sequentialCauchyRegularizationChapterTasteGate⟩⟩

end BEDC.Derived.SequentialCauchyRegularizationUp
