import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopRegularCutEquivalenceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopRegularCutEquivalenceUp : Type where
  | mk (C L R D Q H T P N : BHist) : BishopRegularCutEquivalenceUp
  deriving DecidableEq

def bishopRegularCutEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopRegularCutEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopRegularCutEquivalenceEncodeBHist h

def bishopRegularCutEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopRegularCutEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopRegularCutEquivalenceDecodeBHist tail)

private theorem bishopRegularCutEquivalenceDecode_encode_bhist :
    ∀ h : BHist,
      bishopRegularCutEquivalenceDecodeBHist
        (bishopRegularCutEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopRegularCutEquivalenceFields : BishopRegularCutEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopRegularCutEquivalenceUp.mk C L R D Q H T P N => [C, L, R, D, Q, H, T, P, N]

def bishopRegularCutEquivalenceToEventFlow : BishopRegularCutEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopRegularCutEquivalenceFields x).map bishopRegularCutEquivalenceEncodeBHist

def bishopRegularCutEquivalenceFromEventFlow :
    EventFlow → Option BishopRegularCutEquivalenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | C :: restL =>
      match restL with
      | [] => none
      | L :: restR =>
          match restR with
          | [] => none
          | R :: restD =>
              match restD with
              | [] => none
              | D :: restQ =>
                  match restQ with
                  | [] => none
                  | Q :: restH =>
                      match restH with
                      | [] => none
                      | H :: restT =>
                          match restT with
                          | [] => none
                          | T :: restP =>
                              match restP with
                              | [] => none
                              | P :: restN =>
                                  match restN with
                                  | [] => none
                                  | N :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (BishopRegularCutEquivalenceUp.mk
                                              (bishopRegularCutEquivalenceDecodeBHist C)
                                              (bishopRegularCutEquivalenceDecodeBHist L)
                                              (bishopRegularCutEquivalenceDecodeBHist R)
                                              (bishopRegularCutEquivalenceDecodeBHist D)
                                              (bishopRegularCutEquivalenceDecodeBHist Q)
                                              (bishopRegularCutEquivalenceDecodeBHist H)
                                              (bishopRegularCutEquivalenceDecodeBHist T)
                                              (bishopRegularCutEquivalenceDecodeBHist P)
                                              (bishopRegularCutEquivalenceDecodeBHist N))
                                      | _ :: _ => none

private theorem bishopRegularCutEquivalence_round_trip :
    ∀ x : BishopRegularCutEquivalenceUp,
      bishopRegularCutEquivalenceFromEventFlow
        (bishopRegularCutEquivalenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk C L R D Q H T P N =>
      change
        some
          (BishopRegularCutEquivalenceUp.mk
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist C))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist L))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist R))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist D))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist Q))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist H))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist T))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist P))
            (bishopRegularCutEquivalenceDecodeBHist
              (bishopRegularCutEquivalenceEncodeBHist N))) =
          some (BishopRegularCutEquivalenceUp.mk C L R D Q H T P N)
      rw [bishopRegularCutEquivalenceDecode_encode_bhist C,
        bishopRegularCutEquivalenceDecode_encode_bhist L,
        bishopRegularCutEquivalenceDecode_encode_bhist R,
        bishopRegularCutEquivalenceDecode_encode_bhist D,
        bishopRegularCutEquivalenceDecode_encode_bhist Q,
        bishopRegularCutEquivalenceDecode_encode_bhist H,
        bishopRegularCutEquivalenceDecode_encode_bhist T,
        bishopRegularCutEquivalenceDecode_encode_bhist P,
        bishopRegularCutEquivalenceDecode_encode_bhist N]

private theorem bishopRegularCutEquivalenceToEventFlow_injective
    {x y : BishopRegularCutEquivalenceUp} :
    bishopRegularCutEquivalenceToEventFlow x =
      bishopRegularCutEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopRegularCutEquivalenceFromEventFlow (bishopRegularCutEquivalenceToEventFlow x) =
        bishopRegularCutEquivalenceFromEventFlow (bishopRegularCutEquivalenceToEventFlow y) :=
    congrArg bishopRegularCutEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopRegularCutEquivalence_round_trip x).symm
      (Eq.trans hread (bishopRegularCutEquivalence_round_trip y)))

instance bishopRegularCutEquivalenceBHistCarrier :
    BHistCarrier BishopRegularCutEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopRegularCutEquivalenceToEventFlow
  fromEventFlow := bishopRegularCutEquivalenceFromEventFlow

instance bishopRegularCutEquivalenceChapterTasteGate :
    ChapterTasteGate BishopRegularCutEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopRegularCutEquivalenceFromEventFlow
          (bishopRegularCutEquivalenceToEventFlow x) =
        some x
    exact bishopRegularCutEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopRegularCutEquivalenceToEventFlow_injective heq)

theorem BishopRegularCutEquivalenceCarrier_namecert_obligations :
    Nonempty (ChapterTasteGate BishopRegularCutEquivalenceUp) ∧
      (∀ h : BHist,
        bishopRegularCutEquivalenceDecodeBHist
          (bishopRegularCutEquivalenceEncodeBHist h) = h) ∧
        (∀ x : BishopRegularCutEquivalenceUp,
          bishopRegularCutEquivalenceFromEventFlow
            (bishopRegularCutEquivalenceToEventFlow x) = some x) ∧
          bishopRegularCutEquivalenceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨bishopRegularCutEquivalenceChapterTasteGate⟩
  · constructor
    · exact bishopRegularCutEquivalenceDecode_encode_bhist
    · constructor
      · exact bishopRegularCutEquivalence_round_trip
      · rfl

end BEDC.Derived.BishopRegularCutEquivalenceUp.TasteGate
