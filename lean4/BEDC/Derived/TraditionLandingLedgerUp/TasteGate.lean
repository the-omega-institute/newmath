import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TraditionLandingLedgerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TraditionLandingLedgerUp : Type where
  | mk (S T R D H C P N : BHist) : TraditionLandingLedgerUp
  deriving DecidableEq

def traditionLandingLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: traditionLandingLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: traditionLandingLedgerEncodeBHist h

def traditionLandingLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (traditionLandingLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (traditionLandingLedgerDecodeBHist tail)

private theorem TraditionLandingLedgerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def traditionLandingLedgerToEventFlow : TraditionLandingLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionLandingLedgerUp.mk S T R D H C P N =>
      [[BMark.b0],
        traditionLandingLedgerEncodeBHist S,
        [BMark.b1, BMark.b0],
        traditionLandingLedgerEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b0],
        traditionLandingLedgerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traditionLandingLedgerEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traditionLandingLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traditionLandingLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        traditionLandingLedgerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        traditionLandingLedgerEncodeBHist N]

def traditionLandingLedgerFromEventFlow : EventFlow → Option TraditionLandingLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagS :: restS =>
      match restS with
      | [] => none
      | S :: restTTag =>
          match restTTag with
          | [] => none
          | _tagT :: restT =>
              match restT with
              | [] => none
              | T :: restRTag =>
                  match restRTag with
                  | [] => none
                  | _tagR :: restR =>
                      match restR with
                      | [] => none
                      | R :: restDTag =>
                          match restDTag with
                          | [] => none
                          | _tagD :: restD =>
                              match restD with
                              | [] => none
                              | D :: restHTag =>
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
                                                                        (TraditionLandingLedgerUp.mk
                                                                          (traditionLandingLedgerDecodeBHist S)
                                                                          (traditionLandingLedgerDecodeBHist T)
                                                                          (traditionLandingLedgerDecodeBHist R)
                                                                          (traditionLandingLedgerDecodeBHist D)
                                                                          (traditionLandingLedgerDecodeBHist H)
                                                                          (traditionLandingLedgerDecodeBHist C)
                                                                          (traditionLandingLedgerDecodeBHist P)
                                                                          (traditionLandingLedgerDecodeBHist N))
                                                                  | _ :: _ => none

private theorem TraditionLandingLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : TraditionLandingLedgerUp,
      traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S T R D H C P N =>
      change
        some
          (TraditionLandingLedgerUp.mk
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist S))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist T))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist R))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist D))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist H))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist C))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist P))
            (traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist N))) =
          some (TraditionLandingLedgerUp.mk S T R D H C P N)
      rw [TraditionLandingLedgerTasteGate_single_carrier_alignment_decode S,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode T,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode R,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode D,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode H,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode C,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode P,
        TraditionLandingLedgerTasteGate_single_carrier_alignment_decode N]

private theorem TraditionLandingLedgerTasteGate_single_carrier_alignment_injective
    {x y : TraditionLandingLedgerUp} :
    traditionLandingLedgerToEventFlow x = traditionLandingLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) =
        traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow y) :=
    congrArg traditionLandingLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (TraditionLandingLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (TraditionLandingLedgerTasteGate_single_carrier_alignment_round_trip y)))

private def traditionLandingLedgerFields : TraditionLandingLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TraditionLandingLedgerUp.mk S T R D H C P N => [S, T, R, D, H, C, P, N]

private theorem TraditionLandingLedgerTasteGate_single_carrier_alignment_fields :
    ∀ x y : TraditionLandingLedgerUp,
      traditionLandingLedgerFields x = traditionLandingLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 T1 R1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 T2 R2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance traditionLandingLedgerBHistCarrier :
    BHistCarrier TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := traditionLandingLedgerToEventFlow
  fromEventFlow := traditionLandingLedgerFromEventFlow

instance traditionLandingLedgerChapterTasteGate :
    ChapterTasteGate TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) = some x
    exact TraditionLandingLedgerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TraditionLandingLedgerTasteGate_single_carrier_alignment_injective heq)

instance traditionLandingLedgerFieldFaithful :
    FieldFaithful TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := traditionLandingLedgerFields
  field_faithful := TraditionLandingLedgerTasteGate_single_carrier_alignment_fields

instance traditionLandingLedgerNontrivial : Nontrivial TraditionLandingLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TraditionLandingLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TraditionLandingLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TraditionLandingLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      traditionLandingLedgerDecodeBHist (traditionLandingLedgerEncodeBHist h) = h) ∧
      (∀ x : TraditionLandingLedgerUp,
        traditionLandingLedgerFromEventFlow (traditionLandingLedgerToEventFlow x) = some x) ∧
        (∀ x y : TraditionLandingLedgerUp,
          traditionLandingLedgerToEventFlow x = traditionLandingLedgerToEventFlow y → x = y) ∧
          traditionLandingLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact TraditionLandingLedgerTasteGate_single_carrier_alignment_decode
  constructor
  · exact TraditionLandingLedgerTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact TraditionLandingLedgerTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.TraditionLandingLedgerUp.TasteGate
