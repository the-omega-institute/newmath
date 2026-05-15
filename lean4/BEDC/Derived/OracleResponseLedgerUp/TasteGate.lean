import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OracleResponseLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OracleResponseLedgerUp : Type where
  | mk (S Q R B F E H C P N : BHist) : OracleResponseLedgerUp
  deriving DecidableEq

def oracleResponseLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: oracleResponseLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: oracleResponseLedgerEncodeBHist h

def oracleResponseLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (oracleResponseLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (oracleResponseLedgerDecodeBHist tail)

private theorem oracleResponseLedgerDecode_encode_bhist :
    ∀ h : BHist, oracleResponseLedgerDecodeBHist (oracleResponseLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def oracleResponseLedgerToEventFlow : OracleResponseLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | OracleResponseLedgerUp.mk S Q R B F E H C P N =>
      [[BMark.b0],
        oracleResponseLedgerEncodeBHist S,
        [BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        oracleResponseLedgerEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        oracleResponseLedgerEncodeBHist N]

private def oracleResponseLedgerDecodePacket
    (S Q R B F E H C P N : RawEvent) : OracleResponseLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  OracleResponseLedgerUp.mk
    (oracleResponseLedgerDecodeBHist S)
    (oracleResponseLedgerDecodeBHist Q)
    (oracleResponseLedgerDecodeBHist R)
    (oracleResponseLedgerDecodeBHist B)
    (oracleResponseLedgerDecodeBHist F)
    (oracleResponseLedgerDecodeBHist E)
    (oracleResponseLedgerDecodeBHist H)
    (oracleResponseLedgerDecodeBHist C)
    (oracleResponseLedgerDecodeBHist P)
    (oracleResponseLedgerDecodeBHist N)

def oracleResponseLedgerFromEventFlow : EventFlow → Option OracleResponseLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tagS :: restS =>
      match restS with
      | [] => none
      | S :: restQTag =>
          match restQTag with
          | [] => none
          | _tagQ :: restQ =>
              match restQ with
              | [] => none
              | Q :: restRTag =>
                  match restRTag with
                  | [] => none
                  | _tagR :: restR =>
                      match restR with
                      | [] => none
                      | R :: restBTag =>
                          match restBTag with
                          | [] => none
                          | _tagB :: restB =>
                              match restB with
                              | [] => none
                              | B :: restFTag =>
                                  match restFTag with
                                  | [] => none
                                  | _tagF :: restF =>
                                      match restF with
                                      | [] => none
                                      | F :: restETag =>
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
                                                                              | N :: restFinal =>
                                                                                  match restFinal with
                                                                                  | [] =>
                                                                                      some
                                                                                        (oracleResponseLedgerDecodePacket
                                                                                          S Q R B F E H C P N)
                                                                                  | _ :: _ => none

private theorem oracleResponseLedger_round_trip :
    ∀ x : OracleResponseLedgerUp,
      oracleResponseLedgerFromEventFlow (oracleResponseLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S Q R B F E H C P N =>
      change
        some
            (oracleResponseLedgerDecodePacket
              (oracleResponseLedgerEncodeBHist S)
              (oracleResponseLedgerEncodeBHist Q)
              (oracleResponseLedgerEncodeBHist R)
              (oracleResponseLedgerEncodeBHist B)
              (oracleResponseLedgerEncodeBHist F)
              (oracleResponseLedgerEncodeBHist E)
              (oracleResponseLedgerEncodeBHist H)
              (oracleResponseLedgerEncodeBHist C)
              (oracleResponseLedgerEncodeBHist P)
              (oracleResponseLedgerEncodeBHist N)) =
          some (OracleResponseLedgerUp.mk S Q R B F E H C P N)
      unfold oracleResponseLedgerDecodePacket
      rw [oracleResponseLedgerDecode_encode_bhist S,
        oracleResponseLedgerDecode_encode_bhist Q,
        oracleResponseLedgerDecode_encode_bhist R,
        oracleResponseLedgerDecode_encode_bhist B,
        oracleResponseLedgerDecode_encode_bhist F,
        oracleResponseLedgerDecode_encode_bhist E,
        oracleResponseLedgerDecode_encode_bhist H,
        oracleResponseLedgerDecode_encode_bhist C,
        oracleResponseLedgerDecode_encode_bhist P,
        oracleResponseLedgerDecode_encode_bhist N]

private theorem oracleResponseLedgerToEventFlow_injective {x y : OracleResponseLedgerUp} :
    oracleResponseLedgerToEventFlow x = oracleResponseLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      oracleResponseLedgerFromEventFlow (oracleResponseLedgerToEventFlow x) =
        oracleResponseLedgerFromEventFlow (oracleResponseLedgerToEventFlow y) :=
    congrArg oracleResponseLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (oracleResponseLedger_round_trip x).symm
      (Eq.trans hread (oracleResponseLedger_round_trip y)))

def oracleResponseLedgerFields : OracleResponseLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OracleResponseLedgerUp.mk S Q R B F E H C P N => [S, Q, R, B, F, E, H, C, P, N]

private theorem oracleResponseLedgerFields_faithful :
    ∀ x y : OracleResponseLedgerUp, oracleResponseLedgerFields x = oracleResponseLedgerFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk S₁ Q₁ R₁ B₁ F₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ Q₂ R₂ B₂ F₂ E₂ H₂ C₂ P₂ N₂ =>
          cases h
          rfl

instance oracleResponseLedgerBHistCarrier : BHistCarrier OracleResponseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := oracleResponseLedgerToEventFlow
  fromEventFlow := oracleResponseLedgerFromEventFlow

instance oracleResponseLedgerChapterTasteGate : ChapterTasteGate OracleResponseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change oracleResponseLedgerFromEventFlow (oracleResponseLedgerToEventFlow x) = some x
    exact oracleResponseLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (oracleResponseLedgerToEventFlow_injective heq)

instance oracleResponseLedgerFieldFaithful : FieldFaithful OracleResponseLedgerUp where
  fields := oracleResponseLedgerFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    exact oracleResponseLedgerFields_faithful

instance oracleResponseLedgerNontrivial : Nontrivial OracleResponseLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨OracleResponseLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      OracleResponseLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate OracleResponseLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  oracleResponseLedgerChapterTasteGate

theorem OracleResponseLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, oracleResponseLedgerDecodeBHist (oracleResponseLedgerEncodeBHist h) = h) ∧
      (∀ x : OracleResponseLedgerUp,
        oracleResponseLedgerFromEventFlow (oracleResponseLedgerToEventFlow x) = some x) ∧
        (∀ x y : OracleResponseLedgerUp,
          oracleResponseLedgerToEventFlow x = oracleResponseLedgerToEventFlow y → x = y) ∧
          oracleResponseLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : OracleResponseLedgerUp,
              oracleResponseLedgerFields x = oracleResponseLedgerFields y → x = y) ∧
              (∃ x y : OracleResponseLedgerUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact oracleResponseLedgerDecode_encode_bhist
  · constructor
    · exact oracleResponseLedger_round_trip
    · constructor
      · intro x y heq
        exact oracleResponseLedgerToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact oracleResponseLedgerFields_faithful
          · exact
              ⟨OracleResponseLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                OracleResponseLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.OracleResponseLedgerUp
