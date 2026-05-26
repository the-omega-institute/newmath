import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArchimedeanModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArchimedeanModulusUp : Type where
  | mk : (P D S Q E A H C N : BHist) → ArchimedeanModulusUp

def archimedeanModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: archimedeanModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: archimedeanModulusEncodeBHist h

def archimedeanModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (archimedeanModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (archimedeanModulusDecodeBHist tail)

private theorem archimedeanModulus_decode_encode_bhist :
    ∀ h : BHist,
      archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def archimedeanModulusFields : ArchimedeanModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanModulusUp.mk P D S Q E A H C N => [P, D, S, Q, E, A, H, C, N]

def archimedeanModulusToEventFlow : ArchimedeanModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ArchimedeanModulusUp.mk P D S Q E A H C N =>
      archimedeanModulusEncodeBHist P ::
        archimedeanModulusEncodeBHist D ::
          archimedeanModulusEncodeBHist S ::
            archimedeanModulusEncodeBHist Q ::
              archimedeanModulusEncodeBHist E ::
                archimedeanModulusEncodeBHist A ::
                  archimedeanModulusEncodeBHist H ::
                    archimedeanModulusEncodeBHist C ::
                      archimedeanModulusEncodeBHist N :: []

def archimedeanModulusFromEventFlow : EventFlow → Option ArchimedeanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    match flow with
    | [] => none
    | P :: rest0 =>
      match rest0 with
      | [] => none
      | D :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | Q :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                              | C :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (ArchimedeanModulusUp.mk
                                              (archimedeanModulusDecodeBHist P)
                                              (archimedeanModulusDecodeBHist D)
                                              (archimedeanModulusDecodeBHist S)
                                              (archimedeanModulusDecodeBHist Q)
                                              (archimedeanModulusDecodeBHist E)
                                              (archimedeanModulusDecodeBHist A)
                                              (archimedeanModulusDecodeBHist H)
                                              (archimedeanModulusDecodeBHist C)
                                              (archimedeanModulusDecodeBHist N))
                                      | _ :: _ => none

private theorem archimedeanModulus_round_trip :
    ∀ x : ArchimedeanModulusUp,
      archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P D S Q E A H C N =>
      change
        some
          (ArchimedeanModulusUp.mk
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist P))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist D))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist S))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist Q))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist E))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist A))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist H))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist C))
            (archimedeanModulusDecodeBHist (archimedeanModulusEncodeBHist N))) =
          some (ArchimedeanModulusUp.mk P D S Q E A H C N)
      rw [archimedeanModulus_decode_encode_bhist P,
        archimedeanModulus_decode_encode_bhist D,
        archimedeanModulus_decode_encode_bhist S,
        archimedeanModulus_decode_encode_bhist Q,
        archimedeanModulus_decode_encode_bhist E,
        archimedeanModulus_decode_encode_bhist A,
        archimedeanModulus_decode_encode_bhist H,
        archimedeanModulus_decode_encode_bhist C,
        archimedeanModulus_decode_encode_bhist N]

private theorem archimedeanModulusToEventFlow_injective {x y : ArchimedeanModulusUp} :
    archimedeanModulusToEventFlow x = archimedeanModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) =
        archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow y) :=
    congrArg archimedeanModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (archimedeanModulus_round_trip x).symm
      (Eq.trans hread (archimedeanModulus_round_trip y)))

private theorem archimedeanModulus_field_faithful :
    ∀ x y : ArchimedeanModulusUp,
      archimedeanModulusFields x = archimedeanModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk P₁ D₁ S₁ Q₁ E₁ A₁ H₁ C₁ N₁ =>
      cases y with
      | mk P₂ D₂ S₂ Q₂ E₂ A₂ H₂ C₂ N₂ =>
          cases h
          rfl

instance archimedeanModulusBHistCarrier : BHistCarrier ArchimedeanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := archimedeanModulusToEventFlow
  fromEventFlow := archimedeanModulusFromEventFlow

instance archimedeanModulusChapterTasteGate :
    ChapterTasteGate ArchimedeanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) = some x
    exact archimedeanModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (archimedeanModulusToEventFlow_injective heq)

instance archimedeanModulusFieldFaithful : FieldFaithful ArchimedeanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := archimedeanModulusFields
  field_faithful := archimedeanModulus_field_faithful

instance archimedeanModulusNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ArchimedeanModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ArchimedeanModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ArchimedeanModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ArchimedeanModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  archimedeanModulusChapterTasteGate

theorem ArchimedeanModulusTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ArchimedeanModulusUp) ∧
      Nonempty (FieldFaithful ArchimedeanModulusUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ArchimedeanModulusUp) ∧
          (∀ h : BHist, archimedeanModulusDecodeBHist
            (archimedeanModulusEncodeBHist h) = h) ∧
            (∀ x : ArchimedeanModulusUp,
              archimedeanModulusFromEventFlow (archimedeanModulusToEventFlow x) =
                some x) ∧
              (∀ x y : ArchimedeanModulusUp,
                archimedeanModulusToEventFlow x = archimedeanModulusToEventFlow y →
                  x = y) ∧
                archimedeanModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨⟨archimedeanModulusChapterTasteGate⟩, ⟨archimedeanModulusFieldFaithful⟩,
      ⟨archimedeanModulusNontrivial⟩, archimedeanModulus_decode_encode_bhist,
      archimedeanModulus_round_trip,
      (fun _ _ heq => archimedeanModulusToEventFlow_injective heq), rfl⟩

end BEDC.Derived.ArchimedeanModulusUp
