import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EilenbergSteenrodAxiomsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EilenbergSteenrodAxiomsUp : Type where
  | mk (H C S T D X E I Nt R P L : BHist) : EilenbergSteenrodAxiomsUp
  deriving DecidableEq

def eilenbergSteenrodAxiomsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eilenbergSteenrodAxiomsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eilenbergSteenrodAxiomsEncodeBHist h

def eilenbergSteenrodAxiomsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eilenbergSteenrodAxiomsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eilenbergSteenrodAxiomsDecodeBHist tail)

private theorem eilenbergSteenrodAxiomsDecode_encode_bhist :
    ∀ h : BHist,
      eilenbergSteenrodAxiomsDecodeBHist
        (eilenbergSteenrodAxiomsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eilenbergSteenrodAxiomsFields :
    EilenbergSteenrodAxiomsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EilenbergSteenrodAxiomsUp.mk H C S T D X E I Nt R P L =>
      [H, C, S, T, D, X, E, I, Nt, R, P, L]

def eilenbergSteenrodAxiomsToEventFlow :
    EilenbergSteenrodAxiomsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eilenbergSteenrodAxiomsFields x).map eilenbergSteenrodAxiomsEncodeBHist

def eilenbergSteenrodAxiomsFromEventFlow :
    EventFlow → Option EilenbergSteenrodAxiomsUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | H :: rest0 =>
      match rest0 with
      | [] => none
      | C :: rest1 =>
          match rest1 with
          | [] => none
          | S :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | D :: rest4 =>
                      match rest4 with
                      | [] => none
                      | X :: rest5 =>
                          match rest5 with
                          | [] => none
                          | E :: rest6 =>
                              match rest6 with
                              | [] => none
                              | I :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Nt :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | R :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | L :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (EilenbergSteenrodAxiomsUp.mk
                                                          (eilenbergSteenrodAxiomsDecodeBHist H)
                                                          (eilenbergSteenrodAxiomsDecodeBHist C)
                                                          (eilenbergSteenrodAxiomsDecodeBHist S)
                                                          (eilenbergSteenrodAxiomsDecodeBHist T)
                                                          (eilenbergSteenrodAxiomsDecodeBHist D)
                                                          (eilenbergSteenrodAxiomsDecodeBHist X)
                                                          (eilenbergSteenrodAxiomsDecodeBHist E)
                                                          (eilenbergSteenrodAxiomsDecodeBHist I)
                                                          (eilenbergSteenrodAxiomsDecodeBHist Nt)
                                                          (eilenbergSteenrodAxiomsDecodeBHist R)
                                                          (eilenbergSteenrodAxiomsDecodeBHist P)
                                                          (eilenbergSteenrodAxiomsDecodeBHist L))
                                                  | _ :: _ => none

private theorem eilenbergSteenrodAxioms_round_trip :
    ∀ x : EilenbergSteenrodAxiomsUp,
      eilenbergSteenrodAxiomsFromEventFlow
        (eilenbergSteenrodAxiomsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk H C S T D X E I Nt R P L =>
      change
        some
          (EilenbergSteenrodAxiomsUp.mk
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist H))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist C))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist S))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist T))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist D))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist X))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist E))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist I))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist Nt))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist R))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist P))
            (eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist L))) =
          some (EilenbergSteenrodAxiomsUp.mk H C S T D X E I Nt R P L)
      rw [eilenbergSteenrodAxiomsDecode_encode_bhist H,
        eilenbergSteenrodAxiomsDecode_encode_bhist C,
        eilenbergSteenrodAxiomsDecode_encode_bhist S,
        eilenbergSteenrodAxiomsDecode_encode_bhist T,
        eilenbergSteenrodAxiomsDecode_encode_bhist D,
        eilenbergSteenrodAxiomsDecode_encode_bhist X,
        eilenbergSteenrodAxiomsDecode_encode_bhist E,
        eilenbergSteenrodAxiomsDecode_encode_bhist I,
        eilenbergSteenrodAxiomsDecode_encode_bhist Nt,
        eilenbergSteenrodAxiomsDecode_encode_bhist R,
        eilenbergSteenrodAxiomsDecode_encode_bhist P,
        eilenbergSteenrodAxiomsDecode_encode_bhist L]

private theorem eilenbergSteenrodAxiomsToEventFlow_injective
    {x y : EilenbergSteenrodAxiomsUp} :
    eilenbergSteenrodAxiomsToEventFlow x =
      eilenbergSteenrodAxiomsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eilenbergSteenrodAxiomsFromEventFlow
          (eilenbergSteenrodAxiomsToEventFlow x) =
        eilenbergSteenrodAxiomsFromEventFlow
          (eilenbergSteenrodAxiomsToEventFlow y) :=
    congrArg eilenbergSteenrodAxiomsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (eilenbergSteenrodAxioms_round_trip x).symm
      (Eq.trans hread (eilenbergSteenrodAxioms_round_trip y)))

private theorem eilenbergSteenrodAxioms_fields_faithful :
    ∀ x y : EilenbergSteenrodAxiomsUp,
      eilenbergSteenrodAxiomsFields x = eilenbergSteenrodAxiomsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk H1 C1 S1 T1 D1 X1 E1 I1 Nt1 R1 P1 L1 =>
      cases y with
      | mk H2 C2 S2 T2 D2 X2 E2 I2 Nt2 R2 P2 L2 =>
          cases hfields
          rfl

instance eilenbergSteenrodAxiomsBHistCarrier :
    BHistCarrier EilenbergSteenrodAxiomsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eilenbergSteenrodAxiomsToEventFlow
  fromEventFlow := eilenbergSteenrodAxiomsFromEventFlow

instance eilenbergSteenrodAxiomsChapterTasteGate :
    ChapterTasteGate EilenbergSteenrodAxiomsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      eilenbergSteenrodAxiomsFromEventFlow
        (eilenbergSteenrodAxiomsToEventFlow x) = some x
    exact eilenbergSteenrodAxioms_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (eilenbergSteenrodAxiomsToEventFlow_injective heq)

instance eilenbergSteenrodAxiomsFieldFaithful :
    FieldFaithful EilenbergSteenrodAxiomsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eilenbergSteenrodAxiomsFields
  field_faithful := eilenbergSteenrodAxioms_fields_faithful

instance eilenbergSteenrodAxiomsNontrivial :
    BEDC.Meta.TasteGate.Nontrivial EilenbergSteenrodAxiomsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EilenbergSteenrodAxiomsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      EilenbergSteenrodAxiomsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem EilenbergSteenrodAxiomsTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate EilenbergSteenrodAxiomsUp) ∧
      Nonempty (FieldFaithful EilenbergSteenrodAxiomsUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial EilenbergSteenrodAxiomsUp) ∧
          (∀ h : BHist,
            eilenbergSteenrodAxiomsDecodeBHist
              (eilenbergSteenrodAxiomsEncodeBHist h) = h) ∧
            (∀ x : EilenbergSteenrodAxiomsUp,
              eilenbergSteenrodAxiomsFromEventFlow
                (eilenbergSteenrodAxiomsToEventFlow x) = some x) ∧
              (∀ x y : EilenbergSteenrodAxiomsUp,
                eilenbergSteenrodAxiomsToEventFlow x =
                  eilenbergSteenrodAxiomsToEventFlow y → x = y) ∧
                eilenbergSteenrodAxiomsEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨eilenbergSteenrodAxiomsChapterTasteGate⟩
  · constructor
    · exact ⟨eilenbergSteenrodAxiomsFieldFaithful⟩
    · constructor
      · exact ⟨eilenbergSteenrodAxiomsNontrivial⟩
      · constructor
        · exact eilenbergSteenrodAxiomsDecode_encode_bhist
        · constructor
          · exact eilenbergSteenrodAxioms_round_trip
          · constructor
            · intro x y heq
              exact eilenbergSteenrodAxiomsToEventFlow_injective heq
            · rfl

end BEDC.Derived.EilenbergSteenrodAxiomsUp
