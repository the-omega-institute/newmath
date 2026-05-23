import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationRefutationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationRefutationUp : Type where
  | mk : (T Pi O M F D V L E H C P N : BHist) → FiniteObservationRefutationUp

def finiteObservationRefutationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationRefutationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationRefutationEncodeBHist h

def finiteObservationRefutationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationRefutationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationRefutationDecodeBHist tail)

private theorem finiteObservationRefutationDecode_encode_bhist :
    ∀ h : BHist,
      finiteObservationRefutationDecodeBHist (finiteObservationRefutationEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteObservationRefutationToEventFlow : FiniteObservationRefutationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationRefutationUp.mk T Pi O M F D V L E H C P N =>
      [[BMark.b0],
        finiteObservationRefutationEncodeBHist T,
        [BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist Pi,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteObservationRefutationEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationRefutationEncodeBHist N]

def finiteObservationRefutationFromEventFlow :
    EventFlow → Option FiniteObservationRefutationUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | T :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | Pi :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | O :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | F :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | D :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | V :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | L :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | E :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | H :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | C :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | P :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | N :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (FiniteObservationRefutationUp.mk
                                                                                                                  (finiteObservationRefutationDecodeBHist T)
                                                                                                                  (finiteObservationRefutationDecodeBHist Pi)
                                                                                                                  (finiteObservationRefutationDecodeBHist O)
                                                                                                                  (finiteObservationRefutationDecodeBHist M)
                                                                                                                  (finiteObservationRefutationDecodeBHist F)
                                                                                                                  (finiteObservationRefutationDecodeBHist D)
                                                                                                                  (finiteObservationRefutationDecodeBHist V)
                                                                                                                  (finiteObservationRefutationDecodeBHist L)
                                                                                                                  (finiteObservationRefutationDecodeBHist E)
                                                                                                                  (finiteObservationRefutationDecodeBHist H)
                                                                                                                  (finiteObservationRefutationDecodeBHist C)
                                                                                                                  (finiteObservationRefutationDecodeBHist P)
                                                                                                                  (finiteObservationRefutationDecodeBHist N))
                                                                                                          | _ :: _ => none

private theorem finiteObservationRefutation_round_trip :
    ∀ x : FiniteObservationRefutationUp,
      finiteObservationRefutationFromEventFlow
        (finiteObservationRefutationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T Pi O M F D V L E H C P N =>
      change
        some
          (FiniteObservationRefutationUp.mk
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist T))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist Pi))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist O))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist M))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist F))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist D))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist V))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist L))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist E))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist H))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist C))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist P))
            (finiteObservationRefutationDecodeBHist
              (finiteObservationRefutationEncodeBHist N))) =
          some (FiniteObservationRefutationUp.mk T Pi O M F D V L E H C P N)
      rw [finiteObservationRefutationDecode_encode_bhist T,
        finiteObservationRefutationDecode_encode_bhist Pi,
        finiteObservationRefutationDecode_encode_bhist O,
        finiteObservationRefutationDecode_encode_bhist M,
        finiteObservationRefutationDecode_encode_bhist F,
        finiteObservationRefutationDecode_encode_bhist D,
        finiteObservationRefutationDecode_encode_bhist V,
        finiteObservationRefutationDecode_encode_bhist L,
        finiteObservationRefutationDecode_encode_bhist E,
        finiteObservationRefutationDecode_encode_bhist H,
        finiteObservationRefutationDecode_encode_bhist C,
        finiteObservationRefutationDecode_encode_bhist P,
        finiteObservationRefutationDecode_encode_bhist N]

private theorem finiteObservationRefutationToEventFlow_injective
    {x y : FiniteObservationRefutationUp} :
    finiteObservationRefutationToEventFlow x =
      finiteObservationRefutationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteObservationRefutationFromEventFlow
          (finiteObservationRefutationToEventFlow x) =
        finiteObservationRefutationFromEventFlow
          (finiteObservationRefutationToEventFlow y) :=
    congrArg finiteObservationRefutationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteObservationRefutation_round_trip x).symm
      (Eq.trans hread (finiteObservationRefutation_round_trip y)))

instance finiteObservationRefutationBHistCarrier :
    BHistCarrier FiniteObservationRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationRefutationToEventFlow
  fromEventFlow := finiteObservationRefutationFromEventFlow

instance finiteObservationRefutationChapterTasteGate :
    ChapterTasteGate FiniteObservationRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteObservationRefutationFromEventFlow
        (finiteObservationRefutationToEventFlow x) = some x
    exact finiteObservationRefutation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteObservationRefutationToEventFlow_injective heq)

instance finiteObservationRefutationFieldFaithful :
    FieldFaithful FiniteObservationRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteObservationRefutationUp.mk T Pi O M F D V L E H C P N =>
        [T, Pi, O, M, F, D, V, L, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk T1 Pi1 O1 M1 F1 D1 V1 L1 E1 H1 C1 P1 N1 =>
        cases y with
        | mk T2 Pi2 O2 M2 F2 D2 V2 L2 E2 H2 C2 P2 N2 =>
            cases h
            rfl

instance finiteObservationRefutationNontrivial :
    Nontrivial FiniteObservationRefutationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteObservationRefutationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      FiniteObservationRefutationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteObservationRefutationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationRefutationChapterTasteGate

theorem FiniteObservationRefutationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteObservationRefutationDecodeBHist (finiteObservationRefutationEncodeBHist h) =
        h) ∧
      (∀ x : FiniteObservationRefutationUp,
        finiteObservationRefutationFromEventFlow
          (finiteObservationRefutationToEventFlow x) = some x) ∧
      (∀ x y : FiniteObservationRefutationUp,
        finiteObservationRefutationToEventFlow x =
          finiteObservationRefutationToEventFlow y → x = y) ∧
      finiteObservationRefutationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteObservationRefutationDecode_encode_bhist
  · constructor
    · exact finiteObservationRefutation_round_trip
    · constructor
      · intro x y heq
        exact finiteObservationRefutationToEventFlow_injective heq
      · rfl

theorem FiniteObservationRefutationCarrier_namecert_obligations
    (x : FiniteObservationRefutationUp) :
    SemanticNameCert
      (fun row : BHist => row ∈ FieldFaithful.fields x)
      (fun row : BHist => row ∈ FieldFaithful.fields x)
      (fun row : BHist => row ∈ FieldFaithful.fields x)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame NameCert
  cases x with
  | mk T Pi O M F D V L E H C P N =>
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro T (List.Mem.head [Pi, O, M, F, D, V, L, E, H, C, P, N])
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _other same
            exact hsame_symm same
          equiv_trans := by
            intro _row _middle _other sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _other same source
            cases same
            exact source
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.FiniteObservationRefutationUp
