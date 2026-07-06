import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SingularHomologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SingularHomologyUp : Type where
  | mk (X Delta Sigma C B Z Q H T P N : BHist) : SingularHomologyUp
  deriving DecidableEq

def singularHomologyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: singularHomologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: singularHomologyEncodeBHist h

def singularHomologyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (singularHomologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (singularHomologyDecodeBHist tail)

private theorem singularHomology_decode_encode_bhist :
    ∀ h : BHist, singularHomologyDecodeBHist (singularHomologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def singularHomologyFields : SingularHomologyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SingularHomologyUp.mk X Delta Sigma C B Z Q H T P N =>
      [X, Delta, Sigma, C, B, Z, Q, H, T, P, N]

def singularHomologyToEventFlow : SingularHomologyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map singularHomologyEncodeBHist (singularHomologyFields x)

def singularHomologyFromEventFlow : EventFlow -> Option SingularHomologyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | Delta :: rest1 =>
          match rest1 with
          | [] => none
          | Sigma :: rest2 =>
              match rest2 with
              | [] => none
              | C :: rest3 =>
                  match rest3 with
                  | [] => none
                  | B :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Z :: rest5 =>
                          match rest5 with
                          | [] => none
                          | Q :: rest6 =>
                              match rest6 with
                              | [] => none
                              | H :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | T :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | P :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | N :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (SingularHomologyUp.mk
                                                      (singularHomologyDecodeBHist X)
                                                      (singularHomologyDecodeBHist Delta)
                                                      (singularHomologyDecodeBHist Sigma)
                                                      (singularHomologyDecodeBHist C)
                                                      (singularHomologyDecodeBHist B)
                                                      (singularHomologyDecodeBHist Z)
                                                      (singularHomologyDecodeBHist Q)
                                                      (singularHomologyDecodeBHist H)
                                                      (singularHomologyDecodeBHist T)
                                                      (singularHomologyDecodeBHist P)
                                                      (singularHomologyDecodeBHist N))
                                              | _ :: _ => none

private theorem singularHomology_round_trip :
    ∀ x : SingularHomologyUp,
      singularHomologyFromEventFlow (singularHomologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Delta Sigma C B Z Q H T P N =>
      change
        some
          (SingularHomologyUp.mk
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist X))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist Delta))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist Sigma))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist C))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist B))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist Z))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist Q))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist H))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist T))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist P))
            (singularHomologyDecodeBHist (singularHomologyEncodeBHist N))) =
          some (SingularHomologyUp.mk X Delta Sigma C B Z Q H T P N)
      rw [singularHomology_decode_encode_bhist X,
        singularHomology_decode_encode_bhist Delta,
        singularHomology_decode_encode_bhist Sigma,
        singularHomology_decode_encode_bhist C,
        singularHomology_decode_encode_bhist B,
        singularHomology_decode_encode_bhist Z,
        singularHomology_decode_encode_bhist Q,
        singularHomology_decode_encode_bhist H,
        singularHomology_decode_encode_bhist T,
        singularHomology_decode_encode_bhist P,
        singularHomology_decode_encode_bhist N]

private theorem singularHomologyToEventFlow_injective {x y : SingularHomologyUp} :
    singularHomologyToEventFlow x = singularHomologyToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      singularHomologyFromEventFlow (singularHomologyToEventFlow x) =
        singularHomologyFromEventFlow (singularHomologyToEventFlow y) :=
    congrArg singularHomologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (singularHomology_round_trip x).symm
      (Eq.trans hread (singularHomology_round_trip y)))

private theorem singularHomology_field_faithful :
    ∀ x y : SingularHomologyUp, singularHomologyFields x = singularHomologyFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 Delta1 Sigma1 C1 B1 Z1 Q1 H1 T1 P1 N1 =>
      cases y with
      | mk X2 Delta2 Sigma2 C2 B2 Z2 Q2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance singularHomologyBHistCarrier : BHistCarrier SingularHomologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := singularHomologyToEventFlow
  fromEventFlow := singularHomologyFromEventFlow

instance singularHomologyChapterTasteGate : ChapterTasteGate SingularHomologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change singularHomologyFromEventFlow (singularHomologyToEventFlow x) = some x
    exact singularHomology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (singularHomologyToEventFlow_injective heq)

instance singularHomologyFieldFaithful : FieldFaithful SingularHomologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := singularHomologyFields
  field_faithful := singularHomology_field_faithful

instance singularHomologyNontrivial : Nontrivial SingularHomologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SingularHomologyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SingularHomologyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SingularHomologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  singularHomologyChapterTasteGate

theorem SingularHomologyTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate SingularHomologyUp) ∧
      Nonempty (FieldFaithful SingularHomologyUp) ∧
        Nonempty (Nontrivial SingularHomologyUp) ∧
          (∀ h : BHist, singularHomologyDecodeBHist (singularHomologyEncodeBHist h) = h) ∧
            singularHomologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨singularHomologyChapterTasteGate⟩, ⟨singularHomologyFieldFaithful⟩,
      ⟨singularHomologyNontrivial⟩, singularHomology_decode_encode_bhist, rfl⟩

end BEDC.Derived.SingularHomologyUp
