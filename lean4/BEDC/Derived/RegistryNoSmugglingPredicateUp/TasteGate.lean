import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegistryNoSmugglingPredicateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegistryNoSmugglingPredicateUp : Type where
  | mk : (T E G U H C P N : BHist) → RegistryNoSmugglingPredicateUp
  deriving DecidableEq

def registryNoSmugglingPredicateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: registryNoSmugglingPredicateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: registryNoSmugglingPredicateEncodeBHist h

def registryNoSmugglingPredicateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (registryNoSmugglingPredicateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (registryNoSmugglingPredicateDecodeBHist tail)

theorem RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      registryNoSmugglingPredicateDecodeBHist
          (registryNoSmugglingPredicateEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def registryNoSmugglingPredicateToEventFlow :
    RegistryNoSmugglingPredicateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RegistryNoSmugglingPredicateUp.mk T E G U H C P N =>
      [[BMark.b0],
        registryNoSmugglingPredicateEncodeBHist T,
        [BMark.b1, BMark.b0],
        registryNoSmugglingPredicateEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b0],
        registryNoSmugglingPredicateEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryNoSmugglingPredicateEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryNoSmugglingPredicateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryNoSmugglingPredicateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        registryNoSmugglingPredicateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        registryNoSmugglingPredicateEncodeBHist N]

def registryNoSmugglingPredicateFromEventFlow :
    EventFlow → Option RegistryNoSmugglingPredicateUp
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
              | E :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | U :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | C :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | P :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | N :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (RegistryNoSmugglingPredicateUp.mk
                                                                          (registryNoSmugglingPredicateDecodeBHist T)
                                                                          (registryNoSmugglingPredicateDecodeBHist E)
                                                                          (registryNoSmugglingPredicateDecodeBHist G)
                                                                          (registryNoSmugglingPredicateDecodeBHist U)
                                                                          (registryNoSmugglingPredicateDecodeBHist H)
                                                                          (registryNoSmugglingPredicateDecodeBHist C)
                                                                          (registryNoSmugglingPredicateDecodeBHist P)
                                                                          (registryNoSmugglingPredicateDecodeBHist N))
                                                                  | _ :: _ => none

theorem RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegistryNoSmugglingPredicateUp,
      registryNoSmugglingPredicateFromEventFlow
          (registryNoSmugglingPredicateToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T E G U H C P N =>
      change
        some
          (RegistryNoSmugglingPredicateUp.mk
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist T))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist E))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist G))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist U))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist H))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist C))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist P))
            (registryNoSmugglingPredicateDecodeBHist
              (registryNoSmugglingPredicateEncodeBHist N))) =
          some (RegistryNoSmugglingPredicateUp.mk T E G U H C P N)
      rw [RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode T,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode E,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode G,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode U,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode H,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode C,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode P,
        RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode N]

theorem RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_injective
    {x y : RegistryNoSmugglingPredicateUp} :
    registryNoSmugglingPredicateToEventFlow x =
        registryNoSmugglingPredicateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      registryNoSmugglingPredicateFromEventFlow
          (registryNoSmugglingPredicateToEventFlow x) =
        registryNoSmugglingPredicateFromEventFlow
          (registryNoSmugglingPredicateToEventFlow y) :=
    congrArg registryNoSmugglingPredicateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_round_trip y)))

instance registryNoSmugglingPredicateBHistCarrier :
    BHistCarrier RegistryNoSmugglingPredicateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := registryNoSmugglingPredicateToEventFlow
  fromEventFlow := registryNoSmugglingPredicateFromEventFlow

instance registryNoSmugglingPredicateChapterTasteGate :
    ChapterTasteGate RegistryNoSmugglingPredicateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      registryNoSmugglingPredicateFromEventFlow
          (registryNoSmugglingPredicateToEventFlow x) =
        some x
    exact RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_injective heq)

instance registryNoSmugglingPredicateFieldFaithful :
    FieldFaithful RegistryNoSmugglingPredicateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RegistryNoSmugglingPredicateUp.mk T E G U H C P N => [T, E, G, U, H, C, P, N]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk T1 E1 G1 U1 H1 C1 P1 N1 =>
        cases y with
        | mk T2 E2 G2 U2 H2 C2 P2 N2 =>
            injection hfields with hT tail1
            cases hT
            injection tail1 with hE tail2
            cases hE
            injection tail2 with hG tail3
            cases hG
            injection tail3 with hU tail4
            cases hU
            injection tail4 with hH tail5
            cases hH
            injection tail5 with hC tail6
            cases hC
            injection tail6 with hP tail7
            cases hP
            injection tail7 with hN _
            cases hN
            rfl

instance registryNoSmugglingPredicateNontrivial :
    Nontrivial RegistryNoSmugglingPredicateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegistryNoSmugglingPredicateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegistryNoSmugglingPredicateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hT
        cases hT⟩

theorem RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        registryNoSmugglingPredicateDecodeBHist
            (registryNoSmugglingPredicateEncodeBHist h) =
          h) ∧
      (∀ x : RegistryNoSmugglingPredicateUp,
        registryNoSmugglingPredicateFromEventFlow
            (registryNoSmugglingPredicateToEventFlow x) =
          some x) ∧
        (∀ x y : RegistryNoSmugglingPredicateUp,
          registryNoSmugglingPredicateToEventFlow x =
              registryNoSmugglingPredicateToEventFlow y →
            x = y) ∧
          registryNoSmugglingPredicateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_decode
  · constructor
    · exact RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact RegistryNoSmugglingPredicateTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.RegistryNoSmugglingPredicateUp
