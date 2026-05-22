import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindCutCauchyBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindCutCauchyBoundaryUp : Type where
  | mk (L U K Q S R D E H C P N : BHist) : DedekindCutCauchyBoundaryUp
  deriving DecidableEq

def dedekindCutCauchyBoundaryEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dedekindCutCauchyBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dedekindCutCauchyBoundaryEncodeBHist h

def dedekindCutCauchyBoundaryDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dedekindCutCauchyBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dedekindCutCauchyBoundaryDecodeBHist tail)

private theorem dedekindCutCauchyBoundaryDecode_encode_bhist :
    forall h : BHist,
      dedekindCutCauchyBoundaryDecodeBHist (dedekindCutCauchyBoundaryEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dedekindCutCauchyBoundaryFields :
    DedekindCutCauchyBoundaryUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N =>
      [L, U, K, Q, S, R, D, E, H, C, P, N]

def dedekindCutCauchyBoundaryToEventFlow :
    DedekindCutCauchyBoundaryUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dedekindCutCauchyBoundaryFields x).map dedekindCutCauchyBoundaryEncodeBHist

def dedekindCutCauchyBoundaryFromEventFlow :
    EventFlow -> Option DedekindCutCauchyBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | L :: restU =>
      match restU with
      | [] => none
      | U :: restK =>
          match restK with
          | [] => none
          | K :: restQ =>
              match restQ with
              | [] => none
              | Q :: restS =>
                  match restS with
                  | [] => none
                  | S :: restR =>
                      match restR with
                      | [] => none
                      | R :: restD =>
                          match restD with
                          | [] => none
                          | D :: restE =>
                              match restE with
                              | [] => none
                              | E :: restH =>
                                  match restH with
                                  | [] => none
                                  | H :: restC =>
                                      match restC with
                                      | [] => none
                                      | C :: restP =>
                                          match restP with
                                          | [] => none
                                          | P :: restN =>
                                              match restN with
                                              | [] => none
                                              | N :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (DedekindCutCauchyBoundaryUp.mk
                                                          (dedekindCutCauchyBoundaryDecodeBHist L)
                                                          (dedekindCutCauchyBoundaryDecodeBHist U)
                                                          (dedekindCutCauchyBoundaryDecodeBHist K)
                                                          (dedekindCutCauchyBoundaryDecodeBHist Q)
                                                          (dedekindCutCauchyBoundaryDecodeBHist S)
                                                          (dedekindCutCauchyBoundaryDecodeBHist R)
                                                          (dedekindCutCauchyBoundaryDecodeBHist D)
                                                          (dedekindCutCauchyBoundaryDecodeBHist E)
                                                          (dedekindCutCauchyBoundaryDecodeBHist H)
                                                          (dedekindCutCauchyBoundaryDecodeBHist C)
                                                          (dedekindCutCauchyBoundaryDecodeBHist P)
                                                          (dedekindCutCauchyBoundaryDecodeBHist N))
                                                  | _ :: _ => none

private theorem dedekindCutCauchyBoundary_round_trip :
    forall x : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K Q S R D E H C P N =>
      change
        some
          (DedekindCutCauchyBoundaryUp.mk
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist L))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist U))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist K))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist Q))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist S))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist R))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist D))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist E))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist H))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist C))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist P))
            (dedekindCutCauchyBoundaryDecodeBHist
              (dedekindCutCauchyBoundaryEncodeBHist N))) =
          some (DedekindCutCauchyBoundaryUp.mk L U K Q S R D E H C P N)
      rw [dedekindCutCauchyBoundaryDecode_encode_bhist L,
        dedekindCutCauchyBoundaryDecode_encode_bhist U,
        dedekindCutCauchyBoundaryDecode_encode_bhist K,
        dedekindCutCauchyBoundaryDecode_encode_bhist Q,
        dedekindCutCauchyBoundaryDecode_encode_bhist S,
        dedekindCutCauchyBoundaryDecode_encode_bhist R,
        dedekindCutCauchyBoundaryDecode_encode_bhist D,
        dedekindCutCauchyBoundaryDecode_encode_bhist E,
        dedekindCutCauchyBoundaryDecode_encode_bhist H,
        dedekindCutCauchyBoundaryDecode_encode_bhist C,
        dedekindCutCauchyBoundaryDecode_encode_bhist P,
        dedekindCutCauchyBoundaryDecode_encode_bhist N]

private theorem dedekindCutCauchyBoundaryToEventFlow_injective
    {x y : DedekindCutCauchyBoundaryUp} :
    dedekindCutCauchyBoundaryToEventFlow x =
        dedekindCutCauchyBoundaryToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow y) :=
    congrArg dedekindCutCauchyBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dedekindCutCauchyBoundary_round_trip x).symm
      (Eq.trans hread (dedekindCutCauchyBoundary_round_trip y)))

private theorem dedekindCutCauchyBoundary_fields_faithful :
    forall x y : DedekindCutCauchyBoundaryUp,
      dedekindCutCauchyBoundaryFields x = dedekindCutCauchyBoundaryFields y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 K1 Q1 S1 R1 D1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 K2 Q2 S2 R2 D2 E2 H2 C2 P2 N2 =>
          injection hfields with hL t1
          cases hL
          injection t1 with hU t2
          cases hU
          injection t2 with hK t3
          cases hK
          injection t3 with hQ t4
          cases hQ
          injection t4 with hS t5
          cases hS
          injection t5 with hR t6
          cases hR
          injection t6 with hD t7
          cases hD
          injection t7 with hE t8
          cases hE
          injection t8 with hH t9
          cases hH
          injection t9 with hC t10
          cases hC
          injection t10 with hP t11
          cases hP
          injection t11 with hN _
          cases hN
          rfl

instance dedekindCutCauchyBoundaryBHistCarrier :
    BHistCarrier DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dedekindCutCauchyBoundaryToEventFlow
  fromEventFlow := dedekindCutCauchyBoundaryFromEventFlow

instance dedekindCutCauchyBoundaryChapterTasteGate :
    ChapterTasteGate DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dedekindCutCauchyBoundaryFromEventFlow
          (dedekindCutCauchyBoundaryToEventFlow x) =
        some x
    exact dedekindCutCauchyBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dedekindCutCauchyBoundaryToEventFlow_injective heq)

instance dedekindCutCauchyBoundaryFieldFaithful :
    FieldFaithful DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dedekindCutCauchyBoundaryFields
  field_faithful := dedekindCutCauchyBoundary_fields_faithful

instance dedekindCutCauchyBoundaryNontrivial :
    Nontrivial DedekindCutCauchyBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindCutCauchyBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DedekindCutCauchyBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dedekindCutCauchyBoundaryChapterTasteGate

namespace TasteGate

theorem DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DedekindCutCauchyBoundaryUp) ∧
      Nonempty (FieldFaithful DedekindCutCauchyBoundaryUp) ∧
        Nonempty (Nontrivial DedekindCutCauchyBoundaryUp) ∧
          (forall h : BHist,
            dedekindCutCauchyBoundaryDecodeBHist
                (dedekindCutCauchyBoundaryEncodeBHist h) =
              h) ∧
            (forall x : DedekindCutCauchyBoundaryUp,
              dedekindCutCauchyBoundaryFromEventFlow
                  (dedekindCutCauchyBoundaryToEventFlow x) =
                some x) ∧
              (forall x y : DedekindCutCauchyBoundaryUp,
                dedekindCutCauchyBoundaryToEventFlow x =
                    dedekindCutCauchyBoundaryToEventFlow y ->
                  x = y) ∧
                dedekindCutCauchyBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨dedekindCutCauchyBoundaryChapterTasteGate⟩
  · constructor
    · exact ⟨dedekindCutCauchyBoundaryFieldFaithful⟩
    · constructor
      · exact ⟨dedekindCutCauchyBoundaryNontrivial⟩
      · constructor
        · exact dedekindCutCauchyBoundaryDecode_encode_bhist
        · constructor
          · exact dedekindCutCauchyBoundary_round_trip
          · constructor
            · intro x y heq
              exact dedekindCutCauchyBoundaryToEventFlow_injective heq
            · rfl

theorem DedekindCutCauchyBoundaryUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DedekindCutCauchyBoundaryUp) ∧
      Nonempty (FieldFaithful DedekindCutCauchyBoundaryUp) ∧
        Nonempty (Nontrivial DedekindCutCauchyBoundaryUp) ∧
          (forall h : BHist,
            dedekindCutCauchyBoundaryDecodeBHist
                (dedekindCutCauchyBoundaryEncodeBHist h) =
              h) ∧
            (forall x : DedekindCutCauchyBoundaryUp,
              dedekindCutCauchyBoundaryFromEventFlow
                  (dedekindCutCauchyBoundaryToEventFlow x) =
                some x) ∧
              (forall x y : DedekindCutCauchyBoundaryUp,
                dedekindCutCauchyBoundaryToEventFlow x =
                    dedekindCutCauchyBoundaryToEventFlow y ->
                  x = y) ∧
                dedekindCutCauchyBoundaryEncodeBHist BHist.Empty = ([] : RawEvent) := by
  exact DedekindCutCauchyBoundaryTasteGate_single_carrier_alignment

def taste_gate : ChapterTasteGate DedekindCutCauchyBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.DedekindCutCauchyBoundaryUp.taste_gate

end TasteGate

end BEDC.Derived.DedekindCutCauchyBoundaryUp
