import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ResearchProgrammeRouteUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ResearchProgrammeRouteUp : Type where
  | mk : (P S K V E O X H C G N : BHist) → ResearchProgrammeRouteUp
  deriving DecidableEq

def researchProgrammeRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: researchProgrammeRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: researchProgrammeRouteEncodeBHist h

def researchProgrammeRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (researchProgrammeRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (researchProgrammeRouteDecodeBHist tail)

private theorem researchProgrammeRouteDecode_encode_bhist :
    ∀ h : BHist,
      researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem researchProgrammeRoute_mk_congr
    {P P' S S' K K' V V' E E' O O' X X' H H' C C' G G' N N' : BHist}
    (hP : P' = P) (hS : S' = S) (hK : K' = K) (hV : V' = V) (hE : E' = E)
    (hO : O' = O) (hX : X' = X) (hH : H' = H) (hC : C' = C) (hG : G' = G)
    (hN : N' = N) :
    ResearchProgrammeRouteUp.mk P' S' K' V' E' O' X' H' C' G' N' =
      ResearchProgrammeRouteUp.mk P S K V E O X H C G N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hP
  cases hS
  cases hK
  cases hV
  cases hE
  cases hO
  cases hX
  cases hH
  cases hC
  cases hG
  cases hN
  rfl

def researchProgrammeRouteToEventFlow : ResearchProgrammeRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ResearchProgrammeRouteUp.mk P S K V E O X H C G N =>
      [[BMark.b0],
        researchProgrammeRouteEncodeBHist P,
        [BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist X,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        researchProgrammeRouteEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        researchProgrammeRouteEncodeBHist N]

def researchProgrammeRouteFromEventFlow : EventFlow → Option ResearchProgrammeRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | P :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | S :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | K :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | V :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | E :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | O :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | X :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | H :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | C :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | G :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | N :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (ResearchProgrammeRouteUp.mk
                                                                                                  (researchProgrammeRouteDecodeBHist P)
                                                                                                  (researchProgrammeRouteDecodeBHist S)
                                                                                                  (researchProgrammeRouteDecodeBHist K)
                                                                                                  (researchProgrammeRouteDecodeBHist V)
                                                                                                  (researchProgrammeRouteDecodeBHist E)
                                                                                                  (researchProgrammeRouteDecodeBHist O)
                                                                                                  (researchProgrammeRouteDecodeBHist X)
                                                                                                  (researchProgrammeRouteDecodeBHist H)
                                                                                                  (researchProgrammeRouteDecodeBHist C)
                                                                                                  (researchProgrammeRouteDecodeBHist G)
                                                                                                  (researchProgrammeRouteDecodeBHist N))
                                                                                          | _ :: _ => none

private theorem researchProgrammeRoute_round_trip :
    ∀ x : ResearchProgrammeRouteUp,
      researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk P S K V E O X H C G N =>
      change
        some
          (ResearchProgrammeRouteUp.mk
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist P))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist S))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist K))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist V))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist E))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist O))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist X))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist H))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist C))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist G))
            (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist N))) =
          some (ResearchProgrammeRouteUp.mk P S K V E O X H C G N)
      exact
        congrArg some
          (researchProgrammeRoute_mk_congr
            (researchProgrammeRouteDecode_encode_bhist P)
            (researchProgrammeRouteDecode_encode_bhist S)
            (researchProgrammeRouteDecode_encode_bhist K)
            (researchProgrammeRouteDecode_encode_bhist V)
            (researchProgrammeRouteDecode_encode_bhist E)
            (researchProgrammeRouteDecode_encode_bhist O)
            (researchProgrammeRouteDecode_encode_bhist X)
            (researchProgrammeRouteDecode_encode_bhist H)
            (researchProgrammeRouteDecode_encode_bhist C)
            (researchProgrammeRouteDecode_encode_bhist G)
            (researchProgrammeRouteDecode_encode_bhist N))

private theorem researchProgrammeRouteToEventFlow_injective
    {x y : ResearchProgrammeRouteUp} :
    researchProgrammeRouteToEventFlow x = researchProgrammeRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow x) =
        researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow y) :=
    congrArg researchProgrammeRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (researchProgrammeRoute_round_trip x).symm
      (Eq.trans hread (researchProgrammeRoute_round_trip y)))

def researchProgrammeRouteFields : ResearchProgrammeRouteUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ResearchProgrammeRouteUp.mk P S K V E O X H C G N => [P, S, K, V, E, O, X, H, C, G, N]

private theorem researchProgrammeRoute_field_faithful :
    ∀ x y : ResearchProgrammeRouteUp,
      researchProgrammeRouteFields x = researchProgrammeRouteFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk P₁ S₁ K₁ V₁ E₁ O₁ X₁ H₁ C₁ G₁ N₁ =>
      cases y with
      | mk P₂ S₂ K₂ V₂ E₂ O₂ X₂ H₂ C₂ G₂ N₂ =>
          injection h with hP t1
          injection t1 with hS t2
          injection t2 with hK t3
          injection t3 with hV t4
          injection t4 with hE t5
          injection t5 with hO t6
          injection t6 with hX t7
          injection t7 with hH t8
          injection t8 with hC t9
          injection t9 with hG t10
          injection t10 with hN _
          cases hP
          cases hS
          cases hK
          cases hV
          cases hE
          cases hO
          cases hX
          cases hH
          cases hC
          cases hG
          cases hN
          rfl

instance researchProgrammeRouteBHistCarrier : BHistCarrier ResearchProgrammeRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := researchProgrammeRouteToEventFlow
  fromEventFlow := researchProgrammeRouteFromEventFlow

instance researchProgrammeRouteChapterTasteGate : ChapterTasteGate ResearchProgrammeRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow x) = some x
    exact researchProgrammeRoute_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (researchProgrammeRouteToEventFlow_injective heq)

instance researchProgrammeRouteFieldFaithful : FieldFaithful ResearchProgrammeRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := researchProgrammeRouteFields
  field_faithful := researchProgrammeRoute_field_faithful

instance researchProgrammeRouteNontrivial : Nontrivial ResearchProgrammeRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ResearchProgrammeRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ResearchProgrammeRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ResearchProgrammeRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  researchProgrammeRouteChapterTasteGate

def taste_gate_witness : FieldFaithful ResearchProgrammeRouteUp :=
  -- BEDC touchpoint anchor: BHist BMark
  researchProgrammeRouteFieldFaithful

theorem ResearchProgrammeRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist, researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist h) = h) ∧
      (∀ x : ResearchProgrammeRouteUp,
        researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow x) = some x) ∧
        (∀ x y : ResearchProgrammeRouteUp,
          researchProgrammeRouteToEventFlow x = researchProgrammeRouteToEventFlow y → x = y) ∧
          researchProgrammeRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  have hdecode :
      ∀ h : BHist, researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  have hround :
      ∀ x : ResearchProgrammeRouteUp,
        researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow x) = some x := by
    intro x
    cases x with
    | mk P S K V E O X H C G N =>
        change
          some
            (ResearchProgrammeRouteUp.mk
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist P))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist S))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist K))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist V))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist E))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist O))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist X))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist H))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist C))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist G))
              (researchProgrammeRouteDecodeBHist (researchProgrammeRouteEncodeBHist N))) =
            some (ResearchProgrammeRouteUp.mk P S K V E O X H C G N)
        rw [hdecode P, hdecode S, hdecode K, hdecode V, hdecode E, hdecode O,
          hdecode X, hdecode H, hdecode C, hdecode G, hdecode N]
  have hinj :
      ∀ x y : ResearchProgrammeRouteUp,
        researchProgrammeRouteToEventFlow x = researchProgrammeRouteToEventFlow y → x = y := by
    intro x y heq
    have hread :
        researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow x) =
          researchProgrammeRouteFromEventFlow (researchProgrammeRouteToEventFlow y) :=
      congrArg researchProgrammeRouteFromEventFlow heq
    exact Option.some.inj
      (Eq.trans (hround x).symm (Eq.trans hread (hround y)))
  exact ⟨hdecode, hround, hinj, rfl⟩

end BEDC.Derived.ResearchProgrammeRouteUp
