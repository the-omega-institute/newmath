import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundCompilerRecognitionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundCompilerRecognitionUp : Type where
  | mk (I G A T V L H C P N : BHist) : GroundCompilerRecognitionUp
  deriving DecidableEq

def groundCompilerRecognitionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundCompilerRecognitionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundCompilerRecognitionEncodeBHist h

def groundCompilerRecognitionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundCompilerRecognitionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundCompilerRecognitionDecodeBHist tail)

private theorem groundCompilerRecognitionDecode_encode_bhist :
    ∀ h : BHist, groundCompilerRecognitionDecodeBHist
      (groundCompilerRecognitionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem groundCompilerRecognition_mk_congr
    {I I' G G' A A' T T' V V' L L' H H' C C' P P' N N' : BHist}
    (hI : I' = I) (hG : G' = G) (hA : A' = A) (hT : T' = T)
    (hV : V' = V) (hL : L' = L) (hH : H' = H) (hC : C' = C)
    (hP : P' = P) (hN : N' = N) :
    GroundCompilerRecognitionUp.mk I' G' A' T' V' L' H' C' P' N' =
      GroundCompilerRecognitionUp.mk I G A T V L H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hI
  cases hG
  cases hA
  cases hT
  cases hV
  cases hL
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def groundCompilerRecognitionToEventFlow : GroundCompilerRecognitionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognitionUp.mk I G A T V L H C P N =>
      [[BMark.b0],
        groundCompilerRecognitionEncodeBHist I,
        [BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundCompilerRecognitionEncodeBHist N]

def groundCompilerRecognitionFromEventFlow :
    EventFlow → Option GroundCompilerRecognitionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | I :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | G :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | T :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | V :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | L :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | H :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | C :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | P :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | N :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (GroundCompilerRecognitionUp.mk
                                                                                          (groundCompilerRecognitionDecodeBHist I)
                                                                                          (groundCompilerRecognitionDecodeBHist G)
                                                                                          (groundCompilerRecognitionDecodeBHist A)
                                                                                          (groundCompilerRecognitionDecodeBHist T)
                                                                                          (groundCompilerRecognitionDecodeBHist V)
                                                                                          (groundCompilerRecognitionDecodeBHist L)
                                                                                          (groundCompilerRecognitionDecodeBHist H)
                                                                                          (groundCompilerRecognitionDecodeBHist C)
                                                                                          (groundCompilerRecognitionDecodeBHist P)
                                                                                          (groundCompilerRecognitionDecodeBHist N))
                                                                                  | _ :: _ => none

private theorem groundCompilerRecognition_round_trip :
    ∀ x : GroundCompilerRecognitionUp,
      groundCompilerRecognitionFromEventFlow
        (groundCompilerRecognitionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I G A T V L H C P N =>
      change
        some
          (GroundCompilerRecognitionUp.mk
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist I))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist G))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist A))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist T))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist V))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist L))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist H))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist C))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist P))
            (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist N))) =
          some (GroundCompilerRecognitionUp.mk I G A T V L H C P N)
      exact
        congrArg some
          (groundCompilerRecognition_mk_congr
            (groundCompilerRecognitionDecode_encode_bhist I)
            (groundCompilerRecognitionDecode_encode_bhist G)
            (groundCompilerRecognitionDecode_encode_bhist A)
            (groundCompilerRecognitionDecode_encode_bhist T)
            (groundCompilerRecognitionDecode_encode_bhist V)
            (groundCompilerRecognitionDecode_encode_bhist L)
            (groundCompilerRecognitionDecode_encode_bhist H)
            (groundCompilerRecognitionDecode_encode_bhist C)
            (groundCompilerRecognitionDecode_encode_bhist P)
            (groundCompilerRecognitionDecode_encode_bhist N))

private theorem groundCompilerRecognitionToEventFlow_injective
    {x y : GroundCompilerRecognitionUp} :
    groundCompilerRecognitionToEventFlow x =
      groundCompilerRecognitionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundCompilerRecognitionFromEventFlow
          (groundCompilerRecognitionToEventFlow x) =
        groundCompilerRecognitionFromEventFlow
          (groundCompilerRecognitionToEventFlow y) :=
    congrArg groundCompilerRecognitionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundCompilerRecognition_round_trip x).symm
      (Eq.trans hread (groundCompilerRecognition_round_trip y)))

instance groundCompilerRecognitionBHistCarrier :
    BHistCarrier GroundCompilerRecognitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundCompilerRecognitionToEventFlow
  fromEventFlow := groundCompilerRecognitionFromEventFlow

instance groundCompilerRecognitionChapterTasteGate :
    ChapterTasteGate GroundCompilerRecognitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      groundCompilerRecognitionFromEventFlow
        (groundCompilerRecognitionToEventFlow x) = some x
    exact groundCompilerRecognition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundCompilerRecognitionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate GroundCompilerRecognitionUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact groundCompilerRecognitionChapterTasteGate

def groundCompilerRecognitionFields : GroundCompilerRecognitionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GroundCompilerRecognitionUp.mk I G A T V L H C P N =>
      [I, G, A, T, V, L, H, C, P, N]

instance groundCompilerRecognitionFieldFaithful :
    FieldFaithful GroundCompilerRecognitionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := groundCompilerRecognitionFields
  field_faithful := by
    intro x y hfields
    cases x with
    | mk I G A T V L H C P N =>
        cases y with
        | mk I' G' A' T' V' L' H' C' P' N' =>
            injection hfields with hI htail0
            injection htail0 with hG htail1
            injection htail1 with hA htail2
            injection htail2 with hT htail3
            injection htail3 with hV htail4
            injection htail4 with hL htail5
            injection htail5 with hH htail6
            injection htail6 with hC htail7
            injection htail7 with hP htail8
            injection htail8 with hN _hNil
            cases hI
            cases hG
            cases hA
            cases hT
            cases hV
            cases hL
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance groundCompilerRecognitionNontrivial :
    Nontrivial GroundCompilerRecognitionUp where
  witness_pair :=
    ⟨GroundCompilerRecognitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GroundCompilerRecognitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem GroundCompilerRecognitionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist h) = h) ∧
      (forall x : GroundCompilerRecognitionUp,
        groundCompilerRecognitionFromEventFlow (groundCompilerRecognitionToEventFlow x) =
          some x) ∧
        (forall x y : GroundCompilerRecognitionUp,
          groundCompilerRecognitionToEventFlow x = groundCompilerRecognitionToEventFlow y ->
            x = y) ∧
          groundCompilerRecognitionEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (forall x y : GroundCompilerRecognitionUp,
              groundCompilerRecognitionFields x = groundCompilerRecognitionFields y -> x = y) ∧
              (exists x y : GroundCompilerRecognitionUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk I G A T V L H C P N =>
          change
            some
              (GroundCompilerRecognitionUp.mk
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist I))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist G))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist A))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist T))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist V))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist L))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist H))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist C))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist P))
                (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist N))) =
              some (GroundCompilerRecognitionUp.mk I G A T V L H C P N)
          exact
            congrArg some
              (groundCompilerRecognition_mk_congr
                (groundCompilerRecognitionDecode_encode_bhist I)
                (groundCompilerRecognitionDecode_encode_bhist G)
                (groundCompilerRecognitionDecode_encode_bhist A)
                (groundCompilerRecognitionDecode_encode_bhist T)
                (groundCompilerRecognitionDecode_encode_bhist V)
                (groundCompilerRecognitionDecode_encode_bhist L)
                (groundCompilerRecognitionDecode_encode_bhist H)
                (groundCompilerRecognitionDecode_encode_bhist C)
                (groundCompilerRecognitionDecode_encode_bhist P)
                (groundCompilerRecognitionDecode_encode_bhist N))
    · constructor
      · intro x y heq
        have hx :
            groundCompilerRecognitionFromEventFlow
              (groundCompilerRecognitionToEventFlow x) = some x := by
          cases x with
          | mk I G A T V L H C P N =>
              change
                some
                  (GroundCompilerRecognitionUp.mk
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist I))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist G))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist A))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist T))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist V))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist L))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist H))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist C))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist P))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist N))) =
                  some (GroundCompilerRecognitionUp.mk I G A T V L H C P N)
              exact
                congrArg some
                  (groundCompilerRecognition_mk_congr
                    (groundCompilerRecognitionDecode_encode_bhist I)
                    (groundCompilerRecognitionDecode_encode_bhist G)
                    (groundCompilerRecognitionDecode_encode_bhist A)
                    (groundCompilerRecognitionDecode_encode_bhist T)
                    (groundCompilerRecognitionDecode_encode_bhist V)
                    (groundCompilerRecognitionDecode_encode_bhist L)
                    (groundCompilerRecognitionDecode_encode_bhist H)
                    (groundCompilerRecognitionDecode_encode_bhist C)
                    (groundCompilerRecognitionDecode_encode_bhist P)
                    (groundCompilerRecognitionDecode_encode_bhist N))
        have hy :
            groundCompilerRecognitionFromEventFlow
              (groundCompilerRecognitionToEventFlow y) = some y := by
          cases y with
          | mk I G A T V L H C P N =>
              change
                some
                  (GroundCompilerRecognitionUp.mk
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist I))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist G))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist A))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist T))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist V))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist L))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist H))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist C))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist P))
                    (groundCompilerRecognitionDecodeBHist (groundCompilerRecognitionEncodeBHist N))) =
                  some (GroundCompilerRecognitionUp.mk I G A T V L H C P N)
              exact
                congrArg some
                  (groundCompilerRecognition_mk_congr
                    (groundCompilerRecognitionDecode_encode_bhist I)
                    (groundCompilerRecognitionDecode_encode_bhist G)
                    (groundCompilerRecognitionDecode_encode_bhist A)
                    (groundCompilerRecognitionDecode_encode_bhist T)
                    (groundCompilerRecognitionDecode_encode_bhist V)
                    (groundCompilerRecognitionDecode_encode_bhist L)
                    (groundCompilerRecognitionDecode_encode_bhist H)
                    (groundCompilerRecognitionDecode_encode_bhist C)
                    (groundCompilerRecognitionDecode_encode_bhist P)
                    (groundCompilerRecognitionDecode_encode_bhist N))
        have hread :
            groundCompilerRecognitionFromEventFlow
                (groundCompilerRecognitionToEventFlow x) =
              groundCompilerRecognitionFromEventFlow
                (groundCompilerRecognitionToEventFlow y) :=
          congrArg groundCompilerRecognitionFromEventFlow heq
        exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
      · constructor
        · rfl
        · constructor
          · intro x y hfields
            cases x with
            | mk I G A T V L H C P N =>
                cases y with
                | mk I' G' A' T' V' L' H' C' P' N' =>
                    injection hfields with hI htail0
                    injection htail0 with hG htail1
                    injection htail1 with hA htail2
                    injection htail2 with hT htail3
                    injection htail3 with hV htail4
                    injection htail4 with hL htail5
                    injection htail5 with hH htail6
                    injection htail6 with hC htail7
                    injection htail7 with hP htail8
                    injection htail8 with hN _hNil
                    cases hI
                    cases hG
                    cases hA
                    cases hT
                    cases hV
                    cases hL
                    cases hH
                    cases hC
                    cases hP
                    cases hN
                    rfl
          · exact
              ⟨GroundCompilerRecognitionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
                GroundCompilerRecognitionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                by
                  intro h
                  cases h⟩

theorem GroundCompilerRecognitionCarrier_finite_trace_handoff_boundary :
    (∀ x : GroundCompilerRecognitionUp,
      ∃ I G A T V L H C P N : BHist,
        x = GroundCompilerRecognitionUp.mk I G A T V L H C P N ∧
          FieldFaithful.fields x = [I, G, A, T, V, L, H, C, P, N]) ∧
      (∀ I G A V L H C P N : BHist,
        BHistCarrier.toEventFlow
          (GroundCompilerRecognitionUp.mk I G A (BHist.e0 BHist.Empty) V L H C P N) ≠
        BHistCarrier.toEventFlow
          (GroundCompilerRecognitionUp.mk I G A BHist.Empty V L H C P N)) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    cases x with
    | mk I G A T V L H C P N =>
        exact ⟨I, G, A, T, V, L, H, C, P, N, rfl, rfl⟩
  · intro I G A V L H C P N heq
    change
      groundCompilerRecognitionToEventFlow
          (GroundCompilerRecognitionUp.mk I G A (BHist.e0 BHist.Empty) V L H C P N) =
        groundCompilerRecognitionToEventFlow
          (GroundCompilerRecognitionUp.mk I G A BHist.Empty V L H C P N) at heq
    injection heq with _ htail₁
    injection htail₁ with _ htail₂
    injection htail₂ with _ htail₃
    injection htail₃ with _ htail₄
    injection htail₄ with _ htail₅
    injection htail₅ with _ htail₆
    injection htail₆ with _ htail₇
    injection htail₇ with hrow _
    cases hrow

theorem GroundCompilerRecognitionNameCert_obligations
    (x : GroundCompilerRecognitionUp) :
    ∃ I G A T V L H C P N : BHist,
      x = GroundCompilerRecognitionUp.mk I G A T V L H C P N ∧
        hsame H H ∧ Cont C P (append C P) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I G A T V L H C P N =>
      exact ⟨I, G, A, T, V, L, H, C, P, N, rfl, hsame_refl H, rfl⟩

end BEDC.Derived.GroundCompilerRecognitionUp
