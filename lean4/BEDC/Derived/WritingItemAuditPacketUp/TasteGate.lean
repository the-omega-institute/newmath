import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.WritingItemAuditPacketUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive WritingItemAuditPacketUp : Type where
  | mk : (K C R L T F G Q H A P N : BHist) → WritingItemAuditPacketUp
  deriving DecidableEq

def writingItemAuditPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: writingItemAuditPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: writingItemAuditPacketEncodeBHist h

def writingItemAuditPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (writingItemAuditPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (writingItemAuditPacketDecodeBHist tail)

private theorem writingItemAuditPacketDecode_encode_bhist :
    ∀ h : BHist,
      writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem writingItemAuditPacket_mk_congr
    {K K' C C' R R' L L' T T' F F' G G' Q Q' H H' A A' P P' N N' : BHist}
    (hK : K' = K) (hC : C' = C) (hR : R' = R) (hL : L' = L) (hT : T' = T)
    (hF : F' = F) (hG : G' = G) (hQ : Q' = Q) (hH : H' = H) (hA : A' = A)
    (hP : P' = P) (hN : N' = N) :
    WritingItemAuditPacketUp.mk K' C' R' L' T' F' G' Q' H' A' P' N' =
      WritingItemAuditPacketUp.mk K C R L T F G Q H A P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hK
  cases hC
  cases hR
  cases hL
  cases hT
  cases hF
  cases hG
  cases hQ
  cases hH
  cases hA
  cases hP
  cases hN
  rfl

def writingItemAuditPacketToEventFlow : WritingItemAuditPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | WritingItemAuditPacketUp.mk K C R L T F G Q H A P N =>
      [[BMark.b0],
        writingItemAuditPacketEncodeBHist K,
        [BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        writingItemAuditPacketEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        writingItemAuditPacketEncodeBHist N]

def writingItemAuditPacketFromEventFlow : EventFlow → Option WritingItemAuditPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | K :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | C :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | T :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | F :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | G :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | Q :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | A :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | P :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | N :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (WritingItemAuditPacketUp.mk
                                                                                                          (writingItemAuditPacketDecodeBHist K)
                                                                                                          (writingItemAuditPacketDecodeBHist C)
                                                                                                          (writingItemAuditPacketDecodeBHist R)
                                                                                                          (writingItemAuditPacketDecodeBHist L)
                                                                                                          (writingItemAuditPacketDecodeBHist T)
                                                                                                          (writingItemAuditPacketDecodeBHist F)
                                                                                                          (writingItemAuditPacketDecodeBHist G)
                                                                                                          (writingItemAuditPacketDecodeBHist Q)
                                                                                                          (writingItemAuditPacketDecodeBHist H)
                                                                                                          (writingItemAuditPacketDecodeBHist A)
                                                                                                          (writingItemAuditPacketDecodeBHist P)
                                                                                                          (writingItemAuditPacketDecodeBHist N))
                                                                                                  | _ :: _ => none

private theorem writingItemAuditPacket_round_trip :
    ∀ x : WritingItemAuditPacketUp,
      writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K C R L T F G Q H A P N =>
      change
        some
          (WritingItemAuditPacketUp.mk
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist K))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist C))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist R))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist L))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist T))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist F))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist G))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist Q))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist H))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist A))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist P))
            (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist N))) =
          some (WritingItemAuditPacketUp.mk K C R L T F G Q H A P N)
      exact
        congrArg some
          (writingItemAuditPacket_mk_congr
            (writingItemAuditPacketDecode_encode_bhist K)
            (writingItemAuditPacketDecode_encode_bhist C)
            (writingItemAuditPacketDecode_encode_bhist R)
            (writingItemAuditPacketDecode_encode_bhist L)
            (writingItemAuditPacketDecode_encode_bhist T)
            (writingItemAuditPacketDecode_encode_bhist F)
            (writingItemAuditPacketDecode_encode_bhist G)
            (writingItemAuditPacketDecode_encode_bhist Q)
            (writingItemAuditPacketDecode_encode_bhist H)
            (writingItemAuditPacketDecode_encode_bhist A)
            (writingItemAuditPacketDecode_encode_bhist P)
            (writingItemAuditPacketDecode_encode_bhist N))

private theorem writingItemAuditPacketToEventFlow_injective
    {x y : WritingItemAuditPacketUp} :
    writingItemAuditPacketToEventFlow x = writingItemAuditPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) =
        writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow y) :=
    congrArg writingItemAuditPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (writingItemAuditPacket_round_trip x).symm
      (Eq.trans hread (writingItemAuditPacket_round_trip y)))

instance writingItemAuditPacketBHistCarrier : BHistCarrier WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := writingItemAuditPacketToEventFlow
  fromEventFlow := writingItemAuditPacketFromEventFlow

instance writingItemAuditPacketChapterTasteGate : ChapterTasteGate WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) = some x
    exact writingItemAuditPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (writingItemAuditPacketToEventFlow_injective heq)

instance writingItemAuditPacketFieldFaithful : FieldFaithful WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | WritingItemAuditPacketUp.mk K C R L T F G Q H A P N =>
        [K, C, R, L, T, F, G, Q, H, A, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk K₁ C₁ R₁ L₁ T₁ F₁ G₁ Q₁ H₁ A₁ P₁ N₁ =>
        cases y with
        | mk K₂ C₂ R₂ L₂ T₂ F₂ G₂ Q₂ H₂ A₂ P₂ N₂ =>
            cases h
            rfl

instance writingItemAuditPacketNontrivial : Nontrivial WritingItemAuditPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨WritingItemAuditPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      WritingItemAuditPacketUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate WritingItemAuditPacketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  writingItemAuditPacketChapterTasteGate

theorem WritingItemAuditPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist, writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist h) = h) ∧
      (∀ x : WritingItemAuditPacketUp,
        writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) = some x) ∧
        (∀ x y : WritingItemAuditPacketUp,
          writingItemAuditPacketToEventFlow x = writingItemAuditPacketToEventFlow y → x = y) ∧
          writingItemAuditPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro x
      cases x with
      | mk K C R L T F G Q H A P N =>
          change
            some
              (WritingItemAuditPacketUp.mk
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist K))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist C))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist R))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist L))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist T))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist F))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist G))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist Q))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist H))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist A))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist P))
                (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist N))) =
              some (WritingItemAuditPacketUp.mk K C R L T F G Q H A P N)
          have hK :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist K) = K := by
            induction K with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hC :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist C) = C := by
            induction C with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hR :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist R) = R := by
            induction R with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hL :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist L) = L := by
            induction L with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hT :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist T) = T := by
            induction T with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hF :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist F) = F := by
            induction F with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hG :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist G) = G := by
            induction G with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hQ :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist Q) = Q := by
            induction Q with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hH :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist H) = H := by
            induction H with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hA :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist A) = A := by
            induction A with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hP :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist P) = P := by
            induction P with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          have hN :
              writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist N) = N := by
            induction N with
            | Empty => rfl
            | e0 h ih => exact congrArg BHist.e0 ih
            | e1 h ih => exact congrArg BHist.e1 ih
          exact
            congrArg some
              (writingItemAuditPacket_mk_congr hK hC hR hL hT hF hG hQ hH hA hP hN)
    · constructor
      · intro x y heq
        have hread :
            writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) =
              writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow y) :=
          congrArg writingItemAuditPacketFromEventFlow heq
        have hx :
            writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow x) =
              some x := by
          cases x with
          | mk K C R L T F G Q H A P N =>
              change
                some
                  (WritingItemAuditPacketUp.mk
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist K))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist C))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist R))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist L))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist T))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist F))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist G))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist Q))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist H))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist A))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist P))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist N))) =
                  some (WritingItemAuditPacketUp.mk K C R L T F G Q H A P N)
              exact
                congrArg some
                  (writingItemAuditPacket_mk_congr
                    (writingItemAuditPacketDecode_encode_bhist K)
                    (writingItemAuditPacketDecode_encode_bhist C)
                    (writingItemAuditPacketDecode_encode_bhist R)
                    (writingItemAuditPacketDecode_encode_bhist L)
                    (writingItemAuditPacketDecode_encode_bhist T)
                    (writingItemAuditPacketDecode_encode_bhist F)
                    (writingItemAuditPacketDecode_encode_bhist G)
                    (writingItemAuditPacketDecode_encode_bhist Q)
                    (writingItemAuditPacketDecode_encode_bhist H)
                    (writingItemAuditPacketDecode_encode_bhist A)
                    (writingItemAuditPacketDecode_encode_bhist P)
                    (writingItemAuditPacketDecode_encode_bhist N))
        have hy :
            writingItemAuditPacketFromEventFlow (writingItemAuditPacketToEventFlow y) =
              some y := by
          cases y with
          | mk K C R L T F G Q H A P N =>
              change
                some
                  (WritingItemAuditPacketUp.mk
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist K))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist C))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist R))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist L))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist T))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist F))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist G))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist Q))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist H))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist A))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist P))
                    (writingItemAuditPacketDecodeBHist (writingItemAuditPacketEncodeBHist N))) =
                  some (WritingItemAuditPacketUp.mk K C R L T F G Q H A P N)
              exact
                congrArg some
                  (writingItemAuditPacket_mk_congr
                    (writingItemAuditPacketDecode_encode_bhist K)
                    (writingItemAuditPacketDecode_encode_bhist C)
                    (writingItemAuditPacketDecode_encode_bhist R)
                    (writingItemAuditPacketDecode_encode_bhist L)
                    (writingItemAuditPacketDecode_encode_bhist T)
                    (writingItemAuditPacketDecode_encode_bhist F)
                    (writingItemAuditPacketDecode_encode_bhist G)
                    (writingItemAuditPacketDecode_encode_bhist Q)
                    (writingItemAuditPacketDecode_encode_bhist H)
                    (writingItemAuditPacketDecode_encode_bhist A)
                    (writingItemAuditPacketDecode_encode_bhist P)
                    (writingItemAuditPacketDecode_encode_bhist N))
        exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
      · rfl

end BEDC.Derived.WritingItemAuditPacketUp
