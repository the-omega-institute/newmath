import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GroundLoopBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GroundLoopBoundaryUp : Type where
  | mk :
      (marks sameness cross reflection history contRoutes provenance nameCert : BHist) →
      GroundLoopBoundaryUp
  deriving DecidableEq

def groundLoopBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: groundLoopBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: groundLoopBoundaryEncodeBHist h

def groundLoopBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (groundLoopBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (groundLoopBoundaryDecodeBHist tail)

private theorem groundLoopBoundaryDecode_encode_bhist :
    ∀ h : BHist, groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem groundLoopBoundary_mk_congr
    {marks marks' sameness sameness' cross cross' reflection reflection' history history'
      contRoutes contRoutes' provenance provenance' nameCert nameCert' : BHist}
    (hMarks : marks' = marks)
    (hSameness : sameness' = sameness)
    (hCross : cross' = cross)
    (hReflection : reflection' = reflection)
    (hHistory : history' = history)
    (hContRoutes : contRoutes' = contRoutes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    GroundLoopBoundaryUp.mk marks' sameness' cross' reflection' history' contRoutes'
        provenance' nameCert' =
      GroundLoopBoundaryUp.mk marks sameness cross reflection history contRoutes provenance
        nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMarks
  cases hSameness
  cases hCross
  cases hReflection
  cases hHistory
  cases hContRoutes
  cases hProvenance
  cases hNameCert
  rfl

def groundLoopBoundaryToEventFlow : GroundLoopBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | GroundLoopBoundaryUp.mk marks sameness cross reflection history contRoutes provenance
      nameCert =>
      [[BMark.b0],
        groundLoopBoundaryEncodeBHist marks,
        [BMark.b1, BMark.b0],
        groundLoopBoundaryEncodeBHist sameness,
        [BMark.b1, BMark.b1, BMark.b0],
        groundLoopBoundaryEncodeBHist cross,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundLoopBoundaryEncodeBHist reflection,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundLoopBoundaryEncodeBHist history,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundLoopBoundaryEncodeBHist contRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        groundLoopBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        groundLoopBoundaryEncodeBHist nameCert]

def groundLoopBoundaryFromEventFlow : EventFlow → Option GroundLoopBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | marks :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | sameness :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | cross :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | reflection :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | history :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | contRoutes :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (GroundLoopBoundaryUp.mk
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            marks)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            sameness)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            cross)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            reflection)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            history)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            contRoutes)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            provenance)
                                                                          (groundLoopBoundaryDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem groundLoopBoundary_round_trip :
    ∀ x : GroundLoopBoundaryUp,
      groundLoopBoundaryFromEventFlow (groundLoopBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk marks sameness cross reflection history contRoutes provenance nameCert =>
      change
        some
          (GroundLoopBoundaryUp.mk
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist marks))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist sameness))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist cross))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist reflection))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist history))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist contRoutes))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist provenance))
            (groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist nameCert))) =
          some
            (GroundLoopBoundaryUp.mk marks sameness cross reflection history contRoutes
              provenance nameCert)
      exact
        congrArg some
          (groundLoopBoundary_mk_congr
            (groundLoopBoundaryDecode_encode_bhist marks)
            (groundLoopBoundaryDecode_encode_bhist sameness)
            (groundLoopBoundaryDecode_encode_bhist cross)
            (groundLoopBoundaryDecode_encode_bhist reflection)
            (groundLoopBoundaryDecode_encode_bhist history)
            (groundLoopBoundaryDecode_encode_bhist contRoutes)
            (groundLoopBoundaryDecode_encode_bhist provenance)
            (groundLoopBoundaryDecode_encode_bhist nameCert))

private theorem groundLoopBoundaryToEventFlow_injective {x y : GroundLoopBoundaryUp} :
    groundLoopBoundaryToEventFlow x = groundLoopBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      groundLoopBoundaryFromEventFlow (groundLoopBoundaryToEventFlow x) =
        groundLoopBoundaryFromEventFlow (groundLoopBoundaryToEventFlow y) :=
    congrArg groundLoopBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (groundLoopBoundary_round_trip x).symm
      (Eq.trans hread (groundLoopBoundary_round_trip y)))

instance groundLoopBoundaryBHistCarrier : BHistCarrier GroundLoopBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := groundLoopBoundaryToEventFlow
  fromEventFlow := groundLoopBoundaryFromEventFlow

instance groundLoopBoundaryChapterTasteGate : ChapterTasteGate GroundLoopBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change groundLoopBoundaryFromEventFlow (groundLoopBoundaryToEventFlow x) = some x
    exact groundLoopBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (groundLoopBoundaryToEventFlow_injective heq)

theorem GroundLoopBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, groundLoopBoundaryDecodeBHist (groundLoopBoundaryEncodeBHist h) = h) ∧
      (∀ x : GroundLoopBoundaryUp,
        groundLoopBoundaryFromEventFlow (groundLoopBoundaryToEventFlow x) = some x) ∧
        (∀ x y : GroundLoopBoundaryUp,
          groundLoopBoundaryToEventFlow x = groundLoopBoundaryToEventFlow y → x = y) ∧
          (∀ (x : GroundLoopBoundaryUp) w m,
            List.Mem w (groundLoopBoundaryToEventFlow x) → List.Mem m w →
              m = BMark.b0 ∨ m = BMark.b1) ∧
            groundLoopBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact groundLoopBoundaryDecode_encode_bhist
  · constructor
    · exact groundLoopBoundary_round_trip
    · constructor
      · intro x y heq
        exact groundLoopBoundaryToEventFlow_injective heq
      · constructor
        · intro x w m hw hm
          cases m with
          | b0 =>
              exact Or.inl rfl
          | b1 =>
              exact Or.inr rfl
        · rfl

end BEDC.Derived.GroundLoopBoundaryUp
