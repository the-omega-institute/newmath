import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteObservationLockUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteObservationLockUp : Type where
  | mk : (A D Z Q W R B U H C P N : BHist) → FiniteObservationLockUp

def finiteObservationLockEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteObservationLockEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteObservationLockEncodeBHist h

def finiteObservationLockDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteObservationLockDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteObservationLockDecodeBHist tail)

private theorem finiteObservationLockDecode_encode_bhist :
    ∀ h : BHist, finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

theorem FiniteObservationLockTasteGate_single_carrier_alignment_mk_congr
    {A A' D D' Z Z' Q Q' W W' R R' B B' U U' H H' C C' P P' N N' : BHist}
    (hA : A' = A) (hD : D' = D) (hZ : Z' = Z) (hQ : Q' = Q)
    (hW : W' = W) (hR : R' = R) (hB : B' = B) (hU : U' = U)
    (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    FiniteObservationLockUp.mk A' D' Z' Q' W' R' B' U' H' C' P' N' =
      FiniteObservationLockUp.mk A D Z Q W R B U H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hA
  cases hD
  cases hZ
  cases hQ
  cases hW
  cases hR
  cases hB
  cases hU
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def finiteObservationLockToEventFlow : FiniteObservationLockUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationLockUp.mk A D Z Q W R B U H C P N =>
      [[BMark.b0],
        finiteObservationLockEncodeBHist A,
        [BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist Z,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteObservationLockEncodeBHist U,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteObservationLockEncodeBHist N]

def finiteObservationLockFromEventFlow : EventFlow → Option FiniteObservationLockUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | A :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | D :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | Z :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | Q :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | W :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | R :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | B :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | U :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | H :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match rest18 with
                                                                              | [] =>
                                                                                  none
                                                                              | C ::
                                                                                  rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match rest20 with
                                                                                      | [] =>
                                                                                          none
                                                                                      | P ::
                                                                                          rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match rest22 with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | N ::
                                                                                                  rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (FiniteObservationLockUp.mk
                                                                                                          (finiteObservationLockDecodeBHist A)
                                                                                                          (finiteObservationLockDecodeBHist D)
                                                                                                          (finiteObservationLockDecodeBHist Z)
                                                                                                          (finiteObservationLockDecodeBHist Q)
                                                                                                          (finiteObservationLockDecodeBHist W)
                                                                                                          (finiteObservationLockDecodeBHist R)
                                                                                                          (finiteObservationLockDecodeBHist B)
                                                                                                          (finiteObservationLockDecodeBHist U)
                                                                                                          (finiteObservationLockDecodeBHist H)
                                                                                                          (finiteObservationLockDecodeBHist C)
                                                                                                          (finiteObservationLockDecodeBHist P)
                                                                                                          (finiteObservationLockDecodeBHist N))
                                                                                                  | _ ::
                                                                                                      _ =>
                                                                                                      none

def finiteObservationLockFields : FiniteObservationLockUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteObservationLockUp.mk A D Z Q W R B U H C P N =>
      [A, D, Z, Q, W, R, B, U, H, C, P, N]

private theorem finiteObservationLock_round_trip :
    ∀ x : FiniteObservationLockUp,
      finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A D Z Q W R B U H C P N =>
      show
        some
          (FiniteObservationLockUp.mk
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist A))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist D))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist Z))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist Q))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist W))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist R))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist B))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist U))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist H))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist C))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist P))
            (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist N))) =
          some (FiniteObservationLockUp.mk A D Z Q W R B U H C P N)
      have hA := finiteObservationLockDecode_encode_bhist A
      have hD := finiteObservationLockDecode_encode_bhist D
      have hZ := finiteObservationLockDecode_encode_bhist Z
      have hQ := finiteObservationLockDecode_encode_bhist Q
      have hW := finiteObservationLockDecode_encode_bhist W
      have hR := finiteObservationLockDecode_encode_bhist R
      have hB := finiteObservationLockDecode_encode_bhist B
      have hU := finiteObservationLockDecode_encode_bhist U
      have hH := finiteObservationLockDecode_encode_bhist H
      have hC := finiteObservationLockDecode_encode_bhist C
      have hP := finiteObservationLockDecode_encode_bhist P
      have hN := finiteObservationLockDecode_encode_bhist N
      exact congrArg some
        (FiniteObservationLockTasteGate_single_carrier_alignment_mk_congr
          hA hD hZ hQ hW hR hB hU hH hC hP hN)

private theorem finiteObservationLockToEventFlow_injective :
    ∀ x y : FiniteObservationLockUp,
      finiteObservationLockToEventFlow x = finiteObservationLockToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hxy
  have optionEq : some x = some y := by
    calc
      some x = finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow x) :=
        (finiteObservationLock_round_trip x).symm
      _ = finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow y) :=
        congrArg finiteObservationLockFromEventFlow hxy
      _ = some y := finiteObservationLock_round_trip y
  exact Option.some.inj optionEq

instance finiteObservationLockBHistCarrier : BHistCarrier FiniteObservationLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteObservationLockToEventFlow
  fromEventFlow := finiteObservationLockFromEventFlow

instance finiteObservationLockChapterTasteGate : ChapterTasteGate FiniteObservationLockUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := finiteObservationLock_round_trip
  layer_separation := by
    intro x y hneq hflow
    exact hneq (finiteObservationLockToEventFlow_injective x y hflow)

def taste_gate : ChapterTasteGate FiniteObservationLockUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteObservationLockChapterTasteGate

instance finiteObservationLockFieldFaithful : FieldFaithful FiniteObservationLockUp where
  fields := finiteObservationLockFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk A₁ D₁ Z₁ Q₁ W₁ R₁ B₁ U₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk A₂ D₂ Z₂ Q₂ W₂ R₂ B₂ U₂ H₂ C₂ P₂ N₂ =>
            injection h with hA tD
            injection tD with hD tZ
            injection tZ with hZ tQ
            injection tQ with hQ tW
            injection tW with hW tR
            injection tR with hR tB
            injection tB with hB tU
            injection tU with hU tH
            injection tH with hH tC
            injection tC with hC tP
            injection tP with hP tN
            injection tN with hN _
            cases hA
            cases hD
            cases hZ
            cases hQ
            cases hW
            cases hR
            cases hB
            cases hU
            cases hH
            cases hC
            cases hP
            cases hN
            rfl

instance finiteObservationLockNontrivial : Nontrivial FiniteObservationLockUp where
  witness_pair :=
    ⟨FiniteObservationLockUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteObservationLockUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        injection h with hA
        cases hA⟩

theorem FiniteObservationLockTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist h) = h) ∧
      (∀ x : FiniteObservationLockUp,
        finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow x) = some x) ∧
        (∀ x y : FiniteObservationLockUp,
          finiteObservationLockToEventFlow x = finiteObservationLockToEventFlow y → x = y) ∧
          finiteObservationLockEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : FiniteObservationLockUp,
              finiteObservationLockFields x = finiteObservationLockFields y → x = y) ∧
              (∃ x y : FiniteObservationLockUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  have decodePublic :
      ∀ h : BHist, finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  have roundTripPublic :
      ∀ x : FiniteObservationLockUp,
        finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow x) = some x := by
    intro x
    cases x with
    | mk A D Z Q W R B U H C P N =>
        show
          some
            (FiniteObservationLockUp.mk
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist A))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist D))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist Z))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist Q))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist W))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist R))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist B))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist U))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist H))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist C))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist P))
              (finiteObservationLockDecodeBHist (finiteObservationLockEncodeBHist N))) =
            some (FiniteObservationLockUp.mk A D Z Q W R B U H C P N)
        have hA := decodePublic A
        have hD := decodePublic D
        have hZ := decodePublic Z
        have hQ := decodePublic Q
        have hW := decodePublic W
        have hR := decodePublic R
        have hB := decodePublic B
        have hU := decodePublic U
        have hH := decodePublic H
        have hC := decodePublic C
        have hP := decodePublic P
        have hN := decodePublic N
        exact congrArg some
          (FiniteObservationLockTasteGate_single_carrier_alignment_mk_congr
            hA hD hZ hQ hW hR hB hU hH hC hP hN)
  constructor
  · exact decodePublic
  · constructor
    · exact roundTripPublic
    · constructor
      · intro x y hxy
        have optionEq : some x = some y := by
          calc
            some x = finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow x) :=
              (roundTripPublic x).symm
            _ = finiteObservationLockFromEventFlow (finiteObservationLockToEventFlow y) :=
              congrArg finiteObservationLockFromEventFlow hxy
            _ = some y := roundTripPublic y
        exact Option.some.inj optionEq
      · constructor
        · rfl
        · constructor
          · intro x y h
            cases x with
            | mk A₁ D₁ Z₁ Q₁ W₁ R₁ B₁ U₁ H₁ C₁ P₁ N₁ =>
                cases y with
                | mk A₂ D₂ Z₂ Q₂ W₂ R₂ B₂ U₂ H₂ C₂ P₂ N₂ =>
                    injection h with hA tD
                    injection tD with hD tZ
                    injection tZ with hZ tQ
                    injection tQ with hQ tW
                    injection tW with hW tR
                    injection tR with hR tB
                    injection tB with hB tU
                    injection tU with hU tH
                    injection tH with hH tC
                    injection tC with hC tP
                    injection tP with hP tN
                    injection tN with hN _
                    cases hA
                    cases hD
                    cases hZ
                    cases hQ
                    cases hW
                    cases hR
                    cases hB
                    cases hU
                    cases hH
                    cases hC
                    cases hP
                    cases hN
                    rfl
          · exact
              ⟨FiniteObservationLockUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                FiniteObservationLockUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty,
                by
                  intro h
                  injection h with hA
                  cases hA⟩

end BEDC.Derived.FiniteObservationLockUp
