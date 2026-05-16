import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteMultiHistPacketUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteMultiHistPacketUp : Type where
  | mk :
      (histories ledgers comparisons routes boundary provenance nameCert : BHist) →
      FiniteMultiHistPacketUp
  deriving DecidableEq

def finiteMultiHistPacketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteMultiHistPacketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteMultiHistPacketEncodeBHist h

def finiteMultiHistPacketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteMultiHistPacketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteMultiHistPacketDecodeBHist tail)

private theorem finiteMultiHistPacket_decode_encode_bhist :
    ∀ h : BHist,
      finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteMultiHistPacketToEventFlow : FiniteMultiHistPacketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteMultiHistPacketUp.mk histories ledgers comparisons routes boundary provenance
      nameCert =>
      [[BMark.b0],
        finiteMultiHistPacketEncodeBHist histories,
        [BMark.b1, BMark.b0],
        finiteMultiHistPacketEncodeBHist ledgers,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteMultiHistPacketEncodeBHist comparisons,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMultiHistPacketEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMultiHistPacketEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMultiHistPacketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteMultiHistPacketEncodeBHist nameCert]

def finiteMultiHistPacketFromEventFlow : EventFlow → Option FiniteMultiHistPacketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | histories :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | ledgers :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | comparisons :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | boundary :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | nameCert :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (FiniteMultiHistPacketUp.mk
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    histories)
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    ledgers)
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    comparisons)
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    routes)
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    boundary)
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    provenance)
                                                                  (finiteMultiHistPacketDecodeBHist
                                                                    nameCert))
                                                          | _ :: _ => none

private theorem finiteMultiHistPacket_round_trip :
    ∀ x : FiniteMultiHistPacketUp,
      finiteMultiHistPacketFromEventFlow (finiteMultiHistPacketToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk histories ledgers comparisons routes boundary provenance nameCert =>
      change
        some
          (FiniteMultiHistPacketUp.mk
            (finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist histories))
            (finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist ledgers))
            (finiteMultiHistPacketDecodeBHist
              (finiteMultiHistPacketEncodeBHist comparisons))
            (finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist routes))
            (finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist boundary))
            (finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist provenance))
            (finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist nameCert))) =
          some
            (FiniteMultiHistPacketUp.mk histories ledgers comparisons routes boundary
              provenance nameCert)
      rw [finiteMultiHistPacket_decode_encode_bhist histories,
        finiteMultiHistPacket_decode_encode_bhist ledgers,
        finiteMultiHistPacket_decode_encode_bhist comparisons,
        finiteMultiHistPacket_decode_encode_bhist routes,
        finiteMultiHistPacket_decode_encode_bhist boundary,
        finiteMultiHistPacket_decode_encode_bhist provenance,
        finiteMultiHistPacket_decode_encode_bhist nameCert]

private theorem finiteMultiHistPacketToEventFlow_injective
    {x y : FiniteMultiHistPacketUp} :
    finiteMultiHistPacketToEventFlow x = finiteMultiHistPacketToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteMultiHistPacketFromEventFlow (finiteMultiHistPacketToEventFlow x) =
        finiteMultiHistPacketFromEventFlow (finiteMultiHistPacketToEventFlow y) :=
    congrArg finiteMultiHistPacketFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteMultiHistPacket_round_trip x).symm
      (Eq.trans hread (finiteMultiHistPacket_round_trip y)))

instance finiteMultiHistPacketBHistCarrier : BHistCarrier FiniteMultiHistPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteMultiHistPacketToEventFlow
  fromEventFlow := finiteMultiHistPacketFromEventFlow

instance finiteMultiHistPacketChapterTasteGate : ChapterTasteGate FiniteMultiHistPacketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteMultiHistPacketFromEventFlow (finiteMultiHistPacketToEventFlow x) = some x
    exact finiteMultiHistPacket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteMultiHistPacketToEventFlow_injective heq)

theorem FiniteMultiHistPacketUp_taste_gate_boundary :
    ChapterTasteGate FiniteMultiHistPacketUp ∧
      ∃ x : FiniteMultiHistPacketUp,
        x =
          FiniteMultiHistPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty ∧
          BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  let x : FiniteMultiHistPacketUp :=
    FiniteMultiHistPacketUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty
  constructor
  · exact finiteMultiHistPacketChapterTasteGate
  · exact ⟨x, rfl, ChapterTasteGate.round_trip x⟩

theorem FiniteMultiHistPacketTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteMultiHistPacketDecodeBHist (finiteMultiHistPacketEncodeBHist h) = h) ∧
      (∀ x : FiniteMultiHistPacketUp,
        finiteMultiHistPacketFromEventFlow (finiteMultiHistPacketToEventFlow x) = some x) ∧
        (∀ x : FiniteMultiHistPacketUp,
          finiteMultiHistPacketFromEventFlow (BHistCarrier.toEventFlow x) = some x) ∧
          (∀ x y : FiniteMultiHistPacketUp,
            finiteMultiHistPacketToEventFlow x = finiteMultiHistPacketToEventFlow y → x = y) ∧
            (∀ x y : FiniteMultiHistPacketUp,
              BHistCarrier.toEventFlow x = BHistCarrier.toEventFlow y → x = y) ∧
              (∀ (x : FiniteMultiHistPacketUp) w m,
                List.Mem w (BHistCarrier.toEventFlow x) → List.Mem m w →
                  m = BMark.b0 ∨ m = BMark.b1) ∧
                finiteMultiHistPacketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact finiteMultiHistPacket_decode_encode_bhist
  · constructor
    · exact finiteMultiHistPacket_round_trip
    · constructor
      · intro x
        change finiteMultiHistPacketFromEventFlow (finiteMultiHistPacketToEventFlow x) = some x
        exact finiteMultiHistPacket_round_trip x
      · constructor
        · intro x y heq
          exact finiteMultiHistPacketToEventFlow_injective heq
        · constructor
          · intro x y heq
            exact finiteMultiHistPacketToEventFlow_injective heq
          · constructor
            · intro x w m hw hm
              exact event_flow_conservativity (S := BHistCarrier.toEventFlow x) hw hm
            · rfl

theorem FiniteMultiHistPacketUp_hsame_transport
    {histories ledgers comparisons routes boundary provenance nameCert histories2 ledgers2
      comparisons2 routes2 boundary2 provenance2 nameCert2 : BHist} :
    Cont histories ledgers routes →
      hsame histories histories2 →
        hsame ledgers ledgers2 →
          hsame comparisons comparisons2 →
            hsame routes routes2 →
              hsame boundary boundary2 →
                hsame provenance provenance2 →
                  hsame nameCert nameCert2 →
                    finiteMultiHistPacketToEventFlow
                        (FiniteMultiHistPacketUp.mk histories ledgers comparisons routes
                          boundary provenance nameCert) =
                      finiteMultiHistPacketToEventFlow
                        (FiniteMultiHistPacketUp.mk histories2 ledgers2 comparisons2 routes2
                          boundary2 provenance2 nameCert2) := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro _hCont hHistories hLedgers hComparisons hRoutes hBoundary hProvenance hNameCert
  cases hHistories
  cases hLedgers
  cases hComparisons
  cases hRoutes
  cases hBoundary
  cases hProvenance
  cases hNameCert
  rfl

end BEDC.Derived.FiniteMultiHistPacketUp
