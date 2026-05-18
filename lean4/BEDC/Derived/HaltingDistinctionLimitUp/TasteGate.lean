import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HaltingDistinctionLimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HaltingDistinctionLimitUp : Type where
  | mk (program input trace diagonalObstruction transport route packageProvenance
      localNameCertLedger : BHist) : HaltingDistinctionLimitUp
  deriving DecidableEq

def haltingDistinctionLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: haltingDistinctionLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: haltingDistinctionLimitEncodeBHist h

def haltingDistinctionLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (haltingDistinctionLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (haltingDistinctionLimitDecodeBHist tail)

private theorem haltingDistinctionLimitDecode_encode_bhist :
    ∀ h : BHist, haltingDistinctionLimitDecodeBHist
      (haltingDistinctionLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def haltingDistinctionLimitToEventFlow : HaltingDistinctionLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingDistinctionLimitUp.mk program input trace diagonalObstruction transport route
      packageProvenance localNameCertLedger =>
      [[BMark.b0],
        haltingDistinctionLimitEncodeBHist program,
        [BMark.b1, BMark.b0],
        haltingDistinctionLimitEncodeBHist input,
        [BMark.b1, BMark.b1, BMark.b0],
        haltingDistinctionLimitEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDistinctionLimitEncodeBHist diagonalObstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDistinctionLimitEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDistinctionLimitEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        haltingDistinctionLimitEncodeBHist packageProvenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        haltingDistinctionLimitEncodeBHist localNameCertLedger]

def haltingDistinctionLimitFromEventFlow : EventFlow → Option HaltingDistinctionLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | program :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | input :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | trace :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | diagonalObstruction :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | packageProvenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | localNameCertLedger ::
                                                                  rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (HaltingDistinctionLimitUp.mk
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            program)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            input)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            trace)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            diagonalObstruction)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            transport)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            route)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            packageProvenance)
                                                                          (haltingDistinctionLimitDecodeBHist
                                                                            localNameCertLedger))
                                                                  | _ :: _ => none

private theorem haltingDistinctionLimit_round_trip :
    ∀ x : HaltingDistinctionLimitUp,
      haltingDistinctionLimitFromEventFlow
        (haltingDistinctionLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk program input trace diagonalObstruction transport route packageProvenance
      localNameCertLedger =>
      change
        some
          (HaltingDistinctionLimitUp.mk
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist program))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist input))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist trace))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist diagonalObstruction))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist transport))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist route))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist packageProvenance))
            (haltingDistinctionLimitDecodeBHist
              (haltingDistinctionLimitEncodeBHist localNameCertLedger))) =
          some
            (HaltingDistinctionLimitUp.mk program input trace diagonalObstruction transport
              route packageProvenance localNameCertLedger)
      rw [haltingDistinctionLimitDecode_encode_bhist program,
        haltingDistinctionLimitDecode_encode_bhist input,
        haltingDistinctionLimitDecode_encode_bhist trace,
        haltingDistinctionLimitDecode_encode_bhist diagonalObstruction,
        haltingDistinctionLimitDecode_encode_bhist transport,
        haltingDistinctionLimitDecode_encode_bhist route,
        haltingDistinctionLimitDecode_encode_bhist packageProvenance,
        haltingDistinctionLimitDecode_encode_bhist localNameCertLedger]

private theorem haltingDistinctionLimitToEventFlow_injective
    {x y : HaltingDistinctionLimitUp} :
    haltingDistinctionLimitToEventFlow x = haltingDistinctionLimitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      haltingDistinctionLimitFromEventFlow (haltingDistinctionLimitToEventFlow x) =
        haltingDistinctionLimitFromEventFlow (haltingDistinctionLimitToEventFlow y) :=
    congrArg haltingDistinctionLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (haltingDistinctionLimit_round_trip x).symm
      (Eq.trans hread (haltingDistinctionLimit_round_trip y)))

instance haltingDistinctionLimitBHistCarrier : BHistCarrier HaltingDistinctionLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := haltingDistinctionLimitToEventFlow
  fromEventFlow := haltingDistinctionLimitFromEventFlow

instance haltingDistinctionLimitChapterTasteGate :
    ChapterTasteGate HaltingDistinctionLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      haltingDistinctionLimitFromEventFlow (haltingDistinctionLimitToEventFlow x) = some x
    exact haltingDistinctionLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (haltingDistinctionLimitToEventFlow_injective heq)

def haltingDistinctionLimitFields : HaltingDistinctionLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HaltingDistinctionLimitUp.mk program input trace diagonalObstruction transport route
      packageProvenance localNameCertLedger =>
      [program, input, trace, diagonalObstruction, transport, route, packageProvenance,
        localNameCertLedger]

private theorem HaltingDistinctionLimitTasteGate_field_faithful_concrete :
    ∀ x y : HaltingDistinctionLimitUp,
      haltingDistinctionLimitFields x = haltingDistinctionLimitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk program₁ input₁ trace₁ diagonal₁ transport₁ route₁ provenance₁ ledger₁ =>
      cases y with
      | mk program₂ input₂ trace₂ diagonal₂ transport₂ route₂ provenance₂ ledger₂ =>
          simp only [haltingDistinctionLimitFields] at h
          injection h with hProgram tProgram
          injection tProgram with hInput tInput
          injection tInput with hTrace tTrace
          injection tTrace with hDiagonal tDiagonal
          injection tDiagonal with hTransport tTransport
          injection tTransport with hRoute tRoute
          injection tRoute with hProvenance tProvenance
          injection tProvenance with hLedger _
          subst hProgram
          subst hInput
          subst hTrace
          subst hDiagonal
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hLedger
          rfl

instance haltingDistinctionLimitFieldFaithful :
    FieldFaithful HaltingDistinctionLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := haltingDistinctionLimitFields
  field_faithful := HaltingDistinctionLimitTasteGate_field_faithful_concrete

def HaltingDistinctionLimitClassifier (x y : HaltingDistinctionLimitUp) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame
  match x, y with
  | HaltingDistinctionLimitUp.mk program input trace diagonal transport route
      packageProvenance localNameCertLedger,
    HaltingDistinctionLimitUp.mk program' input' trace' diagonal' transport' route'
      packageProvenance' localNameCertLedger' =>
      hsame program program' ∧
        hsame input input' ∧
          hsame trace trace' ∧
            hsame diagonal diagonal' ∧
              hsame transport transport' ∧
                hsame route route' ∧
                  hsame packageProvenance packageProvenance' ∧
                    hsame localNameCertLedger localNameCertLedger' ∧
                      Cont input trace diagonal ∧ Cont input' trace' diagonal'

def taste_gate : ChapterTasteGate HaltingDistinctionLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  haltingDistinctionLimitChapterTasteGate

theorem HaltingDistinctionLimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, haltingDistinctionLimitDecodeBHist
      (haltingDistinctionLimitEncodeBHist h) = h) ∧
      (∀ x : HaltingDistinctionLimitUp,
        haltingDistinctionLimitFromEventFlow
          (haltingDistinctionLimitToEventFlow x) = some x) ∧
        (∀ x y : HaltingDistinctionLimitUp,
          haltingDistinctionLimitToEventFlow x =
            haltingDistinctionLimitToEventFlow y -> x = y) ∧
          haltingDistinctionLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact haltingDistinctionLimitDecode_encode_bhist
  · constructor
    · exact haltingDistinctionLimit_round_trip
    · constructor
      · intro x y heq
        exact haltingDistinctionLimitToEventFlow_injective heq
      · rfl

theorem HaltingDistinctionLimitFixedPointBoundary
    {program input trace diagonal transport route packageProvenance localNameCertLedger
      endpoint : BHist}
    (traceRoute : Cont input trace diagonal)
    (returnRoute : Cont diagonal route endpoint) :
    Cont input (append trace route) endpoint ∧
      hsame program program ∧
        hsame input input ∧
          hsame trace trace ∧
            hsame diagonal diagonal ∧
              hsame transport transport ∧
                hsame route route ∧
                  hsame packageProvenance packageProvenance ∧
                    hsame localNameCertLedger localNameCertLedger ∧
                      haltingDistinctionLimitFromEventFlow
                          (haltingDistinctionLimitToEventFlow
                            (HaltingDistinctionLimitUp.mk program input trace diagonal
                              transport route packageProvenance localNameCertLedger)) =
                        some
                          (HaltingDistinctionLimitUp.mk program input trace diagonal
                            transport route packageProvenance localNameCertLedger) := by
  -- BEDC touchpoint anchor: BHist Cont append hsame
  constructor
  · cases traceRoute
    cases returnRoute
    exact append_assoc input trace route
  · exact
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        haltingDistinctionLimit_round_trip
          (HaltingDistinctionLimitUp.mk program input trace diagonal transport route
            packageProvenance localNameCertLedger)⟩

theorem HaltingDistinctionLimitPacket_sibling_boundary
    {program input trace diagonal transport route packageProvenance localNameCertLedger
      endpoint siblingRead : BHist}
    (traceRoute : Cont input trace diagonal)
    (returnRoute : Cont diagonal route endpoint)
    (siblingRoute : Cont endpoint packageProvenance siblingRead) :
    Cont input (append trace (append route packageProvenance)) siblingRead ∧
      Cont input (append trace route) endpoint ∧
        hsame diagonal diagonal ∧ hsame packageProvenance packageProvenance ∧
          haltingDistinctionLimitFromEventFlow
              (haltingDistinctionLimitToEventFlow
                (HaltingDistinctionLimitUp.mk program input trace diagonal transport route
                  packageProvenance localNameCertLedger)) =
            some
              (HaltingDistinctionLimitUp.mk program input trace diagonal transport route
                packageProvenance localNameCertLedger) := by
  -- BEDC touchpoint anchor: BHist Cont append hsame
  constructor
  · cases traceRoute
    cases returnRoute
    cases siblingRoute
    exact
      Eq.trans (append_assoc (append input trace) route packageProvenance)
        (append_assoc input trace (append route packageProvenance))
  · constructor
    · cases traceRoute
      cases returnRoute
      exact append_assoc input trace route
    · exact
        ⟨rfl, rfl,
          haltingDistinctionLimit_round_trip
            (HaltingDistinctionLimitUp.mk program input trace diagonal transport route
              packageProvenance localNameCertLedger)⟩

theorem HaltingDistinctionLimitNameCertObligations
    {program input trace diagonal transport route packageProvenance localNameCertLedger
      ledgerRead contextRead : BHist}
    (traceRoute : Cont input trace diagonal)
    (ledgerRoute : Cont diagonal route ledgerRead)
    (contextRoute : Cont ledgerRead packageProvenance contextRead) :
    Cont input (append trace (append route packageProvenance)) contextRead ∧
      hsame program program ∧
        hsame input input ∧
          hsame trace trace ∧
            hsame diagonal diagonal ∧
              hsame transport transport ∧
                hsame route route ∧
                  hsame packageProvenance packageProvenance ∧
                    hsame localNameCertLedger localNameCertLedger ∧
                      haltingDistinctionLimitFromEventFlow
                          (haltingDistinctionLimitToEventFlow
                            (HaltingDistinctionLimitUp.mk program input trace diagonal
                              transport route packageProvenance localNameCertLedger)) =
                        some
                          (HaltingDistinctionLimitUp.mk program input trace diagonal
                            transport route packageProvenance localNameCertLedger) := by
  -- BEDC touchpoint anchor: BHist Cont append hsame
  constructor
  · cases traceRoute
    cases ledgerRoute
    cases contextRoute
    exact
      Eq.trans (append_assoc (append input trace) route packageProvenance)
        (append_assoc input trace (append route packageProvenance))
  · exact
      ⟨hsame_refl program, hsame_refl input, hsame_refl trace, hsame_refl diagonal,
        hsame_refl transport, hsame_refl route, hsame_refl packageProvenance,
        hsame_refl localNameCertLedger,
        haltingDistinctionLimit_round_trip
          (HaltingDistinctionLimitUp.mk program input trace diagonal transport route
            packageProvenance localNameCertLedger)⟩

end BEDC.Derived.HaltingDistinctionLimitUp
