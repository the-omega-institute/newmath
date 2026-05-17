import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TailCompatibleCauchySectionUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TailCompatibleCauchySectionUp : Type where
  | mk :
      (family modulus precision sectionIndex diagonalIndex window budget readback dyadicLedger
        realSeal transport replay provenance nameCert : BHist) →
      TailCompatibleCauchySectionUp
  deriving DecidableEq

def tailCompatibleCauchySectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: tailCompatibleCauchySectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: tailCompatibleCauchySectionEncodeBHist h

def tailCompatibleCauchySectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (tailCompatibleCauchySectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (tailCompatibleCauchySectionDecodeBHist tail)

private theorem tailCompatibleCauchySectionDecode_encode_bhist :
    ∀ h : BHist,
      tailCompatibleCauchySectionDecodeBHist
        (tailCompatibleCauchySectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def tailCompatibleCauchySectionToEventFlow :
    TailCompatibleCauchySectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TailCompatibleCauchySectionUp.mk family modulus precision sectionIndex diagonalIndex window
      budget readback dyadicLedger realSeal transport replay provenance nameCert =>
      [[BMark.b0],
        tailCompatibleCauchySectionEncodeBHist family,
        [BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist sectionIndex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist diagonalIndex,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist budget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        tailCompatibleCauchySectionEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        tailCompatibleCauchySectionEncodeBHist nameCert]

def tailCompatibleCauchySectionFromEventFlow :
    EventFlow → Option TailCompatibleCauchySectionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | family :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | modulus :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | precision :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | sectionIndex :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | diagonalIndex :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | window :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | budget :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | readback :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | dyadicLedger ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17 with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18 with
                                                                              | [] => none
                                                                              | realSeal ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | transport ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | replay ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      none
                                                                                                  | _tag12 ::
                                                                                                      rest24 =>
                                                                                                      match
                                                                                                        rest24
                                                                                                      with
                                                                                                      | [] =>
                                                                                                          none
                                                                                                      | provenance ::
                                                                                                          rest25 =>
                                                                                                          match
                                                                                                            rest25
                                                                                                          with
                                                                                                          | [] =>
                                                                                                              none
                                                                                                          | _tag13 ::
                                                                                                              rest26 =>
                                                                                                              match
                                                                                                                rest26
                                                                                                              with
                                                                                                              | [] =>
                                                                                                                  none
                                                                                                              | nameCert ::
                                                                                                                  rest27 =>
                                                                                                                  match
                                                                                                                    rest27
                                                                                                                  with
                                                                                                                  | [] =>
                                                                                                                      some
                                                                                                                        (TailCompatibleCauchySectionUp.mk
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            family)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            modulus)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            precision)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            sectionIndex)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            diagonalIndex)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            window)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            budget)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            readback)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            dyadicLedger)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            realSeal)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            transport)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            replay)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            provenance)
                                                                                                                          (tailCompatibleCauchySectionDecodeBHist
                                                                                                                            nameCert))
                                                                                                                  | _ :: _ =>
                                                                                                                      none

private theorem tailCompatibleCauchySection_round_trip
    (x : TailCompatibleCauchySectionUp) :
    tailCompatibleCauchySectionFromEventFlow
      (tailCompatibleCauchySectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk family modulus precision sectionIndex diagonalIndex window budget readback dyadicLedger
      realSeal transport replay provenance nameCert =>
      change
        some
          (TailCompatibleCauchySectionUp.mk
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist family))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist modulus))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist precision))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist sectionIndex))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist diagonalIndex))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist window))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist budget))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist readback))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist dyadicLedger))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist realSeal))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist transport))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist replay))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist provenance))
            (tailCompatibleCauchySectionDecodeBHist
              (tailCompatibleCauchySectionEncodeBHist nameCert))) =
          some
            (TailCompatibleCauchySectionUp.mk family modulus precision sectionIndex
              diagonalIndex window budget readback dyadicLedger realSeal transport replay
              provenance nameCert)
      rw [tailCompatibleCauchySectionDecode_encode_bhist family,
        tailCompatibleCauchySectionDecode_encode_bhist modulus,
        tailCompatibleCauchySectionDecode_encode_bhist precision,
        tailCompatibleCauchySectionDecode_encode_bhist sectionIndex,
        tailCompatibleCauchySectionDecode_encode_bhist diagonalIndex,
        tailCompatibleCauchySectionDecode_encode_bhist window,
        tailCompatibleCauchySectionDecode_encode_bhist budget,
        tailCompatibleCauchySectionDecode_encode_bhist readback,
        tailCompatibleCauchySectionDecode_encode_bhist dyadicLedger,
        tailCompatibleCauchySectionDecode_encode_bhist realSeal,
        tailCompatibleCauchySectionDecode_encode_bhist transport,
        tailCompatibleCauchySectionDecode_encode_bhist replay,
        tailCompatibleCauchySectionDecode_encode_bhist provenance,
        tailCompatibleCauchySectionDecode_encode_bhist nameCert]

private theorem tailCompatibleCauchySectionToEventFlow_injective
    {x y : TailCompatibleCauchySectionUp} :
    tailCompatibleCauchySectionToEventFlow x =
      tailCompatibleCauchySectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk family1 modulus1 precision1 sectionIndex1 diagonalIndex1 window1 budget1 readback1
      dyadicLedger1 realSeal1 transport1 replay1 provenance1 nameCert1 =>
      cases y with
      | mk family2 modulus2 precision2 sectionIndex2 diagonalIndex2 window2 budget2
          readback2 dyadicLedger2 realSeal2 transport2 replay2 provenance2 nameCert2 =>
          injection heq with _ tail1
          injection tail1 with hFamily tail2
          injection tail2 with _ tail3
          injection tail3 with hModulus tail4
          injection tail4 with _ tail5
          injection tail5 with hPrecision tail6
          injection tail6 with _ tail7
          injection tail7 with hSection tail8
          injection tail8 with _ tail9
          injection tail9 with hDiagonal tail10
          injection tail10 with _ tail11
          injection tail11 with hWindow tail12
          injection tail12 with _ tail13
          injection tail13 with hBudget tail14
          injection tail14 with _ tail15
          injection tail15 with hReadback tail16
          injection tail16 with _ tail17
          injection tail17 with hDyadic tail18
          injection tail18 with _ tail19
          injection tail19 with hReal tail20
          injection tail20 with _ tail21
          injection tail21 with hTransport tail22
          injection tail22 with _ tail23
          injection tail23 with hReplay tail24
          injection tail24 with _ tail25
          injection tail25 with hProvenance tail26
          injection tail26 with _ tail27
          injection tail27 with hName _
          have familyEq : family1 = family2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist family1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hFamily)
                (tailCompatibleCauchySectionDecode_encode_bhist family2))
          have modulusEq : modulus1 = modulus2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist modulus1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hModulus)
                (tailCompatibleCauchySectionDecode_encode_bhist modulus2))
          have precisionEq : precision1 = precision2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist precision1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hPrecision)
                (tailCompatibleCauchySectionDecode_encode_bhist precision2))
          have sectionEq : sectionIndex1 = sectionIndex2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist sectionIndex1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hSection)
                (tailCompatibleCauchySectionDecode_encode_bhist sectionIndex2))
          have diagonalEq : diagonalIndex1 = diagonalIndex2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist diagonalIndex1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hDiagonal)
                (tailCompatibleCauchySectionDecode_encode_bhist diagonalIndex2))
          have windowEq : window1 = window2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist window1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hWindow)
                (tailCompatibleCauchySectionDecode_encode_bhist window2))
          have budgetEq : budget1 = budget2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist budget1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hBudget)
                (tailCompatibleCauchySectionDecode_encode_bhist budget2))
          have readbackEq : readback1 = readback2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist readback1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hReadback)
                (tailCompatibleCauchySectionDecode_encode_bhist readback2))
          have dyadicEq : dyadicLedger1 = dyadicLedger2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist dyadicLedger1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hDyadic)
                (tailCompatibleCauchySectionDecode_encode_bhist dyadicLedger2))
          have realEq : realSeal1 = realSeal2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist realSeal1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hReal)
                (tailCompatibleCauchySectionDecode_encode_bhist realSeal2))
          have transportEq : transport1 = transport2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist transport1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hTransport)
                (tailCompatibleCauchySectionDecode_encode_bhist transport2))
          have replayEq : replay1 = replay2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist replay1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hReplay)
                (tailCompatibleCauchySectionDecode_encode_bhist replay2))
          have provenanceEq : provenance1 = provenance2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist provenance1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hProvenance)
                (tailCompatibleCauchySectionDecode_encode_bhist provenance2))
          have nameEq : nameCert1 = nameCert2 :=
            Eq.trans (tailCompatibleCauchySectionDecode_encode_bhist nameCert1).symm
              (Eq.trans (congrArg tailCompatibleCauchySectionDecodeBHist hName)
                (tailCompatibleCauchySectionDecode_encode_bhist nameCert2))
          cases familyEq
          cases modulusEq
          cases precisionEq
          cases sectionEq
          cases diagonalEq
          cases windowEq
          cases budgetEq
          cases readbackEq
          cases dyadicEq
          cases realEq
          cases transportEq
          cases replayEq
          cases provenanceEq
          cases nameEq
          rfl

instance tailCompatibleCauchySectionBHistCarrier :
    BHistCarrier TailCompatibleCauchySectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := tailCompatibleCauchySectionToEventFlow
  fromEventFlow := tailCompatibleCauchySectionFromEventFlow

instance tailCompatibleCauchySectionChapterTasteGate :
    ChapterTasteGate TailCompatibleCauchySectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      tailCompatibleCauchySectionFromEventFlow
        (tailCompatibleCauchySectionToEventFlow x) = some x
    exact tailCompatibleCauchySection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (tailCompatibleCauchySectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TailCompatibleCauchySectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  tailCompatibleCauchySectionChapterTasteGate

def tailCompatibleCauchySectionFields :
    TailCompatibleCauchySectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TailCompatibleCauchySectionUp.mk family modulus precision sectionIndex diagonalIndex window
      budget readback dyadicLedger realSeal transport replay provenance nameCert =>
      [family, modulus, precision, sectionIndex, diagonalIndex, window, budget, readback,
        dyadicLedger, realSeal, transport, replay, provenance, nameCert]

instance tailCompatibleCauchySectionFieldFaithful :
    FieldFaithful TailCompatibleCauchySectionUp where
  fields := tailCompatibleCauchySectionFields
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk family1 modulus1 precision1 sectionIndex1 diagonalIndex1 window1 budget1 readback1
        dyadicLedger1 realSeal1 transport1 replay1 provenance1 nameCert1 =>
        cases y with
        | mk family2 modulus2 precision2 sectionIndex2 diagonalIndex2 window2 budget2
            readback2 dyadicLedger2 realSeal2 transport2 replay2 provenance2 nameCert2 =>
            injection h with hFamily t1
            injection t1 with hModulus t2
            injection t2 with hPrecision t3
            injection t3 with hSection t4
            injection t4 with hDiagonal t5
            injection t5 with hWindow t6
            injection t6 with hBudget t7
            injection t7 with hReadback t8
            injection t8 with hDyadic t9
            injection t9 with hReal t10
            injection t10 with hTransport t11
            injection t11 with hReplay t12
            injection t12 with hProvenance t13
            injection t13 with hName _
            cases hFamily
            cases hModulus
            cases hPrecision
            cases hSection
            cases hDiagonal
            cases hWindow
            cases hBudget
            cases hReadback
            cases hDyadic
            cases hReal
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

instance tailCompatibleCauchySectionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial TailCompatibleCauchySectionUp where
  witness_pair :=
    -- BEDC touchpoint anchor: BHist BMark
    ⟨TailCompatibleCauchySectionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TailCompatibleCauchySectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TailCompatibleCauchySectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      tailCompatibleCauchySectionDecodeBHist (tailCompatibleCauchySectionEncodeBHist h) = h) ∧
      (∀ x : TailCompatibleCauchySectionUp,
        tailCompatibleCauchySectionFromEventFlow
          (tailCompatibleCauchySectionToEventFlow x) = some x) ∧
        (∀ x y : TailCompatibleCauchySectionUp,
          tailCompatibleCauchySectionToEventFlow x =
            tailCompatibleCauchySectionToEventFlow y → x = y) ∧
          tailCompatibleCauchySectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact tailCompatibleCauchySectionDecode_encode_bhist
  · constructor
    · exact tailCompatibleCauchySection_round_trip
    · constructor
      · intro x y heq
        exact tailCompatibleCauchySectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.TailCompatibleCauchySectionUp.TasteGate
