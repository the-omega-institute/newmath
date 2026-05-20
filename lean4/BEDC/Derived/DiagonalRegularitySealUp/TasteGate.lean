import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalRegularitySealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalRegularitySealUp : Type where
  | mk
      (representative endpointLeft endpointRight middleModulus dyadicTolerance finiteWindow
        regularityWitness terminalSeal transport routes provenance nameCert : BHist) :
      DiagonalRegularitySealUp
  deriving DecidableEq

def diagonalRegularitySealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalRegularitySealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalRegularitySealEncodeBHist h

def diagonalRegularitySealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalRegularitySealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalRegularitySealDecodeBHist tail)

private theorem diagonalRegularitySealDecodeEncodeBHist :
    ∀ h : BHist,
      diagonalRegularitySealDecodeBHist (diagonalRegularitySealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem diagonalRegularitySealMk_eq
    {representative₁ representative₂ endpointLeft₁ endpointLeft₂ endpointRight₁ endpointRight₂
      middleModulus₁ middleModulus₂ dyadicTolerance₁ dyadicTolerance₂ finiteWindow₁
      finiteWindow₂ regularityWitness₁ regularityWitness₂ terminalSeal₁ terminalSeal₂
      transport₁ transport₂ routes₁ routes₂ provenance₁ provenance₂ nameCert₁ nameCert₂ :
        BHist} :
    representative₁ = representative₂ →
      endpointLeft₁ = endpointLeft₂ →
        endpointRight₁ = endpointRight₂ →
          middleModulus₁ = middleModulus₂ →
            dyadicTolerance₁ = dyadicTolerance₂ →
              finiteWindow₁ = finiteWindow₂ →
                regularityWitness₁ = regularityWitness₂ →
                  terminalSeal₁ = terminalSeal₂ →
                    transport₁ = transport₂ →
                      routes₁ = routes₂ →
                        provenance₁ = provenance₂ →
                          nameCert₁ = nameCert₂ →
                            DiagonalRegularitySealUp.mk representative₁ endpointLeft₁
                                endpointRight₁ middleModulus₁ dyadicTolerance₁ finiteWindow₁
                                regularityWitness₁ terminalSeal₁ transport₁ routes₁ provenance₁
                                nameCert₁ =
                              DiagonalRegularitySealUp.mk representative₂ endpointLeft₂
                                endpointRight₂ middleModulus₂ dyadicTolerance₂ finiteWindow₂
                                regularityWitness₂ terminalSeal₂ transport₂ routes₂ provenance₂
                                nameCert₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro representativeEq endpointLeftEq endpointRightEq middleModulusEq dyadicToleranceEq
    finiteWindowEq regularityWitnessEq terminalSealEq transportEq routesEq provenanceEq
    nameCertEq
  cases representativeEq
  cases endpointLeftEq
  cases endpointRightEq
  cases middleModulusEq
  cases dyadicToleranceEq
  cases finiteWindowEq
  cases regularityWitnessEq
  cases terminalSealEq
  cases transportEq
  cases routesEq
  cases provenanceEq
  cases nameCertEq
  rfl

def diagonalRegularitySealToEventFlow : DiagonalRegularitySealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
      dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance
      nameCert =>
      [[BMark.b0],
        diagonalRegularitySealEncodeBHist representative,
        [BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist endpointLeft,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist endpointRight,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist middleModulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist dyadicTolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist finiteWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist regularityWitness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalRegularitySealEncodeBHist terminalSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalRegularitySealEncodeBHist nameCert]

def diagonalRegularitySealFromEventFlow : EventFlow → Option DiagonalRegularitySealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | representative :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | endpointLeft :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | endpointRight :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | middleModulus :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | dyadicTolerance :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | finiteWindow :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | regularityWitness :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | terminalSeal :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | routes :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | nameCert :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (DiagonalRegularitySealUp.mk
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            representative)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            endpointLeft)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            endpointRight)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            middleModulus)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            dyadicTolerance)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            finiteWindow)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            regularityWitness)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            terminalSeal)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            transport)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            routes)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            provenance)
                                                                                                          (diagonalRegularitySealDecodeBHist
                                                                                                            nameCert))
                                                                                                  | _ :: _ => none

private theorem diagonalRegularitySeal_round_trip :
    ∀ x : DiagonalRegularitySealUp,
      diagonalRegularitySealFromEventFlow (diagonalRegularitySealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk representative endpointLeft endpointRight middleModulus dyadicTolerance finiteWindow
      regularityWitness terminalSeal transport routes provenance nameCert =>
      exact congrArg some
        (diagonalRegularitySealMk_eq
          (diagonalRegularitySealDecodeEncodeBHist representative)
          (diagonalRegularitySealDecodeEncodeBHist endpointLeft)
          (diagonalRegularitySealDecodeEncodeBHist endpointRight)
          (diagonalRegularitySealDecodeEncodeBHist middleModulus)
          (diagonalRegularitySealDecodeEncodeBHist dyadicTolerance)
          (diagonalRegularitySealDecodeEncodeBHist finiteWindow)
          (diagonalRegularitySealDecodeEncodeBHist regularityWitness)
          (diagonalRegularitySealDecodeEncodeBHist terminalSeal)
          (diagonalRegularitySealDecodeEncodeBHist transport)
          (diagonalRegularitySealDecodeEncodeBHist routes)
          (diagonalRegularitySealDecodeEncodeBHist provenance)
          (diagonalRegularitySealDecodeEncodeBHist nameCert))

private theorem diagonalRegularitySealToEventFlow_injective
    {x y : DiagonalRegularitySealUp} :
    diagonalRegularitySealToEventFlow x = diagonalRegularitySealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk representative₁ endpointLeft₁ endpointRight₁ middleModulus₁ dyadicTolerance₁
      finiteWindow₁ regularityWitness₁ terminalSeal₁ transport₁ routes₁ provenance₁
      nameCert₁ =>
      cases y with
      | mk representative₂ endpointLeft₂ endpointRight₂ middleModulus₂ dyadicTolerance₂
          finiteWindow₂ regularityWitness₂ terminalSeal₂ transport₂ routes₂ provenance₂
          nameCert₂ =>
          injection heq with _ rest₀
          injection rest₀ with hRepresentative rest₁
          injection rest₁ with _ rest₂
          injection rest₂ with hEndpointLeft rest₃
          injection rest₃ with _ rest₄
          injection rest₄ with hEndpointRight rest₅
          injection rest₅ with _ rest₆
          injection rest₆ with hMiddleModulus rest₇
          injection rest₇ with _ rest₈
          injection rest₈ with hDyadicTolerance rest₉
          injection rest₉ with _ rest₁₀
          injection rest₁₀ with hFiniteWindow rest₁₁
          injection rest₁₁ with _ rest₁₂
          injection rest₁₂ with hRegularityWitness rest₁₃
          injection rest₁₃ with _ rest₁₄
          injection rest₁₄ with hTerminalSeal rest₁₅
          injection rest₁₅ with _ rest₁₆
          injection rest₁₆ with hTransport rest₁₇
          injection rest₁₇ with _ rest₁₈
          injection rest₁₈ with hRoutes rest₁₉
          injection rest₁₉ with _ rest₂₀
          injection rest₂₀ with hProvenance rest₂₁
          injection rest₂₁ with _ rest₂₂
          injection rest₂₂ with hNameCert _
          have representativeEq : representative₁ = representative₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hRepresentative
            rw [diagonalRegularitySealDecodeEncodeBHist representative₁,
              diagonalRegularitySealDecodeEncodeBHist representative₂] at h
            exact h
          have endpointLeftEq : endpointLeft₁ = endpointLeft₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hEndpointLeft
            rw [diagonalRegularitySealDecodeEncodeBHist endpointLeft₁,
              diagonalRegularitySealDecodeEncodeBHist endpointLeft₂] at h
            exact h
          have endpointRightEq : endpointRight₁ = endpointRight₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hEndpointRight
            rw [diagonalRegularitySealDecodeEncodeBHist endpointRight₁,
              diagonalRegularitySealDecodeEncodeBHist endpointRight₂] at h
            exact h
          have middleModulusEq : middleModulus₁ = middleModulus₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hMiddleModulus
            rw [diagonalRegularitySealDecodeEncodeBHist middleModulus₁,
              diagonalRegularitySealDecodeEncodeBHist middleModulus₂] at h
            exact h
          have dyadicToleranceEq : dyadicTolerance₁ = dyadicTolerance₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hDyadicTolerance
            rw [diagonalRegularitySealDecodeEncodeBHist dyadicTolerance₁,
              diagonalRegularitySealDecodeEncodeBHist dyadicTolerance₂] at h
            exact h
          have finiteWindowEq : finiteWindow₁ = finiteWindow₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hFiniteWindow
            rw [diagonalRegularitySealDecodeEncodeBHist finiteWindow₁,
              diagonalRegularitySealDecodeEncodeBHist finiteWindow₂] at h
            exact h
          have regularityWitnessEq : regularityWitness₁ = regularityWitness₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hRegularityWitness
            rw [diagonalRegularitySealDecodeEncodeBHist regularityWitness₁,
              diagonalRegularitySealDecodeEncodeBHist regularityWitness₂] at h
            exact h
          have terminalSealEq : terminalSeal₁ = terminalSeal₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hTerminalSeal
            rw [diagonalRegularitySealDecodeEncodeBHist terminalSeal₁,
              diagonalRegularitySealDecodeEncodeBHist terminalSeal₂] at h
            exact h
          have transportEq : transport₁ = transport₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hTransport
            rw [diagonalRegularitySealDecodeEncodeBHist transport₁,
              diagonalRegularitySealDecodeEncodeBHist transport₂] at h
            exact h
          have routesEq : routes₁ = routes₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hRoutes
            rw [diagonalRegularitySealDecodeEncodeBHist routes₁,
              diagonalRegularitySealDecodeEncodeBHist routes₂] at h
            exact h
          have provenanceEq : provenance₁ = provenance₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hProvenance
            rw [diagonalRegularitySealDecodeEncodeBHist provenance₁,
              diagonalRegularitySealDecodeEncodeBHist provenance₂] at h
            exact h
          have nameCertEq : nameCert₁ = nameCert₂ := by
            have h := congrArg diagonalRegularitySealDecodeBHist hNameCert
            rw [diagonalRegularitySealDecodeEncodeBHist nameCert₁,
              diagonalRegularitySealDecodeEncodeBHist nameCert₂] at h
            exact h
          cases representativeEq
          cases endpointLeftEq
          cases endpointRightEq
          cases middleModulusEq
          cases dyadicToleranceEq
          cases finiteWindowEq
          cases regularityWitnessEq
          cases terminalSealEq
          cases transportEq
          cases routesEq
          cases provenanceEq
          cases nameCertEq
          rfl

instance diagonalRegularitySealBHistCarrier : BHistCarrier DiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalRegularitySealToEventFlow
  fromEventFlow := diagonalRegularitySealFromEventFlow

instance diagonalRegularitySealChapterTasteGate :
    ChapterTasteGate DiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalRegularitySealFromEventFlow (diagonalRegularitySealToEventFlow x) = some x
    exact diagonalRegularitySeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalRegularitySealToEventFlow_injective heq)

instance diagonalRegularitySealNontrivial : Nontrivial DiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalRegularitySealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalRegularitySealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

instance diagonalRegularitySealFieldFaithful : FieldFaithful DiagonalRegularitySealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
        dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes
        provenance nameCert =>
        [representative, endpointLeft, endpointRight, middleModulus, dyadicTolerance,
          finiteWindow, regularityWitness, terminalSeal, transport, routes, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk representative₁ endpointLeft₁ endpointRight₁ middleModulus₁ dyadicTolerance₁
        finiteWindow₁ regularityWitness₁ terminalSeal₁ transport₁ routes₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk representative₂ endpointLeft₂ endpointRight₂ middleModulus₂ dyadicTolerance₂
            finiteWindow₂ regularityWitness₂ terminalSeal₂ transport₂ routes₂ provenance₂
            nameCert₂ =>
            simp only [] at h
            cases h
            rfl

def taste_gate : ChapterTasteGate DiagonalRegularitySealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  diagonalRegularitySealChapterTasteGate

theorem DiagonalRegularitySealTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalRegularitySealDecodeBHist (diagonalRegularitySealEncodeBHist h) = h) ∧
      (∀ x : DiagonalRegularitySealUp,
        diagonalRegularitySealFromEventFlow (diagonalRegularitySealToEventFlow x) = some x) ∧
        (∀ x y : DiagonalRegularitySealUp,
          diagonalRegularitySealToEventFlow x = diagonalRegularitySealToEventFlow y → x = y) ∧
          diagonalRegularitySealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalRegularitySealDecodeEncodeBHist
  · constructor
    · exact diagonalRegularitySeal_round_trip
    · constructor
      · intro x y heq
        exact diagonalRegularitySealToEventFlow_injective heq
      · rfl

theorem DiagonalRegularitySealCarrier_window_factorization
    {representative endpointLeft endpointRight middleModulus dyadicTolerance finiteWindow
      regularityWitness terminalSeal transport routes provenance nameCert endpointRead middleRead
      toleranceRead sealRead : BHist} :
    Cont representative endpointLeft endpointRead →
      Cont endpointRead endpointRight middleRead →
        Cont middleRead dyadicTolerance toleranceRead →
          Cont finiteWindow regularityWitness sealRead →
            UnaryHistory representative →
              UnaryHistory endpointLeft →
                UnaryHistory endpointRight →
                  UnaryHistory middleModulus →
                    UnaryHistory dyadicTolerance →
                      UnaryHistory finiteWindow →
                        UnaryHistory regularityWitness →
                          ∃ packet : DiagonalRegularitySealUp,
                            packet = DiagonalRegularitySealUp.mk representative endpointLeft
                              endpointRight middleModulus dyadicTolerance finiteWindow
                              regularityWitness terminalSeal transport routes provenance nameCert ∧
                              UnaryHistory endpointRead ∧
                                UnaryHistory middleRead ∧
                                  UnaryHistory toleranceRead ∧
                                    UnaryHistory sealRead ∧
                                      List.Mem
                                        (diagonalRegularitySealEncodeBHist finiteWindow)
                                        (diagonalRegularitySealToEventFlow packet) := by
  -- BEDC touchpoint anchor: BHist BMark Cont UnaryHistory
  intro hEndpoint hMiddle hTolerance hSeal representativeUnary endpointLeftUnary
    endpointRightUnary _middleModulusUnary dyadicToleranceUnary finiteWindowUnary
    regularityWitnessUnary
  let packet :=
    DiagonalRegularitySealUp.mk representative endpointLeft endpointRight middleModulus
      dyadicTolerance finiteWindow regularityWitness terminalSeal transport routes provenance nameCert
  refine ⟨packet, ?_⟩
  constructor
  · rfl
  · have endpointReadUnary : UnaryHistory endpointRead :=
      unary_cont_closed representativeUnary endpointLeftUnary hEndpoint
    have middleReadUnary : UnaryHistory middleRead :=
      unary_cont_closed endpointReadUnary endpointRightUnary hMiddle
    have toleranceReadUnary : UnaryHistory toleranceRead :=
      unary_cont_closed middleReadUnary dyadicToleranceUnary hTolerance
    have sealReadUnary : UnaryHistory sealRead :=
      unary_cont_closed finiteWindowUnary regularityWitnessUnary hSeal
    constructor
    · exact endpointReadUnary
    · constructor
      · exact middleReadUnary
      · constructor
        · exact toleranceReadUnary
        · constructor
          · exact sealReadUnary
          · simp only [packet, diagonalRegularitySealToEventFlow]
            repeat
              first
              | exact List.Mem.head _
              | apply List.Mem.tail

end BEDC.Derived.DiagonalRegularitySealUp
