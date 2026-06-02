import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealLocatedOrderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive RealLocatedOrderUnaryRow : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | empty
  | e1 (tail : RealLocatedOrderUnaryRow)

def RealLocatedOrderUnaryRow.toBHist : RealLocatedOrderUnaryRow → BHist
  -- BEDC touchpoint anchor: BHist
  | RealLocatedOrderUnaryRow.empty => BHist.Empty
  | RealLocatedOrderUnaryRow.e1 tail => BHist.e1 tail.toBHist

def RealLocatedOrderUnaryRow.toUnaryHistory (row : RealLocatedOrderUnaryRow) :
    UnaryHistory row.toBHist :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  match row with
  | RealLocatedOrderUnaryRow.empty => by
      constructor
  | RealLocatedOrderUnaryRow.e1 tail => tail.toUnaryHistory

theorem RealLocatedOrderUnaryRow.toBHist_injective {x y : RealLocatedOrderUnaryRow} :
    x.toBHist = y.toBHist → x = y := by
  -- BEDC touchpoint anchor: BHist
  intro h
  induction x generalizing y with
  | empty =>
      cases y with
      | empty =>
          rfl
      | e1 tail =>
          cases h
  | e1 tail ih =>
      cases y with
      | empty =>
          cases h
      | e1 ytail =>
          injection h with htail
          exact congrArg RealLocatedOrderUnaryRow.e1 (ih htail)

inductive RealLocatedOrderUp : Type where
  | mk (source : RealLocatedOrderUnaryRow) (Y R S D O A H C P : BHist)

def realLocatedOrderFields : RealLocatedOrderUp → List BHist
  | RealLocatedOrderUp.mk source Y R S D O A H C P =>
      [source.toBHist, Y, R, S, D, O, A, H, C, P, source.toBHist]

theorem RealLocatedOrderCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (L : RealLocatedOrderUp)
    {X Y R S D O A H C P N xRead yRead windowRead toleranceRead apartnessRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realLocatedOrderFields L = [X, Y, R, S, D, O, A, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory Y →
          UnaryHistory R →
            UnaryHistory S →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory A →
                    UnaryHistory H →
                      UnaryHistory C →
                        Cont X R xRead →
                          Cont Y R yRead →
                            Cont R S windowRead →
                              Cont S D toleranceRead →
                                Cont O A apartnessRead →
                                  Cont H C replayRead →
                                    PkgSig bundle P pkg →
                                      SemanticNameCert
                                          (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row X ∨ hsame row Y ∨ hsame row R ∨
                                              hsame row S ∨ hsame row D ∨ hsame row O ∨
                                                hsame row A ∨ Cont X R xRead ∨
                                                  Cont Y R yRead ∨ Cont R S windowRead ∨
                                                    Cont S D toleranceRead ∨
                                                      Cont O A apartnessRead ∨
                                                        Cont H C replayRead)
                                          (fun row : BHist =>
                                            PkgSig bundle P pkg ∧ hsame row N)
                                          hsame ∧
                                        UnaryHistory xRead ∧ UnaryHistory yRead ∧
                                          UnaryHistory windowRead ∧
                                            UnaryHistory toleranceRead ∧
                                              UnaryHistory apartnessRead ∧
                                                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro fieldsEq unaryX unaryY unaryR unaryS unaryD unaryO unaryA unaryH unaryC xCont
    yCont windowCont toleranceCont apartnessCont replayCont pkgP
  rcases L with ⟨sourceRow, y0, r0, s0, d0, o0, a0, h0, c0, p0⟩
  injection fieldsEq with hX t1
  injection t1 with hY t2
  injection t2 with hR t3
  injection t3 with hS t4
  injection t4 with hD t5
  injection t5 with hO t6
  injection t6 with hA t7
  injection t7 with hH t8
  injection t8 with hC t9
  injection t9 with hP t10
  injection t10 with hN _
  cases hX
  cases hY
  cases hR
  cases hS
  cases hD
  cases hO
  cases hA
  cases hH
  cases hC
  cases hP
  cases hN
  have xUnary : UnaryHistory xRead :=
    unary_cont_closed unaryX unaryR xCont
  have yUnary : UnaryHistory yRead :=
    unary_cont_closed unaryY unaryR yCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryR unaryS windowCont
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryS unaryD toleranceCont
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed unaryO unaryA apartnessCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryH unaryC replayCont
  have sourceN :
          (fun row : BHist => hsame row sourceRow.toBHist ∧ UnaryHistory row)
            sourceRow.toBHist := by
    exact ⟨hsame_refl sourceRow.toBHist, sourceRow.toUnaryHistory⟩
  have cert :
          SemanticNameCert
              (fun row : BHist => hsame row sourceRow.toBHist ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row sourceRow.toBHist ∨ hsame row Y ∨ hsame row R ∨
                  hsame row S ∨ hsame row D ∨ hsame row O ∨ hsame row A ∨
                    Cont sourceRow.toBHist R xRead ∨ Cont Y R yRead ∨
                      Cont R S windowRead ∨ Cont S D toleranceRead ∨
                        Cont O A apartnessRead ∨ Cont H C replayRead)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row sourceRow.toBHist)
              hsame := by
    exact {
      core := {
            carrier_inhabited := Exists.intro sourceRow.toBHist sourceN
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro _row _other sameRows
              exact hsame_symm sameRows
            equiv_trans := by
              intro _row _middle _other sameLeft sameRight
              exact hsame_trans sameLeft sameRight
            carrier_respects_equiv := by
              intro _row _other sameRows source
              exact
                ⟨hsame_trans (hsame_symm sameRows) source.left,
                  unary_transport source.right sameRows⟩
          }
      pattern_sound := by
            intro _row source
            exact Or.inl source.left
      ledger_sound := by
            intro _row source
            exact ⟨pkgP, source.left⟩
    }
  exact
    ⟨cert, xUnary, yUnary, windowUnary, toleranceUnary, apartnessUnary, replayUnary⟩

theorem RealLocatedOrderCarrier_apartness_handoff [AskSetup] [PackageSetup]
    (L : RealLocatedOrderUp)
    {X Y R S D O A H C P N xRead yRead windowRead toleranceRead locatedRead
      apartnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    realLocatedOrderFields L = [X, Y, R, S, D, O, A, H, C, P, N] →
      UnaryHistory X →
        UnaryHistory Y →
          UnaryHistory R →
            UnaryHistory S →
              UnaryHistory D →
                UnaryHistory O →
                  UnaryHistory A →
                    Cont X R xRead →
                      Cont Y R yRead →
                        Cont R S windowRead →
                          Cont S D toleranceRead →
                            Cont toleranceRead O locatedRead →
                              Cont locatedRead A apartnessRead →
                                PkgSig bundle P pkg →
                                  UnaryHistory xRead ∧ UnaryHistory yRead ∧
                                    UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                      UnaryHistory locatedRead ∧
                                        UnaryHistory apartnessRead ∧
                                          Cont toleranceRead O locatedRead ∧
                                            Cont locatedRead A apartnessRead ∧
                                              PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro fieldsEq unaryX unaryY unaryR unaryS unaryD unaryO unaryA xCont yCont windowCont
    toleranceCont locatedCont apartnessCont pkgP
  rcases L with ⟨sourceRow, y0, r0, s0, d0, o0, a0, h0, c0, p0⟩
  cases fieldsEq
  have xUnary : UnaryHistory xRead :=
    unary_cont_closed unaryX unaryR xCont
  have yUnary : UnaryHistory yRead :=
    unary_cont_closed unaryY unaryR yCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed unaryR unaryS windowCont
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed unaryS unaryD toleranceCont
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed toleranceUnary unaryO locatedCont
  have apartnessUnary : UnaryHistory apartnessRead :=
    unary_cont_closed locatedUnary unaryA apartnessCont
  exact
    ⟨xUnary, yUnary, windowUnary, toleranceUnary, locatedUnary, apartnessUnary, locatedCont,
      apartnessCont, pkgP⟩

end BEDC.Derived.RealLocatedOrderUp
