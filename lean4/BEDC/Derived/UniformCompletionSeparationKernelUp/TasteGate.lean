import BEDC.Derived.UniformCompletionSeparationKernelUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompletionSeparationKernelUp.TasteGate

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def uniformCompletionSeparationKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompletionSeparationKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompletionSeparationKernelEncodeBHist h

def uniformCompletionSeparationKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompletionSeparationKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompletionSeparationKernelDecodeBHist tail)

private theorem uniformCompletionSeparationKernelDecodeEncode :
    ∀ h : BHist,
      uniformCompletionSeparationKernelDecodeBHist
          (uniformCompletionSeparationKernelEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompletionSeparationKernelFields :
    UniformCompletionSeparationKernelUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompletionSeparationKernelUp.mk M U S F N R H C P L =>
      [M, U, S, F, N, R, H, C, P, L]

def uniformCompletionSeparationKernelToEventFlow :
    UniformCompletionSeparationKernelUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    List.map uniformCompletionSeparationKernelEncodeBHist
      (uniformCompletionSeparationKernelFields x)

def uniformCompletionSeparationKernelFromEventFlow :
    EventFlow → Option UniformCompletionSeparationKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | M :: U :: S :: F :: N :: R :: H :: C :: P :: L :: [] =>
      some
        (UniformCompletionSeparationKernelUp.mk
          (uniformCompletionSeparationKernelDecodeBHist M)
          (uniformCompletionSeparationKernelDecodeBHist U)
          (uniformCompletionSeparationKernelDecodeBHist S)
          (uniformCompletionSeparationKernelDecodeBHist F)
          (uniformCompletionSeparationKernelDecodeBHist N)
          (uniformCompletionSeparationKernelDecodeBHist R)
          (uniformCompletionSeparationKernelDecodeBHist H)
          (uniformCompletionSeparationKernelDecodeBHist C)
          (uniformCompletionSeparationKernelDecodeBHist P)
          (uniformCompletionSeparationKernelDecodeBHist L))
  | _ => none

private theorem uniformCompletionSeparationKernelRoundTrip :
    ∀ x : UniformCompletionSeparationKernelUp,
      uniformCompletionSeparationKernelFromEventFlow
          (uniformCompletionSeparationKernelToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M U S F N R H C P L =>
      simp only [uniformCompletionSeparationKernelToEventFlow,
        uniformCompletionSeparationKernelFields,
        uniformCompletionSeparationKernelFromEventFlow, List.map_cons, List.map_nil,
        uniformCompletionSeparationKernelDecodeEncode]

private theorem uniformCompletionSeparationKernelToEventFlow_injective
    {x y : UniformCompletionSeparationKernelUp} :
    uniformCompletionSeparationKernelToEventFlow x =
        uniformCompletionSeparationKernelToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          uniformCompletionSeparationKernelFromEventFlow
            (uniformCompletionSeparationKernelToEventFlow x) :=
        (uniformCompletionSeparationKernelRoundTrip x).symm
      _ =
          uniformCompletionSeparationKernelFromEventFlow
            (uniformCompletionSeparationKernelToEventFlow y) :=
        congrArg uniformCompletionSeparationKernelFromEventFlow hxy
      _ = some y := uniformCompletionSeparationKernelRoundTrip y
  exact Option.some.inj optionEq

instance uniformCompletionSeparationKernelBHistCarrier :
    BHistCarrier UniformCompletionSeparationKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompletionSeparationKernelToEventFlow
  fromEventFlow := uniformCompletionSeparationKernelFromEventFlow

instance uniformCompletionSeparationKernelChapterTasteGate :
    ChapterTasteGate UniformCompletionSeparationKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      uniformCompletionSeparationKernelFromEventFlow
          (uniformCompletionSeparationKernelToEventFlow x) =
        some x
    exact uniformCompletionSeparationKernelRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (uniformCompletionSeparationKernelToEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformCompletionSeparationKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompletionSeparationKernelChapterTasteGate

theorem UniformCompletionSeparationKernelFilterNetBranchVisibility
    [AskSetup] [PackageSetup]
    {M U S F N R H C P L completionRead separatedRead filterRead branchRead sealRead
      structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory U →
        UnaryHistory S →
          UnaryHistory F →
            UnaryHistory N →
              UnaryHistory R →
                UnaryHistory H →
                  UnaryHistory C →
                    UnaryHistory P →
                      UnaryHistory L →
                        Cont M U completionRead →
                          Cont completionRead S separatedRead →
                            Cont separatedRead F filterRead →
                              Cont filterRead N branchRead →
                                Cont branchRead R sealRead →
                                  Cont H C structuralRead →
                                    Cont P L namedRead →
                                      PkgSig bundle P pkg →
                                        PkgSig bundle L pkg →
                                          UnaryHistory completionRead ∧
                                            UnaryHistory separatedRead ∧
                                              UnaryHistory filterRead ∧
                                                UnaryHistory branchRead ∧
                                                  UnaryHistory sealRead ∧
                                                    Cont separatedRead F filterRead ∧
                                                      Cont filterRead N branchRead ∧
                                                        Cont branchRead R sealRead ∧
                                                          PkgSig bundle P pkg ∧
                                                            PkgSig bundle L pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro mUnary uUnary sUnary fUnary nUnary rUnary _hUnary _cUnary _pUnary _lUnary
    completionRoute separatedRoute filterRoute branchRoute sealRoute _structuralRoute
    _namedRoute provenancePkg namePkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary uUnary completionRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed completionUnary sUnary separatedRoute
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed separatedUnary fUnary filterRoute
  have branchUnary : UnaryHistory branchRead :=
    unary_cont_closed filterUnary nUnary branchRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed branchUnary rUnary sealRoute
  exact
    ⟨completionUnary, separatedUnary, filterUnary, branchUnary, sealUnary, filterRoute,
      branchRoute, sealRoute, provenancePkg, namePkg⟩

end BEDC.Derived.UniformCompletionSeparationKernelUp.TasteGate
