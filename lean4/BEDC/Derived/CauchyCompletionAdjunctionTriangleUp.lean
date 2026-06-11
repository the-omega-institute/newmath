import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionAdjunctionTriangleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive CauchyCompletionAdjunctionTriangleUp : Type where
  | mk (F A U I R W D E H C P N : BHist) : CauchyCompletionAdjunctionTriangleUp

def cauchyCompletionAdjunctionTriangleFields :
    CauchyCompletionAdjunctionTriangleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionAdjunctionTriangleUp.mk F A U I R W D E H C P N =>
      [F, A, U, I, R, W, D, E, H, C, P, N]

theorem CauchyCompletionAdjunctionTriangleUniversalHandoff [AskSetup] [PackageSetup]
    {F A U I R W D E H C P N universalRead idempotenceRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyCompletionAdjunctionTriangleFields
        (CauchyCompletionAdjunctionTriangleUp.mk F A U I R W D E H C P N) =
        [F, A, U, I, R, W, D, E, H, C, P, N] →
      UnaryHistory F →
        UnaryHistory A →
          UnaryHistory U →
            UnaryHistory R →
              Cont F A universalRead →
                Cont universalRead U idempotenceRead →
                  Cont idempotenceRead R realRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        UnaryHistory universalRead ∧ UnaryHistory idempotenceRead ∧
                          UnaryHistory realRead ∧ Cont F A universalRead ∧
                            Cont universalRead U idempotenceRead ∧
                              Cont idempotenceRead R realRead ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro _fields functorUnary adjunctionUnary universalUnary regularUnary
    functorAdjunction universalIdempotence idempotenceRegular provenancePkg localNamePkg
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed functorUnary adjunctionUnary functorAdjunction
  have idempotenceReadUnary : UnaryHistory idempotenceRead :=
    unary_cont_closed universalReadUnary universalUnary universalIdempotence
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed idempotenceReadUnary regularUnary idempotenceRegular
  exact
    ⟨universalReadUnary, idempotenceReadUnary, realReadUnary, functorAdjunction,
      universalIdempotence, idempotenceRegular, provenancePkg, localNamePkg⟩

end BEDC.Derived.CauchyCompletionAdjunctionTriangleUp
