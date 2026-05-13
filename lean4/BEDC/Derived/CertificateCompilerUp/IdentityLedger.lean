import BEDC.Derived.CertificateCompilerUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerIdentityLedger [AskSetup] [PackageSetup] {source : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} (sourceUnary : UnaryHistory source)
    (sourcePkg : PkgSig bundle source pkg) :
    CertificateCompilerCarrier source source BHist.Empty source BHist.Empty BHist.Empty
        BHist.Empty source bundle pkg ∧
      Cont source BHist.Empty source ∧ Cont BHist.Empty source source ∧
        hsame source (append BHist.Empty source) ∧ PkgSig bundle source pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle Pkg
  have emptyUnary : UnaryHistory BHist.Empty := unary_empty
  have sourceEmptySource : Cont source BHist.Empty source := cont_right_unit source
  have emptySourceSource : Cont BHist.Empty source source := cont_left_unit source
  have sourceMatchesEmptyPrefix : hsame source (append BHist.Empty source) :=
    (append_empty_left source).symm
  have carrier :
      CertificateCompilerCarrier source source BHist.Empty source BHist.Empty BHist.Empty
          BHist.Empty source bundle pkg :=
    ⟨sourceUnary, sourceUnary, emptyUnary, sourceUnary, emptyUnary, emptyUnary, emptyUnary,
      sourceEmptySource, sourceEmptySource, emptySourceSource, sourceMatchesEmptyPrefix,
      sourcePkg⟩
  exact
    ⟨carrier, sourceEmptySource, emptySourceSource, sourceMatchesEmptyPrefix, sourcePkg⟩

end BEDC.Derived.CertificateCompilerUp
