import BEDC.Derived.AuthorizedGeneratorRecursorUp.L10Carrier

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursorPublicConsumerBoundary [AskSetup] [PackageSetup]
    {I E M B D O A H C P G N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuthorizedGeneratorRecursorCarrier I E M B D O A H C P G N bundle pkg ->
      Cont O C publicRead ->
        PkgSig bundle publicRead pkg ->
          UnaryHistory I ∧ UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory B ∧
            UnaryHistory D ∧ UnaryHistory O ∧ UnaryHistory A ∧ UnaryHistory C ∧
              UnaryHistory publicRead ∧ Cont I E M ∧ Cont M B D ∧ Cont D O A ∧
                Cont O C publicRead ∧ hsame H (append A C) ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier outputPublic publicPkg
  obtain ⟨iUnary, eUnary, mUnary, bUnary, dUnary, oUnary, aUnary, _hUnary, cUnary,
    _pUnary, _gUnary, _nUnary, iEM, mBD, dOA, hAC, pPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed oUnary cUnary outputPublic
  exact
    ⟨iUnary, eUnary, mUnary, bUnary, dUnary, oUnary, aUnary, cUnary,
      publicReadUnary, iEM, mBD, dOA, outputPublic, hAC, pPkg, publicPkg⟩

end BEDC.Derived.AuthorizedGeneratorRecursorUp
