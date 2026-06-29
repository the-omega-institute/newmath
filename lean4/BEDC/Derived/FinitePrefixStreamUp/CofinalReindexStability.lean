import BEDC.Derived.FinitePrefixStreamUp.NameCertObligations

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCofinalReindexStability [AskSetup] [PackageSetup]
    {k W D R H C P N j m sourceCut cutDyadic cutRegular replay : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FinitePrefixStreamCarrier k W D R H C P N →
      UnaryHistory j →
        UnaryHistory m →
          Cont j W sourceCut →
            Cont sourceCut D cutDyadic →
              Cont cutDyadic R cutRegular →
                Cont cutRegular C replay →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row replay ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                                hsame row j ∨ hsame row m ∨ hsame row sourceCut ∨
                                  hsame row cutDyadic ∨ hsame row cutRegular ∨
                                    hsame row replay)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont j W sourceCut ∧
                              Cont sourceCut D cutDyadic ∧ Cont cutDyadic R cutRegular ∧
                                Cont cutRegular C replay ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory sourceCut ∧ UnaryHistory cutDyadic ∧
                          UnaryHistory cutRegular ∧ UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro carrier jUnary _mUnary sourceRoute dyadicRoute regularRoute replayRoute pPkg nPkg
  obtain
    ⟨_kUnary, wUnary, dUnary, rUnary, cUnary, _nUnary, _sameH, _routeH, _routeP,
      _packetRegularRoute⟩ := carrier
  have sourceUnary : UnaryHistory sourceCut :=
    unary_cont_closed jUnary wUnary sourceRoute
  have dyadicUnary : UnaryHistory cutDyadic :=
    unary_cont_closed sourceUnary dUnary dyadicRoute
  have regularUnary : UnaryHistory cutRegular :=
    unary_cont_closed dyadicUnary rUnary regularRoute
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed regularUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replay ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row k ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row j ∨ hsame row m ∨ hsame row sourceCut ∨
                  hsame row cutDyadic ∨ hsame row cutRegular ∨ hsame row replay)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont j W sourceCut ∧ Cont sourceCut D cutDyadic ∧
              Cont cutDyadic R cutRegular ∧ Cont cutRegular C replay ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨replay, hsame_refl replay, replayUnary⟩
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, dyadicRoute, regularRoute, replayRoute, pPkg, nPkg⟩
  }
  exact ⟨cert, sourceUnary, dyadicUnary, regularUnary, replayUnary⟩

end BEDC.Derived.FinitePrefixStreamUp
