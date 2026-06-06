import BEDC.Derived.FastCauchySubsequenceUp.NameCertObligations

namespace BEDC.Derived.FastCauchySubsequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchySubsequenceSourceReplayExhaustion [AskSetup] [PackageSetup]
    {S M Q F R W E H C P N modulusRead selectorRead fastRead regularRead sealRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchySubsequenceCarrier S M Q F R W E H C P N bundle pkg ->
      Cont S M modulusRead ->
        Cont modulusRead Q selectorRead ->
          Cont selectorRead F fastRead ->
            Cont fastRead R regularRead ->
              Cont regularRead W sealRead ->
                Cont H C replayRead ->
                  PkgSig bundle replayRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row replayRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont H C replayRead ∧
                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                              PkgSig bundle replayRead pkg)
                        hsame ∧
                      UnaryHistory modulusRead ∧ UnaryHistory selectorRead ∧
                        UnaryHistory fastRead ∧ UnaryHistory regularRead ∧
                          UnaryHistory sealRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier modulusRoute selectorRoute fastRoute regularRoute sealRoute replayRoute
    replayPkg
  obtain ⟨sUnary, mUnary, qUnary, fUnary, rUnary, wUnary, _eUnary, hUnary, cUnary,
    _pUnary, _nUnary, provenancePkg, localNamePkg⟩ := carrier
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed sUnary mUnary modulusRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed modulusUnary qUnary selectorRoute
  have fastUnary : UnaryHistory fastRead :=
    unary_cont_closed selectorUnary fUnary fastRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed fastUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary wUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
              hsame row N ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H C replayRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayRoute, provenancePkg, localNamePkg, replayPkg⟩
  }
  exact
    ⟨cert, modulusUnary, selectorUnary, fastUnary, regularUnary, sealUnary,
      replayUnary⟩

end BEDC.Derived.FastCauchySubsequenceUp
