import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisCofinalSubbasisScope [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N subbasis generatedBase cauchyRow limitRoute streamRead ratRead
      dyadicRead terminalSeal localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg ->
      Cont Q F subbasis ->
        Cont subbasis W generatedBase ->
          Cont generatedBase F cauchyRow ->
            Cont cauchyRow L limitRoute ->
              Cont limitRoute W streamRead ->
                Cont streamRead R ratRead ->
                  Cont ratRead D dyadicRead ->
                    Cont dyadicRead E terminalSeal ->
                      Cont H C localRead ->
                        PkgSig bundle P pkg ->
                          PkgSig bundle N pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                                    hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row terminalSeal)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont Q F subbasis ∧
                                    Cont subbasis W generatedBase ∧
                                      Cont generatedBase F cauchyRow ∧
                                        Cont cauchyRow L limitRoute ∧
                                          Cont dyadicRead E terminalSeal ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                hsame ∧
                              UnaryHistory subbasis ∧ UnaryHistory generatedBase ∧
                                UnaryHistory cauchyRow ∧ UnaryHistory limitRoute ∧
                                  UnaryHistory terminalSeal := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier routeSubbasis routeGenerated routeCauchy routeLimit routeStream routeRat
    routeDyadic routeTerminal _routeLocal pkgP pkgN
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, dUnary, eUnary, _hUnary, _cUnary,
      _pUnary, _nUnary, _sameHN, _carrierPkg⟩ := carrier
  have subbasisUnary : UnaryHistory subbasis :=
    unary_cont_closed qUnary fUnary routeSubbasis
  have generatedUnary : UnaryHistory generatedBase :=
    unary_cont_closed subbasisUnary wUnary routeGenerated
  have cauchyUnary : UnaryHistory cauchyRow :=
    unary_cont_closed generatedUnary fUnary routeCauchy
  have limitUnary : UnaryHistory limitRoute :=
    unary_cont_closed cauchyUnary lUnary routeLimit
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed limitUnary wUnary routeStream
  have ratUnary : UnaryHistory ratRead :=
    unary_cont_closed streamUnary rUnary routeRat
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed ratUnary dUnary routeDyadic
  have terminalUnary : UnaryHistory terminalSeal :=
    unary_cont_closed dyadicUnary eUnary routeTerminal
  have sourceTerminal :
      (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row) terminalSeal := by
    exact ⟨hsame_refl terminalSeal, terminalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row terminalSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F subbasis ∧ Cont subbasis W generatedBase ∧
              Cont generatedBase F cauchyRow ∧ Cont cauchyRow L limitRoute ∧
                Cont dyadicRead E terminalSeal ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalSeal sourceTerminal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeSubbasis, routeGenerated, routeCauchy, routeLimit,
          routeTerminal, pkgP, pkgN⟩
  }
  exact ⟨cert, subbasisUnary, generatedUnary, cauchyUnary, limitUnary, terminalUnary⟩

end BEDC.Derived.FilterLimitBasisUp
