import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisPublicExport [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N completionBasis limitRoute windowRead readback tolerance
      realSeal publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont Q F completionBasis →
        Cont completionBasis L limitRoute →
          Cont limitRoute W windowRead →
            Cont windowRead R readback →
              Cont readback D tolerance →
                Cont tolerance E realSeal →
                  Cont realSeal N publicRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                                hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row N ∨
                                  hsame row publicRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q F completionBasis ∧
                                Cont completionBasis L limitRoute ∧
                                  Cont limitRoute W windowRead ∧
                                    Cont windowRead R readback ∧
                                      Cont readback D tolerance ∧
                                        Cont tolerance E realSeal ∧
                                          Cont realSeal N publicRead ∧
                                            PkgSig bundle P pkg ∧
                                              PkgSig bundle publicRead pkg)
                            hsame ∧
                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier qf basisLimit limitWindow windowReadRoute readTolerance toleranceSeal
    publicRoute pkgP publicPkg
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, dUnary, eUnary, _hUnary, _cUnary,
      _pUnary, nUnary, _sameHN, _carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionBasis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limitRoute :=
    unary_cont_closed completionUnary lUnary basisLimit
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed limitUnary wUnary limitWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary rUnary windowReadRoute
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed readbackUnary dUnary readTolerance
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed toleranceUnary eUnary toleranceSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary nUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨ hsame row R ∨
              hsame row D ∨ hsame row E ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F completionBasis ∧
              Cont completionBasis L limitRoute ∧ Cont limitRoute W windowRead ∧
                Cont windowRead R readback ∧ Cont readback D tolerance ∧
                  Cont tolerance E realSeal ∧ Cont realSeal N publicRead ∧
                    PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qf, basisLimit, limitWindow, windowReadRoute,
          readTolerance, toleranceSeal, publicRoute, pkgP, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.FilterLimitBasisUp
