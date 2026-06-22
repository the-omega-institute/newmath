import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisCarrier_public_export [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N completionBasis limitRoute windowRead regularRead
      toleranceRead realSeal localRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg ->
      Cont Q F completionBasis ->
        Cont completionBasis L limitRoute ->
          Cont Q W windowRead ->
            Cont windowRead R regularRead ->
              Cont regularRead D toleranceRead ->
                Cont toleranceRead E realSeal ->
                  Cont H C localRead ->
                    Cont realSeal localRead publicRead ->
                      PkgSig bundle P pkg ->
                        PkgSig bundle publicRead pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                                  hsame row R ∨ hsame row D ∨ hsame row E ∨
                                    hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont Q F completionBasis ∧
                                  Cont completionBasis L limitRoute ∧
                                    Cont Q W windowRead ∧
                                      Cont windowRead R regularRead ∧
                                        Cont regularRead D toleranceRead ∧
                                          Cont toleranceRead E realSeal ∧
                                            Cont realSeal localRead publicRead ∧
                                              PkgSig bundle publicRead pkg)
                              hsame ∧
                            UnaryHistory completionBasis ∧ UnaryHistory limitRoute ∧
                              UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                                UnaryHistory toleranceRead ∧ UnaryHistory realSeal ∧
                                  UnaryHistory localRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: FilterLimitBasisCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qf completionLimit qWindow windowRegular regularTolerance toleranceReal
    hc realLocal pkgP publicPkg
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, dUnary, eUnary, hUnary, cUnary,
      _pUnary, _nUnary, _sameHN, _carrierPkg⟩ := carrier
  have completionUnary : UnaryHistory completionBasis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limitRoute :=
    unary_cont_closed completionUnary lUnary completionLimit
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed qUnary wUnary qWindow
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary windowRegular
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed regularUnary dUnary regularTolerance
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed toleranceUnary eUnary toleranceReal
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary hc
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed realUnary localUnary realLocal
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F completionBasis ∧
              Cont completionBasis L limitRoute ∧ Cont Q W windowRead ∧
                Cont windowRead R regularRead ∧ Cont regularRead D toleranceRead ∧
                  Cont toleranceRead E realSeal ∧ Cont realSeal localRead publicRead ∧
                    PkgSig bundle publicRead pkg)
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qf, completionLimit, qWindow, windowRegular, regularTolerance,
          toleranceReal, realLocal, publicPkg⟩
  }
  exact
    ⟨cert, completionUnary, limitUnary, windowUnary, regularUnary, toleranceUnary,
      realUnary, localUnary, publicUnary⟩

end BEDC.Derived.FilterLimitBasisUp
