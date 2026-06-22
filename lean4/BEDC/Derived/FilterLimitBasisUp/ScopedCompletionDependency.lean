import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisScopedCompletionDependency [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N windowRead regularRead toleranceRead realSeal sealedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont Q W windowRead →
        Cont windowRead R regularRead →
          Cont regularRead D toleranceRead →
            Cont toleranceRead E realSeal →
              Cont realSeal N sealedRead →
                PkgSig bundle P pkg →
                  PkgSig bundle sealedRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                            hsame row E ∨ hsame row N ∨ hsame row sealedRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont Q W windowRead ∧
                            Cont windowRead R regularRead ∧
                              Cont regularRead D toleranceRead ∧
                                Cont toleranceRead E realSeal ∧
                                  Cont realSeal N sealedRead ∧
                                    PkgSig bundle P pkg ∧
                                      PkgSig bundle sealedRead pkg)
                        hsame ∧
                      UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: FilterLimitBasisCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qWindow windowRegular regularTolerance toleranceReal realSealed pkgP
    pkgSealed
  obtain
    ⟨qUnary, _fUnary, _lUnary, wUnary, rUnary, dUnary, eUnary, _hUnary, _cUnary,
      _pUnary, nUnary, _sameHN, _carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed qUnary wUnary qWindow
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary windowRegular
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed regularUnary dUnary regularTolerance
  have realUnary : UnaryHistory realSeal :=
    unary_cont_closed toleranceUnary eUnary toleranceReal
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed realUnary nUnary realSealed
  have sourceSealed :
      (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row) sealedRead := by
    exact ⟨hsame_refl sealedRead, sealedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row E ∨ hsame row N ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q W windowRead ∧
              Cont windowRead R regularRead ∧ Cont regularRead D toleranceRead ∧
                Cont toleranceRead E realSeal ∧ Cont realSeal N sealedRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead sourceSealed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qWindow, windowRegular, regularTolerance, toleranceReal,
          realSealed, pkgP, pkgSealed⟩
  }
  exact ⟨cert, sealedUnary⟩

end BEDC.Derived.FilterLimitBasisUp
