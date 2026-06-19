import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisWindowBasisExhaustion [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N basis limit window readback tolerance realSeal localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont Q F basis →
        Cont basis L limit →
          Cont limit W window →
            Cont window R readback →
              Cont readback D tolerance →
                Cont tolerance E realSeal →
                  Cont H C localRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle localRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
                                hsame row R ∨ hsame row D ∨ hsame row E ∨
                                  hsame row basis ∨ hsame row limit ∨ hsame row window ∨
                                    hsame row readback ∨ hsame row tolerance ∨
                                      hsame row realSeal ∨ hsame row localRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont Q F basis ∧ Cont basis L limit ∧
                                Cont limit W window ∧ Cont window R readback ∧
                                  Cont readback D tolerance ∧ Cont tolerance E realSeal ∧
                                    Cont H C localRead ∧ PkgSig bundle P pkg ∧
                                      PkgSig bundle localRead pkg)
                            hsame ∧
                          UnaryHistory basis ∧ UnaryHistory limit ∧ UnaryHistory window ∧
                            UnaryHistory readback ∧ UnaryHistory tolerance ∧
                              UnaryHistory realSeal ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier qf basisLimit limitWindow windowRead readTolerance toleranceSeal
    hc pkgP pkgLocal
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, dUnary, eUnary, hUnary, cUnary,
      _pUnary, _nUnary, _sameHN, _carrierPkg⟩ := carrier
  have basisUnary : UnaryHistory basis :=
    unary_cont_closed qUnary fUnary qf
  have limitUnary : UnaryHistory limit :=
    unary_cont_closed basisUnary lUnary basisLimit
  have windowUnary : UnaryHistory window :=
    unary_cont_closed limitUnary wUnary limitWindow
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed windowUnary rUnary windowRead
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed readbackUnary dUnary readTolerance
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed toleranceUnary eUnary toleranceSeal
  have localReadUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary hc
  have sourceSeal :
      (fun row : BHist => hsame row realSeal ∧ UnaryHistory row) realSeal := by
    exact ⟨hsame_refl realSeal, realSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Q ∨ hsame row F ∨ hsame row L ∨ hsame row W ∨
              hsame row R ∨ hsame row D ∨ hsame row E ∨ hsame row basis ∨
                hsame row limit ∨ hsame row window ∨ hsame row readback ∨
                  hsame row tolerance ∨ hsame row realSeal ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Q F basis ∧ Cont basis L limit ∧
              Cont limit W window ∧ Cont window R readback ∧
                Cont readback D tolerance ∧ Cont tolerance E realSeal ∧
                  Cont H C localRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal sourceSeal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, qf, basisLimit, limitWindow, windowRead, readTolerance,
          toleranceSeal, hc, pkgP, pkgLocal⟩
  }
  exact
    ⟨cert, basisUnary, limitUnary, windowUnary, readbackUnary, toleranceUnary,
      realSealUnary, localReadUnary⟩

end BEDC.Derived.FilterLimitBasisUp
