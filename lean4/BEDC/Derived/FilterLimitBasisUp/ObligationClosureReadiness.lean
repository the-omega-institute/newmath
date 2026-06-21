import BEDC.Derived.FilterLimitBasisUp.TasteGate

namespace BEDC.Derived.FilterLimitBasisUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FilterLimitBasisObligationClosureReadiness [AskSetup] [PackageSetup]
    {Q F L W R D E H C P N closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FilterLimitBasisCarrier Q F L W R D E H C P N bundle pkg →
      Cont C N closureRead →
        PkgSig bundle closureRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row closureRead ∨ hsame row Q ∨ hsame row F ∨ hsame row L ∨
                  hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N closureRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle closureRead pkg)
              hsame ∧
            UnaryHistory closureRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier cn pkgClosure
  obtain
    ⟨qUnary, fUnary, lUnary, wUnary, rUnary, dUnary, eUnary, _hUnary, cUnary,
      _pUnary, nUnary, _sameHN, carrierPkg⟩ := carrier
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed cUnary nUnary cn
  have sourceClosure :
      (fun row : BHist => hsame row closureRead ∧ UnaryHistory row) closureRead := by
    exact ⟨hsame_refl closureRead, closureUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row closureRead ∨ hsame row Q ∨ hsame row F ∨ hsame row L ∨
              hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row E)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N closureRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle closureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro closureRead sourceClosure
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, cn, carrierPkg, pkgClosure⟩
  }
  exact ⟨cert, closureUnary⟩

end BEDC.Derived.FilterLimitBasisUp
