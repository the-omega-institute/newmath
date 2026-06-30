import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticCarrier_diagonal_meet_stability
    [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg →
      Cont meet meet diagonalRead →
        PkgSig bundle diagonalRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row meet ∨ hsame row dyadic ∨ hsame row sum ∨ hsame row product ∨
                  hsame row diagonalRead ∨ Cont meet meet diagonalRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                  PkgSig bundle diagonalRead pkg)
              hsame ∧ UnaryHistory meet ∧ UnaryHistory diagonalRead ∧
            Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧
          Cont meet dyadic product ∧ Cont meet meet diagonalRead := by
  -- BEDC touchpoint anchor: CauchyModulusArithmeticCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier diagonalRoute diagonalPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      _sumUnary, _productUnary, _dyadicUnary, _windowUnary, _readbackUnary,
      _sealUnary, _transportUnary, meetRoute, sumRoute, productRoute, _sealRoute,
      _provenanceRoute, localPackage⟩ := carrier
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed meetUnary meetUnary diagonalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row diagonalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row meet ∨ hsame row dyadic ∨ hsame row sum ∨ hsame row product ∨
              hsame row diagonalRead ∨ Cont meet meet diagonalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧
              PkgSig bundle diagonalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro diagonalRead ⟨hsame_refl diagonalRead, diagonalUnary⟩
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
      right
      right
      right
      right
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, localPackage, diagonalPkg⟩
  }
  exact
    ⟨cert, meetUnary, diagonalUnary, meetRoute, sumRoute, productRoute,
      diagonalRoute⟩

end BEDC.Derived.CauchyModulusArithmeticUp
