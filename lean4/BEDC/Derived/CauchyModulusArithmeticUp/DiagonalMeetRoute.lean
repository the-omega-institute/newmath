import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticDiagonalMeetRoute [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName pairedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet window pairedRead ->
        Cont pairedRead sealRow sealRead ->
          PkgSig bundle sealRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row sum ∨
                      hsame row product ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont meet window pairedRead ∧
                    Cont pairedRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory pairedRead ∧ UnaryHistory sealRead ∧ Cont meet dyadic sum ∧
                Cont meet dyadic product ∧ Cont window readback sealRow ∧
                  PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier pairedRoute sealRoute sealPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      _sumUnary, _productUnary, _dyadicUnary, windowUnary, _readbackUnary, sealUnary,
      _transportUnary, _meetRoute, sumRoute, productRoute, windowReadbackSeal,
      _provenanceRoute, localPackage⟩ := carrier
  have pairedUnary : UnaryHistory pairedRead :=
    unary_cont_closed meetUnary windowUnary pairedRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed pairedUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row meet ∨ hsame row window ∨ hsame row dyadic ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row sum ∨
                hsame row product ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont meet window pairedRead ∧
              Cont pairedRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead
        ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pairedRoute, sealRoute, sealPkg⟩
  }
  exact
    ⟨cert, pairedUnary, sealReadUnary, sumRoute, productRoute, windowReadbackSeal,
      localPackage⟩

end BEDC.Derived.CauchyModulusArithmeticUp
