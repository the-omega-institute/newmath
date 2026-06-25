import BEDC.Derived.CauchyModulusArithmeticUp

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusArithmeticScopedRoute [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow
      transport replay provenance localName thresholdRead sealRead sumProductRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      Cont meet dyadic thresholdRead ->
        Cont thresholdRead sealRow sealRead ->
          Cont sum product sumProductRead ->
            PkgSig bundle sealRead pkg ->
              PkgSig bundle sumProductRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row window ∨ hsame row dyadic ∨ hsame row readback ∨
                        hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont meet dyadic thresholdRead ∧
                        Cont thresholdRead sealRow sealRead ∧
                          PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory sumProductRead ∧
                    Cont meet dyadic sum ∧ Cont meet dyadic product ∧
                      Cont sum product sumProductRead ∧ PkgSig bundle localName pkg ∧
                        PkgSig bundle sumProductRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier thresholdRoute sealRoute sumProductRoute sealPkg sumProductPkg
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, meetUnary,
      sumUnary, productUnary, dyadicUnary, _windowUnary, _readbackUnary, sealRowUnary,
      _transportUnary, _meetRoute, sumRoute, productRoute, _windowSealRoute,
      _provenanceRoute, localPkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed meetUnary dyadicUnary thresholdRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed thresholdUnary sealRowUnary sealRoute
  have sumProductUnary : UnaryHistory sumProductRead :=
    unary_cont_closed sumUnary productUnary sumProductRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row dyadic ∨ hsame row readback ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont meet dyadic thresholdRead ∧
              Cont thresholdRead sealRow sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, thresholdRoute, sealRoute, sealPkg⟩
  }
  exact
    ⟨cert, sumProductUnary, sumRoute, productRoute, sumProductRoute, localPkg,
      sumProductPkg⟩

end BEDC.Derived.CauchyModulusArithmeticUp
