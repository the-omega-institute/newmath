import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusArithmeticCarrier [AskSetup] [PackageSetup]
    (stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream0 ∧ UnaryHistory stream1 ∧ UnaryHistory modulus0 ∧
    UnaryHistory modulus1 ∧ UnaryHistory meet ∧ UnaryHistory sum ∧
      UnaryHistory product ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
        UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
            Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧
            Cont meet dyadic product ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg

theorem CauchyModulusArithmeticCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {stream0 stream1 modulus0 modulus1 meet sum product dyadic window readback sealRow transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier stream0 stream1 modulus0 modulus1 meet sum product dyadic
        window readback sealRow transport replay provenance localName bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream0 ∨ hsame row stream1 ∨ hsame row meet ∨ hsame row sum ∨
              hsame row product ∨ hsame row sealRow)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg)
          hsame ∧
        Cont modulus0 modulus1 meet ∧ Cont meet dyadic sum ∧ Cont meet dyadic product ∧
          Cont window readback sealRow ∧ Cont transport replay provenance ∧
            PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier
  obtain
    ⟨_stream0Unary, _stream1Unary, _modulus0Unary, _modulus1Unary, _meetUnary,
      _sumUnary, _productUnary, _dyadicUnary, _windowUnary, _readbackUnary,
      sealUnary, _transportUnary, meetRoute, sumRoute, productRoute, sealRoute,
      provenanceRoute, packageRoute⟩ := carrier
  have sourceAtSeal : hsame sealRow sealRow ∧ UnaryHistory sealRow :=
    ⟨hsame_refl sealRow, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream0 ∨ hsame row stream1 ∨ hsame row meet ∨ hsame row sum ∨
              hsame row product ∨ hsame row sealRow)
          (fun row : BHist =>
            hsame row sealRow ∧ Cont window readback sealRow ∧
              Cont transport replay provenance ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRow sourceAtSeal
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
        have otherSameSeal : hsame _other sealRow :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory _other := by
          cases sameRows
          exact source.right
        exact ⟨otherSameSeal, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealRoute, provenanceRoute, packageRoute⟩
  }
  exact ⟨cert, meetRoute, sumRoute, productRoute, sealRoute, provenanceRoute, packageRoute⟩

end BEDC.Derived.CauchyModulusArithmeticUp
