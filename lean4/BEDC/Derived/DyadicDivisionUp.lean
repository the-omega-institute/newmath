import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicDivisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicDivisionCarrier [AskSetup] [PackageSetup]
    (numerator denominator guard reciprocal quotient readback transport route provenance
      namecert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory numerator ∧ UnaryHistory denominator ∧ UnaryHistory guard ∧
    UnaryHistory reciprocal ∧ UnaryHistory quotient ∧ UnaryHistory readback ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory namecert ∧ Cont denominator guard reciprocal ∧
          Cont numerator reciprocal quotient ∧ Cont quotient readback provenance ∧
            hsame namecert readback ∧ PkgSig bundle provenance pkg

theorem DyadicDivisionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {numerator denominator guard reciprocal quotient readback transport route provenance
      namecert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicDivisionCarrier numerator denominator guard reciprocal quotient readback transport route
        provenance namecert bundle pkg ->
      SemanticNameCert
        (fun row : BHist => hsame row namecert ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row numerator ∨ hsame row denominator ∨ hsame row guard ∨
            hsame row reciprocal ∨ hsame row quotient ∨ hsame row readback)
        (fun row : BHist => hsame row namecert ∧ PkgSig bundle provenance pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨numeratorUnary, denominatorUnary, guardUnary, reciprocalUnary, quotientUnary,
    readbackUnary, _transportUnary, _routeUnary, _provenanceUnary, namecertUnary,
    _denominatorGuard, _numeratorReciprocal, _quotientReadback, sameNamecertReadback,
    provenancePkg⟩ := carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro namecert ⟨hsame_refl namecert, namecertUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr (hsame_trans source.left sameNamecertReadback)))))
    ledger_sound := by
      intro row source
      exact ⟨source.left, provenancePkg⟩
  }

end BEDC.Derived.DyadicDivisionUp
