import BEDC.Derived.ClosedboundedintervalUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedboundedintervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ClosedBoundedIntervalDensityLedger [AskSetup] [PackageSetup]
    (lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName meshRead densityRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory rational ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory readback ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont lower upper order ∧
          Cont order rational dyadic ∧ Cont dyadic stream meshRead ∧
            Cont meshRead readback densityRead ∧ Cont transport replay provenance ∧
              PkgSig bundle densityRead pkg

theorem ClosedBoundedIntervalDensityLedger_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {lower upper order rational dyadic stream readback sealRow transport replay provenance
      localName meshRead densityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedBoundedIntervalDensityLedger lower upper order rational dyadic stream readback
        sealRow transport replay provenance localName meshRead densityRead bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            ClosedBoundedIntervalDensityLedger lower upper order rational dyadic stream
              readback sealRow transport replay provenance localName meshRead densityRead bundle
              pkg ∧ hsame row densityRead)
          (fun row : BHist => hsame row densityRead)
          (fun row : BHist => hsame row densityRead ∧ PkgSig bundle densityRead pkg)
          hsame ∧
        UnaryHistory meshRead ∧ UnaryHistory densityRead ∧
          PkgSig bundle densityRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger
  have ledgerAll := ledger
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _rationalUnary, dyadicUnary, streamUnary,
    readbackUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _endpointRoute, _containmentRoute, meshRoute, densityRoute,
    _replayRoute, densityPkg⟩ := ledger
  have meshUnary : UnaryHistory meshRead :=
    unary_cont_closed dyadicUnary streamUnary meshRoute
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed meshUnary readbackUnary densityRoute
  have source :
      (fun row : BHist =>
        ClosedBoundedIntervalDensityLedger lower upper order rational dyadic stream readback
          sealRow transport replay provenance localName meshRead densityRead bundle pkg ∧
            hsame row densityRead) densityRead := by
    exact ⟨ledgerAll, hsame_refl densityRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ClosedBoundedIntervalDensityLedger lower upper order rational dyadic stream
              readback sealRow transport replay provenance localName meshRead densityRead bundle
              pkg ∧ hsame row densityRead)
          (fun row : BHist => hsame row densityRead)
          (fun row : BHist => hsame row densityRead ∧ PkgSig bundle densityRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro densityRead source
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
        intro _row _other sameRows rowSource
        exact
          ⟨rowSource.left, hsame_trans (hsame_symm sameRows) rowSource.right⟩
    }
    pattern_sound := by
      intro _row rowSource
      exact rowSource.right
    ledger_sound := by
      intro _row rowSource
      exact ⟨rowSource.right, densityPkg⟩
  }
  exact ⟨cert, meshUnary, densityUnary, densityPkg⟩

end BEDC.Derived.ClosedboundedintervalUp
