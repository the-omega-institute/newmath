import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ConcaveModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ConcaveModulusCarrier [AskSetup] [PackageSetup]
    (modulus left right midpoint bound transport route provenance localName
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig
  UnaryHistory modulus ∧ UnaryHistory left ∧ UnaryHistory right ∧
    UnaryHistory midpoint ∧ UnaryHistory bound ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        UnaryHistory endpoint ∧ Cont left right midpoint ∧ Cont midpoint bound endpoint ∧
          Cont transport route provenance ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle endpoint pkg

theorem ConcaveModulusCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {modulus left right midpoint bound transport route provenance localName
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ConcaveModulusCarrier modulus left right midpoint bound transport route provenance
        localName endpoint bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            ConcaveModulusCarrier modulus left right midpoint bound transport route
              provenance localName endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist => hsame row midpoint ∨ hsame row bound ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro carrier
  have carrierWitness := carrier
  obtain ⟨_modulusUnary, _leftUnary, _rightUnary, _midpointUnary, _boundUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary, _endpointUnary,
    _leftRightMidpoint, _midpointBoundEndpoint, _transportRouteProvenance,
    _provenancePkg, endpointPkg⟩ := carrier
  have sourceEndpoint :
      (fun row : BHist =>
        ConcaveModulusCarrier modulus left right midpoint bound transport route
          provenance localName endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact ⟨carrierWitness, hsame_refl endpoint⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.right)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }

end BEDC.Derived.ConcaveModulusUp
