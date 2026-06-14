import BEDC.Derived.DoubleCauchyDiagonalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DoubleCauchyDiagonalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DoubleCauchyDiagonalCarrier [AskSetup] [PackageSetup]
    (regular windows dyadic diagonal transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory regular ∧ UnaryHistory windows ∧ UnaryHistory dyadic ∧
    UnaryHistory diagonal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont regular windows diagonal ∧
        Cont diagonal dyadic transport ∧ Cont transport route provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem DoubleCauchyDiagonalNamecertObligations [AskSetup] [PackageSetup]
    {regular windows dyadic diagonal transport route provenance localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DoubleCauchyDiagonalCarrier regular windows dyadic diagonal transport route provenance
        localName bundle pkg ->
      Cont windows dyadic endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row regular ∨ hsame row windows ∨ hsame row dyadic ∨
                  hsame row diagonal ∨ hsame row endpoint)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont windows dyadic endpoint ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier endpointRoute endpointPkg
  obtain ⟨_regularUnary, windowsUnary, dyadicUnary, _diagonalUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, _regularWindowRoute,
    _diagonalDyadicRoute, _transportRoute, _provenancePkg, _localNamePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed windowsUnary dyadicUnary endpointRoute
  have endpointSource : hsame endpoint endpoint ∧ UnaryHistory endpoint :=
    ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row regular ∨ hsame row windows ∨ hsame row dyadic ∨
              hsame row diagonal ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont windows dyadic endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointRoute, endpointPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.DoubleCauchyDiagonalUp
