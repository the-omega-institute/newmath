import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BezoutIdentityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BezoutIdentityCarrier [AskSetup] [PackageSetup]
    (g a b x y trace divBoundary transport replay provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory g ∧ UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory x ∧
    UnaryHistory y ∧ UnaryHistory trace ∧ UnaryHistory divBoundary ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem BezoutIdentityCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {g a b x y trace divBoundary transport replay provenance name endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BezoutIdentityCarrier g a b x y trace divBoundary transport replay provenance name
        bundle pkg ->
      Cont trace divBoundary endpoint ->
        PkgSig bundle provenance pkg ->
          PkgSig bundle name pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row g ∨ hsame row a ∨ hsame row b ∨ hsame row x ∨
                    hsame row y ∨ hsame row trace ∨ hsame row divBoundary ∨
                      hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                        hsame row name ∨ hsame row endpoint)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont trace divBoundary endpoint ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
                hsame ∧ UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier replayRoute provenancePkg namePkg
  obtain ⟨_gUnary, _aUnary, _bUnary, _xUnary, _yUnary, traceUnary, divUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed traceUnary divUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row g ∨ hsame row a ∨ hsame row b ∨ hsame row x ∨ hsame row y ∨
              hsame row trace ∨ hsame row divBoundary ∨ hsame row transport ∨
                hsame row replay ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont trace divBoundary endpoint ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.BezoutIdentityUp
