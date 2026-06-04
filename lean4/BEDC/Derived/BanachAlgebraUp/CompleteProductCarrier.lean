import BEDC.Derived.BanachAlgebraUp.CompletionProductNonescape
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachAlgebraCompleteProductCarrier [AskSetup] [PackageSetup]
    {ring norm banach productControl completionSeal transport replay provenance localName
      productRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachAlgebraCarrier ring norm banach productControl completionSeal transport replay
        provenance localName bundle pkg →
      Cont banach productControl productRead →
        PkgSig bundle productRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row productRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row ring ∨ hsame row norm ∨ hsame row banach ∨
                  hsame row productControl ∨ hsame row productRead ∨
                    hsame row completionSeal)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont ring norm banach ∧
                  Cont banach productControl productRead ∧
                    PkgSig bundle productRead pkg ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory productRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig SemanticNameCert hsame
  intro carrier banachProductRoute productPkg
  obtain ⟨_ringUnary, _normUnary, banachUnary, productControlUnary, _completionSealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, ringNormRoute,
    _completionRoute, _replayRoute, provenancePkg⟩ := carrier
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed banachUnary productControlUnary banachProductRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row productRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row ring ∨ hsame row norm ∨ hsame row banach ∨
              hsame row productControl ∨ hsame row productRead ∨
                hsame row completionSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont ring norm banach ∧
              Cont banach productControl productRead ∧ PkgSig bundle productRead pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro productRead ⟨hsame_refl productRead, productUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ringNormRoute, banachProductRoute, productPkg, provenancePkg⟩
  }
  exact ⟨cert, productUnary, provenancePkg⟩

end BEDC.Derived.BanachAlgebraUp
