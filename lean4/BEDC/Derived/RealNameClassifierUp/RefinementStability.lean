import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierRefinementStability [AskSetup] [PackageSetup]
    {sourceA sourceB commonWindow dyadicA dyadicB toleranceA readbackA sealRow transport
      replay provenance localName refinedWindow classifierRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RealNameClassifierUp sourceA commonWindow dyadicA dyadicB toleranceA readbackA
        sealRow transport replay provenance localName bundle pkg →
      Cont commonWindow transport refinedWindow →
        Cont refinedWindow dyadicA classifierRead →
          Cont classifierRead dyadicB sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
                      hsame row transport ∨ hsame row refinedWindow ∨
                        hsame row classifierRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont commonWindow transport refinedWindow ∧
                      Cont refinedWindow dyadicA classifierRead ∧
                        Cont classifierRead dyadicB sealRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory refinedWindow ∧ UnaryHistory classifierRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowTransportRefined refinedDyadicClassifier classifierDyadicSeal sealPkg
  have _sourceBReflexive : hsame sourceB sourceB := hsame_refl sourceB
  obtain ⟨_sourceUnary, commonWindowUnary, dyadicAUnary, dyadicBUnary,
    _toleranceAUnary, _readbackAUnary, _sealUnary, transportUnary, _replayUnary,
    _provenanceUnary, _localNameUnary, _sourceWindowReplay, _dyadicToleranceRoute,
    _toleranceSealRoute, _transportReplaySame, provenancePkg, _localNamePkg⟩ := carrier
  have refinedUnary : UnaryHistory refinedWindow :=
    unary_cont_closed commonWindowUnary transportUnary windowTransportRefined
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed refinedUnary dyadicAUnary refinedDyadicClassifier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary dyadicBUnary classifierDyadicSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
              hsame row transport ∨ hsame row refinedWindow ∨ hsame row classifierRead ∨
                hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonWindow transport refinedWindow ∧
              Cont refinedWindow dyadicA classifierRead ∧
                Cont classifierRead dyadicB sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowTransportRefined, refinedDyadicClassifier,
          classifierDyadicSeal, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, refinedUnary, classifierUnary, sealReadUnary⟩

end BEDC.Derived.RealNameClassifierUp
