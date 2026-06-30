import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierKernelScopeDeterminacy [AskSetup] [PackageSetup]
    {sourceA sourceB commonWindow dyadicA dyadicB tolerance readbackA sealRow transport replay
      provenance localName classifierRead sealRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp sourceA commonWindow dyadicA dyadicB tolerance readbackA sealRow
        transport replay provenance localName bundle pkg →
      Cont commonWindow dyadicA classifierRead →
        Cont classifierRead dyadicB sealRead →
          Cont sealRead localName scopedRead →
            PkgSig bundle scopedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
                      hsame row classifierRead ∨ hsame row sealRead ∨
                        hsame row localName ∨ hsame row scopedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont commonWindow dyadicA classifierRead ∧
                      Cont classifierRead dyadicB sealRead ∧
                        Cont sealRead localName scopedRead ∧ PkgSig bundle scopedRead pkg)
                  hsame ∧
                UnaryHistory classifierRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier classifierRoute sealRoute scopedRoute scopedPkg
  have _sourceBReflexive : hsame sourceB sourceB := hsame_refl sourceB
  obtain ⟨_sourceUnary, commonWindowUnary, dyadicAUnary, dyadicBUnary, _toleranceUnary,
    _readbackAUnary, _sealRowUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _sourceWindowReplay, _dyadicToleranceRoute, _toleranceReadbackSeal,
    _transportReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed commonWindowUnary dyadicAUnary classifierRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed classifierUnary dyadicBUnary sealRoute
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed sealReadUnary localNameUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row commonWindow ∨ hsame row dyadicA ∨ hsame row dyadicB ∨
              hsame row classifierRead ∨ hsame row sealRead ∨ hsame row localName ∨
                hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont commonWindow dyadicA classifierRead ∧
              Cont classifierRead dyadicB sealRead ∧
                Cont sealRead localName scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, classifierRoute, sealRoute, scopedRoute, scopedPkg⟩
  }
  exact ⟨cert, classifierUnary, sealReadUnary, scopedUnary⟩

end BEDC.Derived.RealNameClassifierUp
