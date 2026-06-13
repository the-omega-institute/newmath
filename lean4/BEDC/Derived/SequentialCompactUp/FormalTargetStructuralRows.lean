import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactFormalTargetStructuralRowsCertificate [AskSetup] [PackageSetup]
    {K B S W R E H C P N structuralRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont H C structuralRead ->
        Cont structuralRead P publicRead ->
          PkgSig bundle publicRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row structuralRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont H C structuralRead ∧
                    Cont structuralRead P publicRead ∧ PkgSig bundle publicRead pkg)
                hsame ∧
              UnaryHistory structuralRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier structuralRoute publicRoute publicPkg
  obtain ⟨_kUnary, _bUnary, _sUnary, _wUnary, _rUnary, _eUnary, hUnary, cUnary,
    pUnary, _nUnary, _compactBaireStream, _streamWindowRegular,
      _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary cUnary structuralRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed structuralUnary pUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row structuralRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont H C structuralRead ∧
              Cont structuralRead P publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, structuralRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, structuralUnary, publicUnary⟩

end BEDC.Derived.SequentialCompactUp
