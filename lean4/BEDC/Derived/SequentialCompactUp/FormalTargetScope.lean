import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactFormalTargetScope [AskSetup] [PackageSetup]
    {K B S W R E H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont K B S →
        Cont S W R →
          Cont R E publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                      hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row publicRead)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier _compactStream streamRegular regularPublic publicPkg
  obtain ⟨_unaryK, _unaryB, unaryS, _unaryW, unaryR, unaryE, _unaryH, _unaryC,
    _unaryP, _unaryN, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have regularUnary : UnaryHistory R :=
    unary_cont_closed unaryS _unaryW streamRegular
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed regularUnary unaryE regularPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem SequentialCompactFormalTargetRouteCertificate [AskSetup] [PackageSetup]
    {K B S W R E H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K B (append K B) ->
        Cont S W (append S W) ->
          Cont R E publicRead ->
            PkgSig bundle publicRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                      hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row publicRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K B (append K B) ∧
                      Cont S W (append S W) ∧ Cont R E publicRead ∧
                        PkgSig bundle publicRead pkg)
                  hsame ∧
                Cont K B (append K B) ∧ Cont S W (append S W) ∧
                  Cont R E publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute windowRoute publicRoute publicPkg
  obtain ⟨_unaryK, _unaryB, _unaryS, _unaryW, unaryR, unaryE, _unaryH, _unaryC,
    _unaryP, _unaryN, _compactBaireStream, _streamWindowRegular,
      _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed unaryR unaryE publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K B (append K B) ∧ Cont S W (append S W) ∧
              Cont R E publicRead ∧ PkgSig bundle publicRead pkg)
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
      right; right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, compactRoute, windowRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, compactRoute, windowRoute, publicRoute⟩

end BEDC.Derived.SequentialCompactUp
