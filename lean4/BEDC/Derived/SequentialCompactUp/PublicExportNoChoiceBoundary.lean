import BEDC.Derived.SequentialCompactUp.RootObligationSurface

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactPublicExportNoChoiceBoundary [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectedRead regularRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont W R selectedRead →
        Cont selectedRead E regularRead →
          Cont regularRead N sealRead →
            Cont sealRead P publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                        hsame row R ∨ hsame row E ∨ hsame row N ∨ hsame row P ∨
                          hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W R selectedRead ∧
                        Cont selectedRead E regularRead ∧
                          Cont regularRead N sealRead ∧
                            Cont sealRead P publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectedRoute regularRoute sealRoute publicRoute publicPkg
  obtain ⟨_unaryK, _unaryB, _unaryS, unaryW, unaryR, unaryE, _unaryH, _unaryC,
    unaryP, unaryN, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed unaryW unaryR selectedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary unaryE regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryN sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary unaryP publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row N ∨ hsame row P ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R selectedRead ∧
              Cont selectedRead E regularRead ∧ Cont regularRead N sealRead ∧
                Cont sealRead P publicRead ∧ PkgSig bundle publicRead pkg)
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedRoute, regularRoute, sealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, publicUnary⟩

end BEDC.Derived.SequentialCompactUp
