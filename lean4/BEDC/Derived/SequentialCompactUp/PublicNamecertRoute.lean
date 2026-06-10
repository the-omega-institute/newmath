import BEDC.Derived.SequentialCompactUp.RootObligationSurface

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactPublicNamecertRoute [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectedRead regularRead sealRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont S W selectedRead ->
        Cont selectedRead R regularRead ->
          Cont regularRead E sealRead ->
            Cont sealRead N namedRead ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                        hsame row N ∨ hsame row selectedRead ∨
                          hsame row regularRead ∨ hsame row sealRead ∨
                            hsame row namedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S W selectedRead ∧
                        Cont selectedRead R regularRead ∧
                          Cont regularRead E sealRead ∧
                            Cont sealRead N namedRead ∧
                              PkgSig bundle namedRead pkg)
                    hsame ∧
                  UnaryHistory selectedRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectedRoute regularRoute sealRoute namedRoute namedPkg
  obtain ⟨_unaryK, _unaryB, unaryS, unaryW, unaryR, unaryE, _unaryH, _unaryC,
    _unaryP, unaryN, _compactBaireStream, _streamWindowRegular,
      _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed unaryS unaryW selectedRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary unaryR regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryE sealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
              hsame row N ∨ hsame row selectedRead ∨ hsame row regularRead ∨
                hsame row sealRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W selectedRead ∧
              Cont selectedRead R regularRead ∧ Cont regularRead E sealRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectedRoute, regularRoute, sealRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, selectedUnary, regularUnary, sealUnary, namedUnary⟩

end BEDC.Derived.SequentialCompactUp
