import BEDC.Derived.SequentialCompactUp.StandardBridgeScope

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactMaturePublicBridgePackage [AskSetup] [PackageSetup]
    {K B S W R E H C P N compactRead streamRead windowRead regularRead sealRead publicRead
      bridgeRead matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K B compactRead ->
        Cont B S streamRead ->
          Cont streamRead W windowRead ->
            Cont windowRead R regularRead ->
              Cont regularRead E sealRead ->
                Cont sealRead N publicRead ->
                  Cont publicRead P bridgeRead ->
                    Cont bridgeRead N matureRead ->
                      PkgSig bundle matureRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                                hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                                  hsame row P ∨ hsame row N ∨ hsame row matureRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle matureRead pkg)
                            hsame ∧ UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute streamRoute windowRoute regularRoute sealRoute publicRoute
    bridgeRoute matureRoute maturePkg
  obtain ⟨unaryK, unaryB, unaryS, unaryW, unaryR, unaryE, _unaryH, _unaryC,
    unaryP, unaryN, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryB compactRoute
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed unaryB unaryS streamRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary unaryW windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary unaryR regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary unaryE sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary unaryN publicRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicUnary unaryP bridgeRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed bridgeUnary unaryN matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row matureRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle matureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
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
      exact ⟨source.right, maturePkg⟩
  }
  exact ⟨cert, matureUnary⟩

end BEDC.Derived.SequentialCompactUp
