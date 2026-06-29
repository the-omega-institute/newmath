import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierBridgeRoute [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName swappedSeal composedSeal sharedRead closureRead bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont dyadic rat tolerance →
        Cont tolerance refinement swappedSeal →
          Cont swappedSeal sealRow composedSeal →
            Cont composedSeal localName sharedRead →
              Cont sharedRead provenance closureRead →
                Cont closureRead sealRow bridgeRead →
                  PkgSig bundle bridgeRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row source ∨ hsame row stream ∨ hsame row rat ∨
                            hsame row dyadic ∨ hsame row tolerance ∨ hsame row swappedSeal ∨
                              hsame row composedSeal ∨ hsame row sharedRead ∨
                                hsame row closureRead ∨ hsame row bridgeRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont dyadic rat tolerance ∧
                            Cont tolerance refinement swappedSeal ∧
                              Cont swappedSeal sealRow composedSeal ∧
                                Cont composedSeal localName sharedRead ∧
                                  Cont sharedRead provenance closureRead ∧
                                    Cont closureRead sealRow bridgeRead ∧
                                      PkgSig bundle bridgeRead pkg)
                        hsame ∧
                      UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier dyadicRatRoute swappedSealRoute composedSealRoute sharedReadRoute
    closureRoute bridgeRoute bridgePkg
  obtain ⟨_sourceUnary, _streamUnary, ratUnary, dyadicUnary, _toleranceUnary,
    refinementUnary, sealUnary, _transportUnary, _replayUnary, provenanceUnary,
    localNameUnary, _sourceStreamReplay, _ratDyadicTolerance, _toleranceRefinementSeal,
    _transportReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory tolerance :=
    unary_cont_closed dyadicUnary ratUnary dyadicRatRoute
  have swappedUnary : UnaryHistory swappedSeal :=
    unary_cont_closed toleranceUnary refinementUnary swappedSealRoute
  have composedUnary : UnaryHistory composedSeal :=
    unary_cont_closed swappedUnary sealUnary composedSealRoute
  have sharedUnary : UnaryHistory sharedRead :=
    unary_cont_closed composedUnary localNameUnary sharedReadRoute
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed sharedUnary provenanceUnary closureRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed closureUnary sealUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row swappedSeal ∨ hsame row composedSeal ∨
                hsame row sharedRead ∨ hsame row closureRead ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic rat tolerance ∧
              Cont tolerance refinement swappedSeal ∧ Cont swappedSeal sealRow composedSeal ∧
                Cont composedSeal localName sharedRead ∧
                  Cont sharedRead provenance closureRead ∧
                    Cont closureRead sealRow bridgeRead ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead ⟨hsame_refl bridgeRead, bridgeUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceData.left))))))))
    ledger_sound := by
      intro _row sourceData
      exact
        ⟨sourceData.right, dyadicRatRoute, swappedSealRoute, composedSealRoute,
          sharedReadRoute, closureRoute, bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.RealNameClassifierUp
