import BEDC.Derived.SequentialCompactUp.ObligationReadiness
import BEDC.Derived.SequentialCompactUp.RootObligationSurface

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactPublicNameCertRoute [AskSetup] [PackageSetup]
    {K B S W R E H C P N compactRead subsequenceRead clusterRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K B compactRead ->
        Cont compactRead S subsequenceRead ->
          Cont subsequenceRead R clusterRead ->
            Cont clusterRead E publicRead ->
              PkgSig bundle publicRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                        hsame row R ∨ hsame row E ∨ hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont K B compactRead ∧
                        Cont compactRead S subsequenceRead ∧
                          Cont subsequenceRead R clusterRead ∧
                            Cont clusterRead E publicRead ∧ PkgSig bundle P pkg ∧
                              PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute subsequenceRoute clusterRoute publicRoute publicPkg
  obtain ⟨kUnary, bUnary, sUnary, _wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, carrierPkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed kUnary bUnary compactRoute
  have subsequenceUnary : UnaryHistory subsequenceRead :=
    unary_cont_closed compactUnary sUnary subsequenceRoute
  have clusterUnary : UnaryHistory clusterRead :=
    unary_cont_closed subsequenceUnary rUnary clusterRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed clusterUnary eUnary publicRoute
  constructor
  · exact {
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
          ⟨source.right, compactRoute, subsequenceRoute, clusterRoute, publicRoute,
            carrierPkg, publicPkg⟩
    }
  · exact publicUnary

theorem SequentialCompactPublicNameCertCarrierRows [AskSetup] [PackageSetup]
    {K B S W R E H C P N namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont S W (append S W) ->
        Cont (append S W) R (append (append S W) R) ->
          Cont (append (append S W) R) E namedRead ->
            PkgSig bundle namedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                      hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row namedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S W (append S W) ∧
                      Cont (append S W) R (append (append S W) R) ∧
                        Cont (append (append S W) R) E namedRead ∧
                          PkgSig bundle namedRead pkg)
                  hsame ∧
                sequentialCompactFields (SequentialCompactUp.mk K B S W R E H C P N) =
                  [K, B, S, W, R, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectedRoute regularRoute namedRoute namedPkg
  obtain ⟨_unaryK, _unaryB, unaryS, unaryW, unaryR, unaryE, _unaryH, _unaryC,
    _unaryP, _unaryN, _compactBaireStream, _streamWindowRegular,
      _regularSealTransport, _transportReplayProvenance, _provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory (append S W) :=
    unary_cont_closed unaryS unaryW selectedRoute
  have regularUnary : UnaryHistory (append (append S W) R) :=
    unary_cont_closed selectedUnary unaryR regularRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed regularUnary unaryE namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
              hsame row R ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W (append S W) ∧
              Cont (append S W) R (append (append S W) R) ∧
                Cont (append (append S W) R) E namedRead ∧ PkgSig bundle namedRead pkg)
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
      right; right; right; right; right; right; right; right; right; right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, selectedRoute, regularRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, rfl⟩

end BEDC.Derived.SequentialCompactUp
