import BEDC.Derived.BanachAlgebraUp.TasteGate
import BEDC.Derived.BanachAlgebraUp.CompletionProductNonescape
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachAlgebraUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachAlgebraNameCertObligations [AskSetup] [PackageSetup]
    {R N B Q M H C P L productRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory N ->
        UnaryHistory B ->
          UnaryHistory Q ->
            UnaryHistory M ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont R N B ->
                        Cont B Q productRead ->
                          Cont productRead M completionRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle completionRead pkg ->
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row R ∨ hsame row N ∨ hsame row B ∨
                                        hsame row Q ∨ hsame row M ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row L ∨
                                            hsame row completionRead)
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ Cont R N B ∧
                                        PkgSig bundle completionRead pkg)
                                    hsame ∧ UnaryHistory productRead ∧
                                      UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BanachAlgebraUp BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro rUnary nUnary bUnary qUnary mUnary _hUnary _cUnary _pUnary _lUnary
    ringNormRoute productRoute completionRoute _provenancePkg completionPkg
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed bUnary qUnary productRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed productUnary mUnary completionRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row B ∨ hsame row Q ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row L ∨ hsame row completionRead)
          (fun row : BHist =>
            hsame row completionRead ∧ Cont R N B ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionRead
        ⟨hsame_refl completionRead, completionUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr sourceRow.left))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, ringNormRoute, completionPkg⟩
  }
  exact ⟨cert, productUnary, completionUnary⟩

theorem BanachAlgebraPublicExportSurface [AskSetup] [PackageSetup]
    {R N B Q M H C P L productRead completionRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R ->
      UnaryHistory N ->
        UnaryHistory B ->
          UnaryHistory Q ->
            UnaryHistory M ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory L ->
                      Cont R N B ->
                        Cont B Q productRead ->
                          Cont productRead M completionRead ->
                            Cont completionRead L publicRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle L pkg ->
                                  PkgSig bundle publicRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row publicRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row R ∨ hsame row N ∨ hsame row B ∨
                                            hsame row Q ∨ hsame row M ∨ hsame row H ∨
                                              hsame row C ∨ hsame row P ∨ hsame row L ∨
                                                hsame row productRead ∨
                                                  hsame row completionRead ∨
                                                    hsame row publicRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont R N B ∧
                                            Cont B Q productRead ∧
                                              Cont productRead M completionRead ∧
                                                Cont completionRead L publicRead ∧
                                                  PkgSig bundle publicRead pkg)
                                        hsame ∧ UnaryHistory productRead ∧
                                          UnaryHistory completionRead ∧
                                            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BanachAlgebraUp BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro _rUnary _nUnary bUnary qUnary mUnary _hUnary _cUnary _pUnary lUnary
    ringNormRoute productRoute completionRoute publicRoute _provenancePkg _localPkg publicPkg
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed bUnary qUnary productRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed productUnary mUnary completionRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed completionUnary lUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row N ∨ hsame row B ∨ hsame row Q ∨
              hsame row M ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row L ∨ hsame row productRead ∨ hsame row completionRead ∨
                  hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R N B ∧ Cont B Q productRead ∧
              Cont productRead M completionRead ∧ Cont completionRead L publicRead ∧
                PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, ringNormRoute, productRoute, completionRoute, publicRoute,
          publicPkg⟩
  }
  exact ⟨cert, productUnary, completionUnary, publicUnary⟩

theorem BanachAlgebraGelfandSpectrumDependencyBoundary [AskSetup] [PackageSetup]
    {ring norm banach productControl completionSeal transport replay provenance localName
      productRead completionRead spectrumRequest : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BanachAlgebraCarrier ring norm banach productControl completionSeal transport replay
        provenance localName bundle pkg →
      Cont banach productControl productRead →
        Cont productRead completionSeal completionRead →
          Cont completionRead localName spectrumRequest →
            PkgSig bundle spectrumRequest pkg →
              UnaryHistory productRead ∧ UnaryHistory completionRead ∧
                UnaryHistory spectrumRequest ∧ Cont banach productControl productRead ∧
                  Cont productRead completionSeal completionRead ∧
                    Cont completionRead localName spectrumRequest ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle spectrumRequest pkg := by
  -- BEDC touchpoint anchor: BanachAlgebraUp BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier productRoute completionRoute spectrumRoute spectrumPkg
  obtain ⟨_ringUnary, _normUnary, banachUnary, productControlUnary, completionUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _ringNormRoute,
    _completionSealRoute, _replayRoute, provenancePkg⟩ := carrier
  have productUnary : UnaryHistory productRead :=
    unary_cont_closed banachUnary productControlUnary productRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed productUnary completionUnary completionRoute
  have spectrumUnary : UnaryHistory spectrumRequest :=
    unary_cont_closed completionReadUnary localNameUnary spectrumRoute
  exact
    ⟨productUnary, completionReadUnary, spectrumUnary, productRoute, completionRoute,
      spectrumRoute, provenancePkg, spectrumPkg⟩

end BEDC.Derived.BanachAlgebraUp
