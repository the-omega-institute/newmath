import BEDC.Derived.QuasiMetricUp

namespace BEDC.Derived.QuasiMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuasiMetricCarrier_completion_consumer_nonescape [AskSetup] [PackageSetup]
    {source points distance zero triangle ball filter net uniformReflection transport replay
      provenance localName ballRead completionRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuasiMetricCarrier source points distance zero triangle ball filter net uniformReflection
        transport replay provenance localName bundle pkg ->
      Cont triangle ball ballRead ->
        Cont ball uniformReflection completionRead ->
          Cont completionRead transport namedRead ->
            PkgSig bundle completionRead pkg ->
              PkgSig bundle namedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row distance ∨ hsame row triangle ∨ hsame row ball ∨
                        hsame row filter ∨ hsame row net ∨ hsame row uniformReflection ∨
                          hsame row completionRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont triangle ball ballRead ∧
                        Cont ball uniformReflection completionRead ∧
                          PkgSig bundle completionRead pkg)
                    hsame ∧
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row distance ∨ hsame row triangle ∨ hsame row ball ∨
                          hsame row uniformReflection ∨ hsame row transport ∨
                            hsame row completionRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont triangle ball ballRead ∧
                          Cont ball uniformReflection completionRead ∧
                            Cont completionRead transport namedRead ∧
                              PkgSig bundle namedRead pkg)
                      hsame ∧
                    UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier triangleBallRead ballUniformRead completionTransportRead completionPkg namedPkg
  have boundary :=
    QuasiMetricCarrier_nonescape carrier triangleBallRead ballUniformRead completionPkg
  obtain ⟨completionCert, _distanceUnary, _triangleUnary, _ballReadUnary,
    completionReadUnary⟩ := boundary
  obtain ⟨_sourceUnary, _pointsUnary, _zeroUnary, _ballUnary, _uniformUnary,
    transportUnary, _sourcePointsDistance, _distanceZeroTriangle, _triangleBallFilter,
    _ballUniformNet, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed completionReadUnary transportUnary completionTransportRead
  have namedCert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row distance ∨ hsame row triangle ∨ hsame row ball ∨
              hsame row uniformReflection ∨ hsame row transport ∨
                hsame row completionRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont triangle ball ballRead ∧
              Cont ball uniformReflection completionRead ∧
                Cont completionRead transport namedRead ∧ PkgSig bundle namedRead pkg)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, triangleBallRead, ballUniformRead, completionTransportRead,
          namedPkg⟩
  }
  exact ⟨completionCert, namedCert, namedUnary⟩

end BEDC.Derived.QuasiMetricUp
