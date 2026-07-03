import BEDC.Derived.QuasiMetricUp

namespace BEDC.Derived.QuasiMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuasiMetricCarrier_public_certificate [AskSetup] [PackageSetup]
    {source points distance zero triangle ball filter net uniformReflection transport replay
      provenance localName directedRead triangleRead ballRead cauchyRead uniformRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuasiMetricCarrier source points distance zero triangle ball filter net uniformReflection
        transport replay provenance localName bundle pkg →
      UnaryHistory localName →
        Cont distance points directedRead →
          Cont distance zero triangleRead →
            Cont triangleRead ball ballRead →
              Cont ballRead filter cauchyRead →
                Cont cauchyRead net uniformRead →
                  Cont uniformRead localName publicRead →
                    PkgSig bundle publicRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row source ∨ hsame row points ∨ hsame row distance ∨
                              hsame row zero ∨ hsame row triangle ∨ hsame row ball ∨
                                hsame row filter ∨ hsame row net ∨
                                  hsame row uniformReflection ∨ hsame row transport ∨
                                    hsame row replay ∨ hsame row provenance ∨
                                      hsame row localName ∨ hsame row publicRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont distance points directedRead ∧
                              Cont distance zero triangleRead ∧
                                Cont triangleRead ball ballRead ∧
                                  Cont ballRead filter cauchyRead ∧
                                    Cont cauchyRead net uniformRead ∧
                                      Cont uniformRead localName publicRead ∧
                                        PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory directedRead ∧ UnaryHistory triangleRead ∧
                          UnaryHistory ballRead ∧ UnaryHistory cauchyRead ∧
                            UnaryHistory uniformRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: QuasiMetricCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier localNameUnary directedRoute triangleRoute ballRoute cauchyRoute uniformRoute
    publicRoute publicPkg
  obtain ⟨sourceUnary, pointsUnary, zeroUnary, ballUnary, uniformReflectionUnary,
    _transportUnary, sourcePointsDistance, _distanceZeroTriangle, _triangleBallFilter,
    _ballUniformNet, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have distanceUnary : UnaryHistory distance :=
    unary_cont_closed sourceUnary pointsUnary sourcePointsDistance
  have triangleBaseUnary : UnaryHistory triangle :=
    unary_cont_closed distanceUnary zeroUnary _distanceZeroTriangle
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed distanceUnary pointsUnary directedRoute
  have triangleUnary : UnaryHistory triangleRead :=
    unary_cont_closed distanceUnary zeroUnary triangleRoute
  have filterUnary : UnaryHistory filter :=
    unary_cont_closed triangleBaseUnary ballUnary _triangleBallFilter
  have netUnary : UnaryHistory net :=
    unary_cont_closed ballUnary uniformReflectionUnary _ballUniformNet
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed triangleUnary ballUnary ballRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed ballReadUnary filterUnary cauchyRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed cauchyUnary netUnary uniformRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed uniformUnary localNameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row points ∨ hsame row distance ∨ hsame row zero ∨
              hsame row triangle ∨ hsame row ball ∨ hsame row filter ∨ hsame row net ∨
                hsame row uniformReflection ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont distance points directedRead ∧
              Cont distance zero triangleRead ∧ Cont triangleRead ball ballRead ∧
                Cont ballRead filter cauchyRead ∧ Cont cauchyRead net uniformRead ∧
                  Cont uniformRead localName publicRead ∧ PkgSig bundle publicRead pkg)
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
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, directedRoute, triangleRoute, ballRoute, cauchyRoute, uniformRoute,
          publicRoute, publicPkg⟩
  }
  exact
    ⟨cert, directedUnary, triangleUnary, ballReadUnary, cauchyUnary, uniformUnary,
      publicUnary⟩

theorem QuasiMetricCarrier_triangle_refinement_public_route [AskSetup] [PackageSetup]
    {source points distance zero triangle ball filter net uniformReflection transport replay
      provenance localName firstBall secondBall triangleRead composedBall reflectedRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    QuasiMetricCarrier source points distance zero triangle ball filter net uniformReflection
        transport replay provenance localName bundle pkg →
      UnaryHistory localName →
        Cont distance points firstBall →
          Cont firstBall ball secondBall →
            Cont secondBall triangle triangleRead →
              Cont triangleRead ball composedBall →
                Cont composedBall uniformReflection reflectedRead →
                  Cont reflectedRead localName publicRead →
                    PkgSig bundle composedBall pkg →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row composedBall ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row source ∨ hsame row points ∨ hsame row distance ∨
                                hsame row triangle ∨ hsame row ball ∨ hsame row transport ∨
                                  hsame row replay ∨ hsame row provenance ∨
                                    hsame row localName ∨ hsame row composedBall)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont distance points firstBall ∧
                                Cont firstBall ball secondBall ∧
                                  Cont secondBall triangle triangleRead ∧
                                    Cont triangleRead ball composedBall ∧
                                      PkgSig bundle composedBall pkg)
                            hsame ∧
                          SemanticNameCert
                              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row source ∨ hsame row points ∨ hsame row distance ∨
                                  hsame row triangle ∨ hsame row ball ∨
                                    hsame row uniformReflection ∨ hsame row localName ∨
                                      hsame row composedBall ∨ hsame row publicRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont distance points firstBall ∧
                                  Cont firstBall ball secondBall ∧
                                    Cont secondBall triangle triangleRead ∧
                                      Cont triangleRead ball composedBall ∧
                                        Cont composedBall uniformReflection reflectedRead ∧
                                          Cont reflectedRead localName publicRead ∧
                                            PkgSig bundle publicRead pkg)
                              hsame ∧
                            UnaryHistory reflectedRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier localNameUnary distancePointRead firstBallRead triangleRoute composedRoute
    composedUniformRead reflectedLocalRead composedPkg publicPkg
  have refinement :=
    QuasiMetricCarrier_directed_ball_triangle_refinement carrier distancePointRead firstBallRead
      triangleRoute composedRoute composedPkg
  obtain ⟨composedCert, _firstBallUnary, _secondBallUnary, _triangleReadUnary,
    composedBallUnary⟩ := refinement
  obtain ⟨_sourceUnary, _pointsUnary, _zeroUnary, _ballUnary, uniformReflectionUnary,
    _transportUnary, _sourcePointsDistance, _distanceZeroTriangle, _triangleBallFilter,
    _ballUniformNet, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ := carrier
  have reflectedUnary : UnaryHistory reflectedRead :=
    unary_cont_closed composedBallUnary uniformReflectionUnary composedUniformRead
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed reflectedUnary localNameUnary reflectedLocalRead
  have publicCert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row points ∨ hsame row distance ∨ hsame row triangle ∨
              hsame row ball ∨ hsame row uniformReflection ∨ hsame row localName ∨
                hsame row composedBall ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont distance points firstBall ∧
              Cont firstBall ball secondBall ∧ Cont secondBall triangle triangleRead ∧
                Cont triangleRead ball composedBall ∧
                  Cont composedBall uniformReflection reflectedRead ∧
                    Cont reflectedRead localName publicRead ∧ PkgSig bundle publicRead pkg)
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
        ⟨source.right, distancePointRead, firstBallRead, triangleRoute, composedRoute,
          composedUniformRead, reflectedLocalRead, publicPkg⟩
  }
  exact ⟨composedCert, publicCert, reflectedUnary, publicUnary⟩

end BEDC.Derived.QuasiMetricUp
