import BEDC.Derived.MetricClosedBallUp

namespace BEDC.Derived.MetricClosedBallUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricClosedBallMatureBoundaryInventory [AskSetup] [PackageSetup]
    (X d c r rho m H C P N radiusRead boundaryRead replayRead openRoute : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MetricClosedBallCarrier X d c r rho m H C P N bundle pkg ∧
    Cont r rho radiusRead ∧ Cont m rho boundaryRead ∧ Cont boundaryRead C replayRead ∧
      PkgSig bundle radiusRead pkg ∧ PkgSig bundle boundaryRead pkg ∧
        PkgSig bundle replayRead pkg ∧ hsame openRoute (append m rho)

theorem MetricClosedBallMatureBoundaryInventoryCertificate [AskSetup] [PackageSetup]
    {X d c r rho m H C P N radiusRead boundaryRead replayRead strict openRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricClosedBallMatureBoundaryInventory X d c r rho m H C P N radiusRead boundaryRead
        replayRead openRoute bundle pkg ->
      Cont m strict openRoute ->
        SemanticNameCert
            (fun row : BHist =>
              (hsame row radiusRead ∨ hsame row boundaryRead ∨ hsame row replayRead ∨
                  hsame row openRoute) ∧
                UnaryHistory row)
            (fun row : BHist =>
              hsame row X ∨ hsame row d ∨ hsame row c ∨ hsame row r ∨ hsame row rho ∨
                hsame row m ∨ hsame row radiusRead ∨ hsame row boundaryRead ∨
                  hsame row replayRead ∨ hsame row openRoute)
            (fun row : BHist =>
              UnaryHistory row ∧ Cont r rho radiusRead ∧ Cont m rho boundaryRead ∧
                Cont boundaryRead C replayRead ∧ Cont m strict openRoute ∧
                  PkgSig bundle radiusRead pkg ∧ PkgSig bundle boundaryRead pkg ∧
                    PkgSig bundle replayRead pkg)
            hsame ∧
          UnaryHistory radiusRead ∧ UnaryHistory boundaryRead ∧ UnaryHistory replayRead ∧
            hsame openRoute (append m strict) := by
  -- BEDC touchpoint anchor: MetricClosedBallCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro inventory strictRoute
  obtain ⟨carrier, radiusRoute, boundaryRoute, replayRoute, radiusPkg, boundaryPkg,
    replayPkg, _openInventory⟩ := inventory
  obtain ⟨_xUnary, _dUnary, _cUnary, rUnary, rhoUnary, mUnary, _hUnary, cSupportUnary,
    _pUnary, _nUnary, _sourceRoute, _membershipRoute, _nameRoute, _membershipSame,
    _provenancePkg⟩ := carrier
  have radiusUnary : UnaryHistory radiusRead :=
    unary_cont_closed rUnary rhoUnary radiusRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed mUnary rhoUnary boundaryRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed boundaryUnary cSupportUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row radiusRead ∨ hsame row boundaryRead ∨ hsame row replayRead ∨
                hsame row openRoute) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row d ∨ hsame row c ∨ hsame row r ∨ hsame row rho ∨
              hsame row m ∨ hsame row radiusRead ∨ hsame row boundaryRead ∨
                hsame row replayRead ∨ hsame row openRoute)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont r rho radiusRead ∧ Cont m rho boundaryRead ∧
              Cont boundaryRead C replayRead ∧ Cont m strict openRoute ∧
                PkgSig bundle radiusRead pkg ∧ PkgSig bundle boundaryRead pkg ∧
                  PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro radiusRead ⟨Or.inl (hsame_refl radiusRead), radiusUnary⟩
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
          ⟨by
            cases source.left with
            | inl sameRadius =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameRadius)
            | inr rest =>
                cases rest with
                | inl sameBoundary =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary))
                | inr rest =>
                    cases rest with
                    | inl sameReplay =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameReplay)))
                    | inr sameOpen =>
                        exact Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameOpen))),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameRadius =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inl sameRadius))))))
      | inr rest =>
          cases rest with
          | inl sameBoundary =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl sameBoundary)))))))
          | inr rest =>
              cases rest with
              | inl sameReplay =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inl sameReplay))))))))
              | inr sameOpen =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inr sameOpen))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, radiusRoute, boundaryRoute, replayRoute, strictRoute, radiusPkg,
          boundaryPkg, replayPkg⟩
  }
  exact ⟨cert, radiusUnary, boundaryUnary, replayUnary, strictRoute⟩

end BEDC.Derived.MetricClosedBallUp
