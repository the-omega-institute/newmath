import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_diameter_consumer_boundary [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      diameterRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead replay diameterRead ->
            PkgSig bundle diameterRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row diameterRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row S ∨ hsame row radius ∨ hsame row ballRead ∨
                      Cont ballRead replay diameterRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle diameterRead pkg ∧
                      hsame row diameterRead)
                  hsame ∧
                UnaryHistory memberRead ∧ UnaryHistory ballRead ∧ UnaryHistory diameterRead ∧
                  Cont S center memberRead ∧ Cont memberRead radius ballRead ∧
                    Cont ballRead replay diameterRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro carrier subsetCenter memberRadius ballReplayDiameter diameterPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have diameterUnary : UnaryHistory diameterRead :=
    unary_cont_closed ballReadUnary replayUnary ballReplayDiameter
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row diameterRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row radius ∨ hsame row ballRead ∨
              Cont ballRead replay diameterRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle diameterRead pkg ∧
              hsame row diameterRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro diameterRead
        ⟨hsame_refl diameterRead, diameterUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr ballReplayDiameter)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, diameterPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, diameterUnary, subsetCenter, memberRadius,
      ballReplayDiameter⟩

end BEDC.Derived.BoundedSetUp
