import BEDC.Derived.BoundedSetUp.BallContainmentRoute

namespace BEDC.Derived.BoundedSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedSetCarrier_located_diameter_readback [AskSetup] [PackageSetup]
    {X S center radius ball transport replay provenance nameRow memberRead ballRead
      diameterRead locatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedSetCarrier X S center radius ball transport replay provenance nameRow bundle pkg ->
      Cont S center memberRead ->
        Cont memberRead radius ballRead ->
          Cont ballRead replay diameterRead ->
            Cont diameterRead transport locatedRead ->
              PkgSig bundle locatedRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row S ∨ hsame row radius ∨ hsame row ballRead ∨
                        hsame row diameterRead ∨ hsame row locatedRead ∨
                          Cont diameterRead transport locatedRead)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∧ PkgSig bundle locatedRead pkg ∧
                        hsame row locatedRead)
                    hsame ∧
                  UnaryHistory memberRead ∧ UnaryHistory ballRead ∧
                    UnaryHistory diameterRead ∧ UnaryHistory locatedRead ∧
                      Cont S center memberRead ∧ Cont memberRead radius ballRead ∧
                        Cont ballRead replay diameterRead ∧
                          Cont diameterRead transport locatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier subsetCenter memberRadius ballReplayDiameter diameterTransportLocated locatedPkg
  obtain ⟨_xUnary, sUnary, centerUnary, radiusUnary, _ballUnary, transportUnary,
    replayUnary, _provenanceUnary, _nameUnary, _carrierMemberRoute, _carrierBallRoute,
    provenancePkg, _namePkg⟩ := carrier
  have memberUnary : UnaryHistory memberRead :=
    unary_cont_closed sUnary centerUnary subsetCenter
  have ballReadUnary : UnaryHistory ballRead :=
    unary_cont_closed memberUnary radiusUnary memberRadius
  have diameterUnary : UnaryHistory diameterRead :=
    unary_cont_closed ballReadUnary replayUnary ballReplayDiameter
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed diameterUnary transportUnary diameterTransportLocated
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row locatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row radius ∨ hsame row ballRead ∨
              hsame row diameterRead ∨ hsame row locatedRead ∨
                Cont diameterRead transport locatedRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle locatedRead pkg ∧
              hsame row locatedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro locatedRead
        ⟨hsame_refl locatedRead, locatedUnary⟩
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
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr diameterTransportLocated)))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, locatedPkg, source.left⟩
  }
  exact
    ⟨cert, memberUnary, ballReadUnary, diameterUnary, locatedUnary, subsetCenter,
      memberRadius, ballReplayDiameter, diameterTransportLocated⟩

end BEDC.Derived.BoundedSetUp
