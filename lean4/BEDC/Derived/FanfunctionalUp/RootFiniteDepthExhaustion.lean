import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootFiniteDepthExhaustion [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead barRead compactRead toleranceRead modulusRead
      named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg ->
      Cont C F prefixRead ->
        Cont prefixRead B barRead ->
          Cont barRead W compactRead ->
            Cont compactRead K toleranceRead ->
              Cont toleranceRead M modulusRead ->
                Cont modulusRead N named ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle named pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row named /\ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row C \/ hsame row F \/ hsame row B \/ hsame row D \/
                              hsame row W \/ hsame row K \/ hsame row M \/ hsame row N \/
                                hsame row named)
                          (fun row : BHist =>
                            UnaryHistory row /\ Cont C F prefixRead /\
                              Cont prefixRead B barRead /\ Cont barRead W compactRead /\
                                Cont compactRead K toleranceRead /\
                                  Cont toleranceRead M modulusRead /\
                                    Cont modulusRead N named /\ PkgSig bundle P pkg /\
                                      PkgSig bundle named pkg)
                          hsame /\
                        UnaryHistory prefixRead /\ UnaryHistory barRead /\
                          UnaryHistory compactRead /\ UnaryHistory toleranceRead /\
                            UnaryHistory modulusRead /\ UnaryHistory named := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cPrefix prefixBar barCompact compactTolerance toleranceModulus
    modulusNamed provenancePkg namedPkg
  obtain
    ⟨cUnary, fUnary, _epsUnary, bUnary, _dUnary, wUnary, mUnary, _hUnary, kUnary,
      _pUnary, nUnary, _sameHN, _barDepthWitness, _witnessModulusReplay,
      _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary fUnary cPrefix
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed prefixUnary bUnary prefixBar
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed barUnary wUnary barCompact
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed compactUnary kUnary compactTolerance
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed toleranceUnary mUnary toleranceModulus
  have namedUnary : UnaryHistory named :=
    unary_cont_closed modulusUnary nUnary modulusNamed
  have sourceNamed :
      (fun row : BHist => hsame row named /\ UnaryHistory row) named := by
    exact ⟨hsame_refl named, namedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row C \/ hsame row F \/ hsame row B \/ hsame row D \/
              hsame row W \/ hsame row K \/ hsame row M \/ hsame row N \/
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row /\ Cont C F prefixRead /\ Cont prefixRead B barRead /\
              Cont barRead W compactRead /\ Cont compactRead K toleranceRead /\
                Cont toleranceRead M modulusRead /\ Cont modulusRead N named /\
                  PkgSig bundle P pkg /\ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named sourceNamed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cPrefix, prefixBar, barCompact, compactTolerance, toleranceModulus,
          modulusNamed, provenancePkg, namedPkg⟩
  }
  exact
    ⟨cert, prefixUnary, barUnary, compactUnary, toleranceUnary, modulusUnary, namedUnary⟩

end BEDC.Derived.FanfunctionalUp
