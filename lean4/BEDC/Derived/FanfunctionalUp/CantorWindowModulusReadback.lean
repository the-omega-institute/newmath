import BEDC.Derived.FanfunctionalUp.RootUniformModulusReadback

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalCantorWindowModulusReadback [AskSetup] [PackageSetup]
    {C F eps B D W M H K P N prefixRead depthRead witnessRead compactRead
      modulusRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface C F eps B D W M H K P N bundle pkg ->
      Cont C B prefixRead ->
        Cont F D depthRead ->
          Cont prefixRead W witnessRead ->
            Cont K B compactRead ->
              Cont witnessRead M modulusRead ->
                Cont modulusRead N named ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle named pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row named ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row C ∨ hsame row B ∨ hsame row F ∨
                              hsame row D ∨ hsame row W ∨ hsame row K ∨
                                hsame row M ∨ hsame row N ∨ hsame row named)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont C B prefixRead ∧
                              Cont F D depthRead ∧ Cont prefixRead W witnessRead ∧
                                Cont K B compactRead ∧
                                  Cont witnessRead M modulusRead ∧
                                    Cont modulusRead N named ∧
                                      PkgSig bundle P pkg ∧
                                        PkgSig bundle named pkg)
                          hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory depthRead ∧
                        UnaryHistory witnessRead ∧ UnaryHistory compactRead ∧
                          UnaryHistory modulusRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier prefixRoute depthRoute witnessRoute compactRoute modulusRoute namedRoute
    provenancePkg namedPkg
  obtain ⟨cUnary, fUnary, _epsUnary, bUnary, dUnary, wUnary, mUnary, _hUnary, kUnary,
    _pUnary, nUnary, _hKRoute, _bdwRoute, _wmHRoute, _pkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cUnary bUnary prefixRoute
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed fUnary dUnary depthRoute
  have witnessUnary : UnaryHistory witnessRead :=
    unary_cont_closed prefixUnary wUnary witnessRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed kUnary bUnary compactRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary mUnary modulusRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed modulusUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
          ⟨source.right, prefixRoute, depthRoute, witnessRoute, compactRoute,
            modulusRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact
      ⟨prefixUnary, depthUnary, witnessUnary, compactUnary, modulusUnary, namedUnary⟩

end BEDC.Derived.FanfunctionalUp
