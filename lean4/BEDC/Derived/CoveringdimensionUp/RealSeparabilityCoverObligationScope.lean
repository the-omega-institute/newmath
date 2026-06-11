import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRealSeparabilityCoverObligationScope [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound lebesgue dyadicWindow regRead realSeal
      densityWindow coverRead scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier compactMetric epsilonNet cover refinement orderBound lebesgue
        dyadicWindow regRead realSeal densityWindow bundle pkg →
      Cont epsilonNet cover densityWindow →
        Cont dyadicWindow regRead realSeal →
          Cont realSeal refinement coverRead →
            Cont coverRead orderBound scopedRead →
              PkgSig bundle scopedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
                        hsame row refinement ∨ hsame row orderBound ∨
                          hsame row dyadicWindow ∨ hsame row regRead ∨
                            hsame row realSeal ∨ hsame row scopedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont epsilonNet cover densityWindow ∧
                        Cont dyadicWindow regRead realSeal ∧
                          Cont realSeal refinement coverRead ∧
                            Cont coverRead orderBound scopedRead ∧
                              PkgSig bundle scopedRead pkg)
                    hsame ∧
                  UnaryHistory realSeal ∧ UnaryHistory coverRead ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier epsilonCoverDensity dyadicRegReal realRefinementCover coverOrderScoped scopedPkg
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary,
    _lebesgueUnary, dyadicUnary, regUnary, _realSealCarrierUnary, _densityUnary,
    _compactEpsilonCover, _coverRefinementOrder, _orderLebesgueReg,
    _dyadicRegRealCarrier, _realSealPkg, _densityPkg⟩ := carrier
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed dyadicUnary regUnary dyadicRegReal
  have coverReadUnary : UnaryHistory coverRead :=
    unary_cont_closed realSealUnary refinementUnary realRefinementCover
  have scopedReadUnary : UnaryHistory scopedRead :=
    unary_cont_closed coverReadUnary orderUnary coverOrderScoped
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row cover ∨
              hsame row refinement ∨ hsame row orderBound ∨ hsame row dyadicWindow ∨
                hsame row regRead ∨ hsame row realSeal ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont epsilonNet cover densityWindow ∧
              Cont dyadicWindow regRead realSeal ∧ Cont realSeal refinement coverRead ∧
                Cont coverRead orderBound scopedRead ∧ PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedReadUnary⟩
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
      cases source.left with
      | refl =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, epsilonCoverDensity, dyadicRegReal, realRefinementCover,
          coverOrderScoped, scopedPkg⟩
  }
  exact ⟨cert, realSealUnary, coverReadUnary, scopedReadUnary⟩

end BEDC.Derived.CoveringdimensionUp
