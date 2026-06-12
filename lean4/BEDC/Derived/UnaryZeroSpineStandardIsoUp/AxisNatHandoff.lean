import BEDC.Derived.UnaryZeroSpineStandardIsoUp

namespace BEDC.Derived.UnaryZeroSpineStandardIsoUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.AxisZeckendorf.AxisNat
open BEDC.Derived.AxisZeckendorf.Spine

theorem UnaryZeroSpineStandardIsoAxisNatHandoff [AskSetup] [PackageSetup]
    {unary axis length forward backward transport routes provenance cert endpoint axisRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryZeroSpineStandardIsoCarrier unary axis length forward backward transport routes
        provenance cert bundle pkg →
      ZeroSpine axis →
        Cont routes cert endpoint →
          PkgSig bundle endpoint pkg →
            Cont axis endpoint axisRead →
              SemanticNameCert
                (fun row : BHist => hsame row axisRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row unary ∨ hsame row axis ∨ hsame row length ∨ hsame row forward ∨
                    hsame row backward ∨ hsame row routes ∨ hsame row endpoint ∨
                      hsame row axisRead)
                (fun row : BHist =>
                  AxisNatSourceSpec axis ∧ UnaryHistory row ∧ Cont axis endpoint axisRead ∧
                    PkgSig bundle endpoint pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier axisSpine routesCert endpointPkg axisEndpointRead
  obtain ⟨unaryRow, axisRow, lengthRow, _provenanceUnary, certUnary, forwardRoute,
    backwardRoute, routesRoute, _provenanceRoute, _transportRoute, _routesPkg⟩ := carrier
  have forwardUnary : UnaryHistory forward :=
    unary_cont_closed unaryRow lengthRow forwardRoute
  have backwardUnary : UnaryHistory backward :=
    unary_cont_closed axisRow lengthRow backwardRoute
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed forwardUnary backwardUnary routesRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routesUnary certUnary routesCert
  have axisReadUnary : UnaryHistory axisRead :=
    unary_cont_closed axisRow endpointUnary axisEndpointRead
  exact {
    core := {
      carrier_inhabited := Exists.intro axisRead ⟨hsame_refl axisRead, axisReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨axisSpine, source.right, axisEndpointRead, endpointPkg⟩
  }

end BEDC.Derived.UnaryZeroSpineStandardIsoUp
