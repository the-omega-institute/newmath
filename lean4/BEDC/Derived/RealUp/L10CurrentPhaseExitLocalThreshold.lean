import BEDC.Derived.RealUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealL10CurrentPhaseExitLocalThreshold [AskSetup] [PackageSetup]
    {dyadicFace streamFace regSeqFace localReal support route endpoint nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory dyadicFace ->
      UnaryHistory streamFace ->
        UnaryHistory regSeqFace ->
          UnaryHistory localReal ->
            UnaryHistory support ->
              Cont dyadicFace streamFace regSeqFace ->
                Cont regSeqFace localReal route ->
                  Cont route support endpoint ->
                    hsame nameCert endpoint ->
                      PkgSig bundle endpoint pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                            (fun row : BHist => hsame row endpoint)
                            (fun row : BHist => hsame row endpoint ∧ Cont route support endpoint)
                            hsame ∧
                          UnaryHistory route ∧ UnaryHistory endpoint ∧
                            Cont dyadicFace streamFace regSeqFace ∧
                              Cont regSeqFace localReal route ∧ Cont route support endpoint ∧
                                hsame nameCert endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro _dyadicUnary _streamUnary regSeqUnary localRealUnary supportUnary dyadicStreamRoute
    realRoute endpointRoute sameName endpointPkg
  have routeUnary : UnaryHistory route :=
    unary_cont_closed regSeqUnary localRealUnary realRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed routeUnary supportUnary endpointRoute
  have sourceAtEndpoint : hsame endpoint endpoint ∧ UnaryHistory endpoint :=
    ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist => hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ Cont route support endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, endpointRoute⟩
  }
  exact
    ⟨cert, routeUnary, endpointUnary, dyadicStreamRoute, realRoute, endpointRoute, sameName,
      endpointPkg⟩

end BEDC.Derived.RealUp
