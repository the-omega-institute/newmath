import BEDC.Derived.LowerSemicontinuousUp.RealHandoff
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LowerSemicontinuousUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LowerSemicontinuousRootLowerRealProjection [AskSetup] [PackageSetup]
    {X F E W R O H C P N lowerRead comparisonRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lowerSemicontinuousRootEpigraphFields (LowerSemicontinuousUp.mk X F E W R O H C P N) =
        [X, F, W, R, E, O, H, C, P, N] ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory E ->
            UnaryHistory O ->
              Cont W R lowerRead ->
                Cont lowerRead E comparisonRead ->
                  Cont comparisonRead O endpointRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row W ∨ hsame row R ∨ hsame row E ∨
                                hsame row O ∨ hsame row endpointRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont W R lowerRead ∧
                                Cont lowerRead E comparisonRead ∧
                                  Cont comparisonRead O endpointRead ∧
                                    PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro fieldRows wUnary rUnary eUnary oUnary lowerRoute comparisonRoute endpointRoute
    provenancePkg namePkg
  cases fieldRows
  have lowerUnary : UnaryHistory lowerRead :=
    unary_cont_closed wUnary rUnary lowerRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed lowerUnary eUnary comparisonRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed comparisonUnary oUnary endpointRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row O ∨
              hsame row endpointRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R lowerRead ∧ Cont lowerRead E comparisonRead ∧
              Cont comparisonRead O endpointRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpointRead ⟨hsame_refl endpointRead, endpointUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, lowerRoute, comparisonRoute, endpointRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.LowerSemicontinuousUp
