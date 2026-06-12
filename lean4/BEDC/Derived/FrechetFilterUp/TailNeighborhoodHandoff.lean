import BEDC.Derived.FrechetFilterUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FrechetFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FrechetFilterTailNeighborhoodHandoff [AskSetup] [PackageSetup]
    {U T S M B Q R A H C P N tailRead scheduleRead metricRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    frechetFilterFields (FrechetFilterUp.mk U T S M B Q R A H C P N) =
        [U, T, S, M, B, Q, R, A, H, C, P, N] ->
      UnaryHistory U ->
        UnaryHistory T ->
          UnaryHistory S ->
            UnaryHistory M ->
              UnaryHistory P ->
                UnaryHistory N ->
                  Cont U T tailRead ->
                    Cont tailRead S scheduleRead ->
                      Cont scheduleRead M metricRead ->
                        Cont metricRead N named ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle named pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row named ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row U ∨ hsame row T ∨ hsame row S ∨
                                      hsame row M ∨ hsame row tailRead ∨
                                        hsame row scheduleRead ∨ hsame row metricRead ∨
                                          hsame row named)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont U T tailRead ∧
                                      Cont tailRead S scheduleRead ∧
                                        Cont scheduleRead M metricRead ∧
                                          Cont metricRead N named ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle named pkg)
                                  hsame ∧
                                UnaryHistory tailRead ∧ UnaryHistory scheduleRead ∧
                                  UnaryHistory metricRead ∧ UnaryHistory named := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows uUnary tUnary sUnary mUnary pUnary nUnary tailRoute scheduleRoute
    metricRoute namedRoute provenancePkg namedPkg
  cases fieldRows
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed uUnary tUnary tailRoute
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed tailUnary sUnary scheduleRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed scheduleUnary mUnary metricRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed metricUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row U ∨ hsame row T ∨ hsame row S ∨ hsame row M ∨
              hsame row tailRead ∨ hsame row scheduleRead ∨ hsame row metricRead ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont U T tailRead ∧ Cont tailRead S scheduleRead ∧
              Cont scheduleRead M metricRead ∧ Cont metricRead N named ∧
                PkgSig bundle P pkg ∧ PkgSig bundle named pkg)
          hsame := {
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
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, tailRoute, scheduleRoute, metricRoute, namedRoute, provenancePkg,
          namedPkg⟩
  }
  exact ⟨cert, tailUnary, scheduleUnary, metricUnary, namedUnary⟩

end BEDC.Derived.FrechetFilterUp
