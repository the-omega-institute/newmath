import BEDC.Derived.DeGiorgiIterationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DeGiorgiIterationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DeGiorgiIterationNameCertObligations [AskSetup] [PackageSetup]
    {L T S P M B Q R H C G N replayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont H C replayRead ->
      Cont replayRead N namedRead ->
        PkgSig bundle G pkg ->
          PkgSig bundle N pkg ->
            UnaryHistory L ->
              UnaryHistory T ->
                UnaryHistory S ->
                  UnaryHistory P ->
                    UnaryHistory M ->
                      UnaryHistory B ->
                        UnaryHistory Q ->
                          UnaryHistory R ->
                            UnaryHistory H ->
                              UnaryHistory C ->
                                UnaryHistory N ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row L ∨ hsame row T ∨ hsame row S ∨
                                        hsame row P ∨ hsame row M ∨ hsame row B ∨
                                          hsame row Q ∨ hsame row R ∨ hsame row H ∨
                                            hsame row C ∨ hsame row G ∨ hsame row N)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ PkgSig bundle G pkg ∧
                                        PkgSig bundle N pkg)
                                    hsame ∧ UnaryHistory replayRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ProbeBundle Pkg PkgSig
  intro replayRoute namedRoute provenancePkg namePkg LUnary TUnary SUnary PUnary MUnary
    BUnary QUnary RUnary HUnary CUnary NUnary
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed HUnary CUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary NUnary namedRoute
  have sourceAtName : hsame N N ∧ UnaryHistory N :=
    ⟨hsame_refl N, NUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row T ∨ hsame row S ∨ hsame row P ∨ hsame row M ∨
              hsame row B ∨ hsame row Q ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                hsame row G ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle G pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro N sourceAtName
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
      cases source.left
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact hsame_refl N
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, replayUnary, namedUnary⟩

end BEDC.Derived.DeGiorgiIterationUp
