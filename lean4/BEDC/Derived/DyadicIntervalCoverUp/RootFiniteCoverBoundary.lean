import BEDC.Derived.DyadicIntervalCoverUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRootFiniteCoverBoundary [AskSetup] [PackageSetup]
    {L U _M _R V W Q _A _H _C P N endpointRead windowRead coverRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory U →
        UnaryHistory W →
          UnaryHistory Q →
            UnaryHistory V →
              UnaryHistory N →
                Cont L U endpointRead →
                  Cont W Q windowRead →
                    Cont endpointRead V coverRead →
                      Cont coverRead N namedRead →
                        PkgSig bundle P pkg →
                          PkgSig bundle namedRead pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row L ∨ hsame row U ∨ hsame row W ∨
                                    hsame row Q ∨ hsame row V ∨ hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle namedRead pkg)
                                hsame ∧
                              UnaryHistory endpointRead ∧ UnaryHistory windowRead ∧
                                UnaryHistory coverRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro lUnary uUnary wUnary qUnary vUnary nUnary endpointRoute windowRoute coverRoute
    nameRoute provenancePkg namedPkg
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed endpointUnary vUnary coverRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed coverUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row Q ∨
              hsame row V ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, endpointUnary, windowUnary, coverUnary, namedUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
